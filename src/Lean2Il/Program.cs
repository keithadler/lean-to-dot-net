using System.Diagnostics;
using System.Reflection;
using System.Reflection.Emit;
using Tenet.Kernel;
using Tenet.Olean;
using Environment = Tenet.Kernel.Environment;

namespace LeanToDotNet;

internal static class Program
{
    private const string Usage = """
        lean2il: compile Lean 4 definitions to a .NET assembly, after re-checking every proof with Tenet.

        usage: lean2il <lake-project> [options]

          <lake-project>        a Lake project that `lake build` has built
          --out <dir>           where to write the assembly and its docs (default: <lake-project>/.lake/dotnet)
          --assembly <name>     assembly name (default: <Namespace>.Proven)
          --namespace <ns>      Lean namespace the exports live in, and the .NET namespace (default: inferred)
          --class <name>        static class holding the exported functions (default: Proven)
          --trust-imports       re-check only the project's own modules, not Lean's library under them
          --no-check            skip the Tenet re-check (the docs then say the proofs were not re-checked)
          --fuzz <n>            random inputs per exported function, run by Lean and by the IL, which must
                                agree (default 100; 0 skips it)
          --leanviz <url>       LeanViz site for the project; theorem names in the docs link there
          --source <url>        base URL of the Lean sources, for links to each theorem's line
          --version             print the version
          -h, --help            this text

        Mark what to compile with @[export sym] in Lean. Everything else it needs is inlined.
        """;

    public static int Main(string[] args)
    {
        try
        {
            return Run(args);
        }
        catch (CompileError e)
        {
            Console.Error.WriteLine("lean2il: " + e.Message);
            return 2;
        }
        catch (Exception e) when (e is FileNotFoundException or DirectoryNotFoundException or ArgumentException)
        {
            Console.Error.WriteLine("lean2il: " + e.Message);
            if (e is FileNotFoundException && e.Message.Contains("cannot find module", StringComparison.Ordinal))
            {
                Console.Error.WriteLine("  The .olean files may be stale: run `lake build` in the project and try again.");
            }
            return 2;
        }
    }

    private static int Run(string[] args)
    {
        var o = Options.Parse(args);
        if (o is null)
        {
            Console.WriteLine(Usage);
            return 0;
        }
        if (o.Version)
        {
            Console.WriteLine("lean2il " + typeof(Program).Assembly.GetName().Version!.ToString(3));
            return 0;
        }
        var total = Stopwatch.StartNew();
        string project = Path.GetFullPath(o.Project);
        string lib = Path.Combine(project, ".lake", "build", "lib", "lean");
        if (!Directory.Exists(lib))
        {
            throw new DirectoryNotFoundException($"{lib} does not exist; run `lake build` in {project} first");
        }
        var search = new LeanSearchPath();
        search.Add(lib);
        string packages = Path.Combine(project, ".lake", "packages");
        if (Directory.Exists(packages))
        {
            foreach (string pkg in Directory.GetDirectories(packages))
            {
                string pl = Path.Combine(pkg, ".lake", "build", "lib", "lean");
                if (Directory.Exists(pl))
                {
                    search.Add(pl);
                }
            }
        }
        var built = Directory.GetFiles(lib, "*.olean", SearchOption.AllDirectories)
            .Select(p => (Module: search.ModuleNameOf(p), Path: p))
            .OrderBy(m => m.Module.ToString(), StringComparer.Ordinal)
            .ToList();
        // Lake leaves the .olean of a deleted source file behind. Compiling it would resurrect code that no longer
        // exists, so only modules with a source file in the project count.
        var own = built.Where(m => File.Exists(Path.Combine(project, Path.Combine(m.Module.ToString().Split('.')) + ".lean"))).ToList();
        foreach (var orphan in built.Except(own))
        {
            Console.WriteLine($"lean2il: skipping {orphan.Module}: its .olean has no source file (left over from a deleted module)");
        }
        if (own.Count == 0)
        {
            throw new FileNotFoundException($"no .olean files under {lib}; run `lake build` first");
        }

        using var checker = new OleanChecker(search);
        checker.Load(own);
        var ownModules = own.Select(m => m.Module).ToHashSet();
        string lean = checker.Modules[own[0].Module].LeanVersion;
        Console.WriteLine($"lean2il: {own.Count} modules in {project} (Lean {lean})");

        // 1. What to compile: everything marked @[export].
        var exports = new List<Name>();
        var ownConstants = new HashSet<Name>();
        foreach (var (module, _) in own)
        {
            OleanModule om = checker.Modules[module];
            // Lean also attaches @[export] to the helpers it builds for well-founded recursion (f._unary); those are
            // its plumbing, not the author's, and their names start with an underscore.
            exports.AddRange(om.KeysInExtension(Name.Parse("Lean.exportAttr")).Where(n => n.LastString?.StartsWith('_') != true));
            ownConstants.UnionWith(om.ConstantNames);
        }
        if (exports.Count == 0)
        {
            throw new CompileError("nothing is marked @[export]; mark each definition to compile with @[export some_symbol]");
        }
        exports.Sort((a, b) => string.CompareOrdinal(a.ToString(), b.ToString()));
        string ns = o.Namespace ?? CommonNamespace(exports);
        string asmName = o.Assembly ?? (ns.Length > 0 ? ns + ".Proven" : "Lean.Proven");

        var env = new Environment();
        env.SetResolver(checker.Resolve);
        if (checker.Resolve(Quot.QuotName) is QuotInfo)
        {
            env.MarkQuotInitialized();
        }
        string runtimePath = typeof(LeanToDotNet.Runtime.LeanNat).Assembly.Location;
        using var clr = new Clr(runtimePath);
        var pab = new PersistedAssemblyBuilder(new AssemblyName(asmName) { Version = new Version(1, 0, 0, 0) }, clr.CoreAssembly);
        ModuleBuilder mb = pab.DefineDynamicModule(asmName);
        var equations = new Dictionary<Name, Expr>();
        var compiler = new Compiler(checker, env, clr, mb, ns, o.Class, ownConstants, equations);

        // 2. Recursive definitions: ask Lean for their equation lemmas, in a module Tenet will check with the rest.
        var recursive = compiler.RecursiveReachableFrom(exports);
        var checkTargets = own.Select(m => m.Module).ToList();
        Equations.Result eqns = Equations.Generate(project, recursive, ownModules, lean);
        if (eqns.Module is { } eqModule)
        {
            search.Add(Path.GetDirectoryName(eqModule.Path)!);
            checker.Load([eqModule]);
            checkTargets.Add(eqModule.Module);
            Equations.Read(eqns, checker, recursive);
            foreach (var (k, v) in eqns.ByDefinition)
            {
                equations[k] = v;
            }
            Console.WriteLine($"lean2il: {Plural(equations.Count, "recursive definition")}, compiled from equation lemmas Lean proved: {string.Join(", ", equations.Keys.Select(k => k.ToString()).Order())}");
        }
        foreach (Name f in eqns.Failed)
        {
            Console.WriteLine($"lean2il: Lean gave no equation lemma for {f}; anything that needs it will be refused");
        }

        // 3. Re-check with Tenet. Nothing is emitted from a project an independent kernel will not accept.
        Verdict verdict = Verdict.NotChecked;
        if (!o.NoCheck)
        {
            var sw = Stopwatch.StartNew();
            OleanCheckResult r = checker.Check(checkTargets, new OleanCheckOptions { CheckImports = !o.TrustImports });
            verdict = new Verdict(true, !o.TrustImports, r.Checked, r.ModulesChecked, r.Failures.Count, sw.Elapsed, lean);
            Console.WriteLine($"tenet: {r.Checked:N0} declarations in {r.ModulesChecked:N0} modules re-checked{(o.TrustImports ? " (project only)" : " (with everything they import)")}, {r.Failures.Count} failed, {sw.Elapsed.TotalSeconds:F1}s");
            if (!r.Success)
            {
                foreach (OleanCheckFailure f in r.Failures.Take(20))
                {
                    Console.Error.WriteLine($"  REJECTED {f.Module}: {f.Name}: {f.Message}");
                }
                throw new CompileError("Tenet rejected the project; nothing was emitted");
            }
        }

        // 4. Compile: the exports, then every recursive helper they turned out to need.
        var declared = exports.Select(compiler.Declare).ToList();
        foreach (Export e in declared)
        {
            compiler.CompileBody(e);
            compiler.CompileDecimalOverload(e);
        }
        compiler.CompilePending();
        var docs = new Docs(checker, env, compiler, ownModules, ownConstants, verdict, o, asmName);
        docs.Collect();
        compiler.Finish(docs.VerdictLine(), lean, docs.TheoremNames);

        string outDir = Path.GetFullPath(o.Out ?? Path.Combine(project, ".lake", "dotnet"));
        Directory.CreateDirectory(outDir);
        string dll = Path.Combine(outDir, asmName + ".dll");
        pab.Save(dll);
        File.Copy(runtimePath, Path.Combine(outDir, Path.GetFileName(runtimePath)), overwrite: true);
        Console.WriteLine($"emitted {dll}: {Plural(declared.Count, "function")} in {compiler.ClassName}, for {clr.TargetFramework}");
        foreach (Export e in declared)
        {
            Console.WriteLine($"  {compiler.ClassName}.{e.ClrName}  <-  {e.Name}{(e.HasDecimalForm ? "  (with a decimal overload)" : "")}");
        }

        // 5. Documentation from the Lean, and a replay of every proved example against the IL.
        int replayed = docs.Replay(dll);
        if (o.Fuzz > 0)
        {
            var sw2 = Stopwatch.StartNew();
            Differential.Outcome d = new Differential(compiler, project, ownModules, o.Fuzz).Run(dll);
            docs.DifferentialLine = d.Calls == 0 ? null
                : $"{d.Calls:N0} random calls to {Plural(d.Functions, "function")}, each run by Lean's own compiler and by the IL, gave the same answer every time.";
            Console.WriteLine($"differential: {d.Calls:N0} random calls to {Plural(d.Functions, "function")}, Lean's own compiler and the IL agree on every one ({sw2.Elapsed.TotalSeconds:F1}s)");
            foreach (string why in d.SkippedWhy)
            {
                Console.WriteLine($"differential: skipped {why}");
            }
        }
        docs.Write(outDir);
        Console.WriteLine($"docs: {asmName}.xml (IntelliSense), {asmName}.md (how to call it), {asmName}.proof.json; {Plural(docs.TheoremCount, "theorem")}, {Plural(replayed, "proved example")} replayed against the IL{(replayed > 0 ? ", all equal" : "")}");
        Console.WriteLine($"done in {total.Elapsed.TotalSeconds:F1}s");
        return 0;
    }

    private static string Plural(int n, string word) => $"{n:N0} {word}{(n == 1 ? "" : "s")}";

    /// <summary>The longest namespace every export shares, e.g. <c>Finance</c> for <c>Finance.round</c> and <c>Finance.roundCents</c>.</summary>
    private static string CommonNamespace(List<Name> names)
    {
        string[][] parts = names.Select(n => n.ToString().Split('.')[..^1]).ToArray();
        int k = 0;
        while (parts.All(p => p.Length > k && p[k] == parts[0][k]))
        {
            k++;
        }
        return string.Join('.', parts[0].Take(k));
    }
}

/// <summary>What Tenet said, to be repeated in every document produced.</summary>
internal sealed record Verdict(bool Checked, bool WithImports, int Declarations, int Modules, int Failed, TimeSpan Elapsed, string Lean)
{
    public static readonly Verdict NotChecked = new(false, false, 0, 0, 0, TimeSpan.Zero, "");
}

internal sealed class Options
{
    public string Project { get; private set; } = "";
    public string? Out { get; private set; }
    public string? Assembly { get; private set; }
    public string? Namespace { get; private set; }
    public string Class { get; private set; } = "Proven";
    public bool TrustImports { get; private set; }
    public bool NoCheck { get; private set; }
    public bool Version { get; private set; }
    public string? LeanViz { get; private set; }
    public string? Source { get; private set; }
    public int Fuzz { get; private set; } = 100;

    public static Options? Parse(string[] args)
    {
        var o = new Options();
        for (int i = 0; i < args.Length; i++)
        {
            string a = args[i];
            string Next() => i + 1 < args.Length ? args[++i] : throw new ArgumentException($"{a} needs a value");
            switch (a)
            {
                case "-h" or "--help": return null;
                case "--version": o.Version = true; break;
                case "--out": o.Out = Next(); break;
                case "--assembly": o.Assembly = Next(); break;
                case "--namespace": o.Namespace = Next(); break;
                case "--class": o.Class = Next(); break;
                case "--trust-imports": o.TrustImports = true; break;
                case "--no-check": o.NoCheck = true; break;
                case "--leanviz": o.LeanViz = Next(); break;
                case "--source": o.Source = Next(); break;
                case "--fuzz": o.Fuzz = int.TryParse(Next(), out int f) && f >= 0 ? f : throw new ArgumentException("--fuzz needs a number, 0 or more"); break;
                default:
                    if (a.StartsWith('-'))
                    {
                        throw new ArgumentException($"unknown option {a}; see lean2il --help");
                    }
                    o.Project = a;
                    break;
            }
        }
        if (o.Project.Length == 0 && !o.Version)
        {
            return null;
        }
        return o;
    }
}
