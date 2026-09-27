using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using Tenet.Kernel;
using Tenet.Olean;

namespace LeanToDotNet;

/// <summary>
/// The equation lemmas of the recursive definitions an export reaches, from Lean.
///
/// Lean proves <c>f.eq_def : ∀ xs, f xs = rhs</c> for every recursive <c>f</c>, but it only generates the lemma
/// when something asks for it, so most are not in the <c>.olean</c> files. This writes a small module that asks,
/// <c>.lake/lean2il/Lean2IlEqns.lean</c>, one theorem per definition restating its <c>eq_def</c>, and has Lean compile
/// it. The module is then loaded like the project's own, and Tenet re-checks it with them, so every equation the
/// compiler relies on has been proved by Lean and accepted by Tenet.
/// </summary>
internal static partial class Equations
{
    public const string ModuleName = "Lean2IlEqns";

    public sealed record Result(Dictionary<Name, Expr> ByDefinition, (Name Module, string Path)? Module, List<Name> Failed);

    /// <summary>Ask Lean for the equations; returns the module to load and check, or none when nothing is recursive.</summary>
    public static Result Generate(string project, IReadOnlyCollection<Name> recursive, IEnumerable<Name> projectModules, string leanVersion)
    {
        var failed = new List<Name>();
        if (recursive.Count == 0)
        {
            return new Result(new(), null, failed);
        }
        string dir = Path.Combine(project, ".lake", "lean2il");
        string build = Path.Combine(dir, "build");
        Directory.CreateDirectory(build);
        string source = Path.Combine(dir, ModuleName + ".lean");
        string olean = Path.Combine(build, ModuleName + ".olean");
        var names = recursive.OrderBy(n => n.ToString(), StringComparer.Ordinal).ToList();

        for (int attempt = 0; attempt < 3 && names.Count > 0; attempt++)
        {
            File.WriteAllText(source, Source(names, projectModules));
            var (code, output) = Run(project, "lake", ["env", "lean", "-o", olean, source]);
            if (code == 0)
            {
                return new Result(new(), (Name.Parse(ModuleName), olean), failed);
            }
            // Drop the definitions Lean could not state an equation for, and try again without them.
            var bad = new HashSet<int>();
            foreach (Match m in ErrorLine().Matches(output))
            {
                int line = int.Parse(m.Groups[1].Value);
                int index = line - FirstTheoremLine(projectModules);
                if (index >= 0 && index < names.Count)
                {
                    bad.Add(index);
                }
            }
            if (bad.Count == 0)
            {
                throw new CompileError("Lean could not generate the equation lemmas lean2il needs:\n" + string.Join('\n', output.Split('\n').Take(20)));
            }
            failed.AddRange(bad.Select(i => names[i]));
            names = names.Where((_, i) => !bad.Contains(i)).ToList();
        }
        if (names.Count == 0)
        {
            return new Result(new(), null, failed);
        }
        throw new CompileError("Lean could not generate the equation lemmas lean2il needs");
    }

    /// <summary>Read each restated equation back from the checked module: definition name to <c>∀ xs, f xs = rhs</c>.</summary>
    public static void Read(Result r, OleanChecker checker, IReadOnlyCollection<Name> recursive)
    {
        if (r.Module is null)
        {
            return;
        }
        OleanModule m = checker.Modules[r.Module.Value.Module];
        foreach (Name n in m.ConstantNames)
        {
            if (n.Prefix.ToString() != ModuleName || checker.Resolve(n) is not TheoremInfo t)
            {
                continue;
            }
            Expr body = t.Type;
            while (body is PiExpr p)
            {
                body = p.Body;
            }
            if (body.IsAppOfArity(Name.Parse("Eq"), 3))
            {
                body.GetAppArgs(out Expr[] eq);
                if (eq[1].GetAppFn() is ConstExpr c && recursive.Contains(c.Name))
                {
                    r.ByDefinition[c.Name] = t.Type;
                }
            }
        }
    }

    private static string Source(List<Name> names, IEnumerable<Name> projectModules)
    {
        var sb = new StringBuilder();
        foreach (Name m in projectModules.OrderBy(m => m.ToString(), StringComparer.Ordinal))
        {
            sb.Append("import ").AppendLine(Ident(m));
        }
        sb.AppendLine("-- Written by lean2il: each theorem restates the equation lemma of a recursive definition an");
        sb.AppendLine("-- exported function uses. lean2il compiles the right-hand sides; Tenet re-checks these proofs.");
        sb.AppendLine("namespace " + ModuleName);
        for (int i = 0; i < names.Count; i++)
        {
            string eq = "@" + Ident(Name.Parse(names[i] + ".eq_def"));
            sb.AppendLine($"theorem e{i} : type_of% {eq} := {eq}");
        }
        sb.AppendLine("end " + ModuleName);
        return sb.ToString();
    }

    private static int FirstTheoremLine(IEnumerable<Name> projectModules) => projectModules.Count() + 4;

    /// <summary>A Lean name as source: each component bare when it is an identifier, in «» when it is not.</summary>
    private static string Ident(Name n) =>
        string.Join('.', n.ToString().Split('.').Select(c => SimpleIdent().IsMatch(c) ? c : "«" + c + "»"));

    [GeneratedRegex(@"^[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_'!?Ͱ-Ͽ]*$")]
    private static partial Regex SimpleIdent();

    [GeneratedRegex(@"Lean2IlEqns\.lean:(\d+):\d+: error")]
    private static partial Regex ErrorLine();

    private static (int Code, string Output) Run(string cwd, string program, string[] args)
    {
        var psi = new ProcessStartInfo(program) { WorkingDirectory = cwd, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (string a in args)
        {
            psi.ArgumentList.Add(a);
        }
        using var p = Process.Start(psi) ?? throw new CompileError($"could not start {program}");
        Task<string> err = p.StandardError.ReadToEndAsync();
        string output = p.StandardOutput.ReadToEnd() + err.Result;
        p.WaitForExit();
        return (p.ExitCode, output);
    }
}
