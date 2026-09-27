using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;
using Tenet.Kernel;

namespace LeanToDotNet;

/// <summary>
/// Every exported function, run on random inputs twice: by Lean's own compiler and by the IL, which must agree.
///
/// The proved examples test the handful of inputs someone thought to write down. This tests hundreds more, against
/// an implementation that shares no code with lean2il: Lean compiles the same definitions through its own pipeline
/// (LCNF, IR, its interpreter) when it runs <c>lean --run</c>. The inputs are generated from a fixed seed, so a failure
/// reproduces, and the first disagreement stops the build with the input, Lean's answer and the IL's.
/// </summary>
internal sealed class Differential
{
    private readonly Compiler _compiler;
    private readonly string _project;
    private readonly IEnumerable<Name> _modules;
    private readonly Random _rng;
    private readonly int _perFunction;

    public Differential(Compiler compiler, string project, IEnumerable<Name> modules, int perFunction, int seed = 20260927)
    {
        _compiler = compiler;
        _project = project;
        _modules = modules;
        _perFunction = perFunction;
        _rng = new Random(seed);
    }

    public sealed record Outcome(int Calls, int Functions, int Skipped, List<string> SkippedWhy);

    private abstract record V;
    private sealed record NumV(BigInteger X) : V;
    private sealed record BoolV(bool X) : V;
    private sealed record StrV(string X) : V;
    private sealed record EnumV(Layout L, int I) : V;
    private sealed record StructV(Layout L, V[] Fields) : V;
    private sealed record ListV(V[] Items) : V;
    private sealed record OptV(V? X) : V;

    private sealed record Case(Export Export, V[] Args);

    public Outcome Run(string dll)
    {
        var cases = new List<Case>();
        var skipped = new List<string>();
        int functions = 0;
        foreach (Export e in _compiler.Exports.Values)
        {
            string? why = e.Params.FirstOrDefault(p => !p.Repr.IsData) is Param bad ? $"its parameter {bad.LeanName} is not data"
                : e.Params.Select(p => Unsupported(p.Repr)).FirstOrDefault(w => w is not null)
                ?? Unsupported(e.Result);
            if (why is not null)
            {
                skipped.Add($"{e.Name}: {why}");
                continue;
            }
            functions++;
            for (int i = 0; i < _perFunction; i++)
            {
                cases.Add(new Case(e, e.Params.Select(p => Gen(p.Repr, 0)).ToArray()));
            }
        }
        if (cases.Count == 0)
        {
            return new Outcome(0, 0, skipped.Count, skipped);
        }
        string[] lean = RunLean(cases);
        string[] il = RunIl(cases, dll);
        for (int i = 0; i < cases.Count; i++)
        {
            if (lean[i] != il[i])
            {
                Case c = cases[i];
                throw new CompileError($"the IL disagrees with Lean's own compiler on {c.Export.Name} {string.Join(" ", c.Args.Select(LeanLiteral))}: Lean gives {lean[i]}, the IL gives {il[i]}");
            }
        }
        return new Outcome(cases.Count, functions, skipped.Count, skipped);
    }

    private static string? Unsupported(Repr r) => r.Kind switch
    {
        Kind.Nat or Kind.Int or Kind.Bool or Kind.String or Kind.Enum => null,
        Kind.List or Kind.Option => Unsupported(r.Elem!),
        Kind.Struct when r.Layout!.Fields.All(f => f.Field is not null) => r.Layout.Fields.Select(f => Unsupported(f.Repr)).FirstOrDefault(w => w is not null),
        Kind.Struct => $"{r.Layout!.Name} has a proof field, which random inputs cannot supply",
        _ => $"no generator for {r.Kind}",
    };

    // ------------------------------------------------------------------ inputs

    private V Gen(Repr r, int depth) => r.Kind switch
    {
        Kind.Nat => new NumV(GenNat()),
        Kind.Int => new NumV(GenInt()),
        Kind.Bool => new BoolV(_rng.Next(2) == 1),
        Kind.String => new StrV(GenString()),
        Kind.Enum => new EnumV(r.Layout!, _rng.Next(r.Layout!.Cases.Count)),
        Kind.Struct => new StructV(r.Layout!, r.Layout!.Fields.Select(f => Gen(f.Repr, depth + 1)).ToArray()),
        Kind.List => new ListV(Enumerable.Range(0, depth > 1 ? _rng.Next(3) : _rng.Next(9)).Select(_ => Gen(r.Elem!, depth + 1)).ToArray()),
        Kind.Option => new OptV(_rng.Next(4) == 0 ? null : Gen(r.Elem!, depth + 1)),
        _ => throw new InvalidOperationException(),
    };

    /// <summary>
    /// Small numbers mostly, where the interesting cases are (0, 1, boundaries), and a few large ones. Kept below a
    /// few thousand: a Nat may be a recursion count or an exponent, and 10^30 of either is not a test, it is a hang.
    /// </summary>
    private BigInteger GenNat() => _rng.Next(10) switch
    {
        < 5 => _rng.Next(0, 12),
        < 9 => _rng.Next(0, 300),
        _ => _rng.Next(0, 3000),
    };

    private BigInteger GenInt()
    {
        BigInteger magnitude = _rng.Next(10) switch
        {
            < 4 => _rng.Next(0, 20),
            < 8 => _rng.Next(0, 100_000),
            _ => BigInteger.Parse(string.Concat(Enumerable.Range(0, _rng.Next(1, 31)).Select(_ => (char)('0' + _rng.Next(10)))), CultureInfo.InvariantCulture),
        };
        return _rng.Next(2) == 0 ? magnitude : -magnitude;
    }

    private static readonly string[] s_pieces = ["a", "b", "z", "A", "0", "7", " ", "-", "é", "ß", "漢", "😀"];

    private string GenString() => string.Concat(Enumerable.Range(0, _rng.Next(0, 7)).Select(_ => s_pieces[_rng.Next(s_pieces.Length)]));

    // ------------------------------------------------------------------ Lean's side

    private string[] RunLean(List<Case> cases)
    {
        string dir = Path.Combine(_project, ".lake", "lean2il");
        Directory.CreateDirectory(dir);
        string file = Path.Combine(dir, "Lean2IlDiff.lean");
        var sb = new StringBuilder();
        foreach (Name m in _modules.OrderBy(m => m.ToString(), StringComparer.Ordinal))
        {
            sb.Append("import ").AppendLine(Lean(m));
        }
        sb.AppendLine("-- Written by lean2il: each line runs an exported function on a random input through Lean's own");
        sb.AppendLine("-- compiler; lean2il runs the same inputs through the IL and requires the same output.");
        // In chunks: one long do-block exceeds Lean's elaboration depth.
        const int chunk = 40;
        int chunks = (cases.Count + chunk - 1) / chunk;
        for (int k = 0; k < chunks; k++)
        {
            sb.AppendLine($"def lean2ilDiff{k} : IO Unit := do");
            foreach (Case c in cases.Skip(k * chunk).Take(chunk))
            {
                string call = "(" + Lean(c.Export.Name) + string.Concat(c.Args.Select(a => " " + LeanLiteral(a))) + ")";
                sb.AppendLine("  IO.println (" + Ser(call, c.Export.Result) + ")");
            }
        }
        sb.AppendLine("def main : IO Unit := do");
        for (int k = 0; k < chunks; k++)
        {
            sb.AppendLine($"  lean2ilDiff{k}");
        }
        File.WriteAllText(file, sb.ToString());
        var psi = new ProcessStartInfo("lake") { WorkingDirectory = _project, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (string a in (string[])["env", "lean", "--run", file])
        {
            psi.ArgumentList.Add(a);
        }
        using var p = Process.Start(psi) ?? throw new CompileError("could not start lake to run the differential test");
        Task<string> err = p.StandardError.ReadToEndAsync();
        string output = p.StandardOutput.ReadToEnd();
        if (!p.WaitForExit(600_000))
        {
            p.Kill(true);
            throw new CompileError("Lean took more than ten minutes on the differential test");
        }
        if (p.ExitCode != 0)
        {
            throw new CompileError("Lean could not run the differential test:\n" + string.Join('\n', (err.Result + output).Split('\n').Take(15)));
        }
        string[] lines = output.Split('\n').Select(l => l.TrimEnd('\r')).ToArray();
        if (lines.Length < cases.Count)
        {
            throw new CompileError($"the differential test printed {lines.Length} lines for {cases.Count} calls");
        }
        return lines[..cases.Count];
    }

    private static string Lean(Name n) =>
        string.Join('.', n.ToString().Split('.').Select(c => c.All(ch => char.IsLetterOrDigit(ch) || ch is '_' or '\'' or '!' or '?') && !char.IsDigit(c[0]) ? c : "«" + c + "»"));

    private static string LeanLiteral(V v) => v switch
    {
        NumV n when n.X.Sign < 0 => $"(({n.X.ToString(CultureInfo.InvariantCulture)}) : Int)",
        NumV n => $"({n.X.ToString(CultureInfo.InvariantCulture)})",
        BoolV b => b.X ? "true" : "false",
        StrV s => "\"" + s.X.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"",
        EnumV e => Lean(e.L.Cases[e.I].Ctor),
        StructV s => "(" + Lean(s.L.Info.Ctors[0]) + string.Concat(s.Fields.Select(f => " " + LeanLiteral(f))) + ")",
        ListV l => "[" + string.Join(", ", l.Items.Select(LeanLiteral)) + "]",
        OptV o => o.X is null ? "none" : "(some " + LeanLiteral(o.X) + ")",
        _ => throw new InvalidOperationException(),
    };

    /// <summary>Lean source that turns the value of <paramref name="expr"/> into the canonical text both sides print.</summary>
    private static string Ser(string expr, Repr r) => r.Kind switch
    {
        Kind.Nat or Kind.Int or Kind.Bool => $"toString {expr}",
        Kind.String => $"(\"\\\"\" ++ {expr} ++ \"\\\"\")",
        Kind.Enum => "(match " + expr + " with " + string.Join(" ", r.Layout!.Cases.Select((c, i) => $"| {Lean(c.Ctor)} => \"{i}\"")) + ")",
        Kind.Struct => "(\"{\" ++ " + string.Join(" ++ \",\" ++ ", r.Layout!.Fields.Select(f => Ser($"({Lean(f.Name)} {expr})", f.Repr))) + " ++ \"}\")",
        Kind.List => $"(\"[\" ++ \",\".intercalate (({expr}).map (fun e => {Ser("e", r.Elem!)})) ++ \"]\")",
        Kind.Option => $"(match {expr} with | none => \"none\" | some v => \"some \" ++ {Ser("v", r.Elem!)})",
        _ => throw new InvalidOperationException(),
    };

    // ------------------------------------------------------------------ the IL's side

    private string[] RunIl(List<Case> cases, string dll)
    {
        string[] results = new string[cases.Count];
        Exception? failure = null;
        // A big stack, so a deep recursion shows up as a result or a clean error rather than a crashed compiler.
        var t = new Thread(() =>
        {
            var alc = new AssemblyLoadContext("lean2il-differential", isCollectible: true);
            string dir = Path.GetDirectoryName(dll)!;
            alc.Resolving += (ctx, name) => File.Exists(Path.Combine(dir, name.Name + ".dll")) ? ctx.LoadFromAssemblyPath(Path.Combine(dir, name.Name + ".dll")) : null;
            try
            {
                Assembly asm = alc.LoadFromStream(new MemoryStream(File.ReadAllBytes(dll)));
                Assembly rt = alc.LoadFromAssemblyName(asm.GetReferencedAssemblies().First(a => a.Name == "LeanToDotNet.Runtime"));
                Type cls = asm.GetType(_compiler.ClassName, throwOnError: true)!;
                for (int i = 0; i < cases.Count; i++)
                {
                    Case c = cases[i];
                    MethodInfo m = cls.GetMethods(BindingFlags.Public | BindingFlags.Static)
                        .First(x => x.Name == c.Export.ClrName && x.GetParameters().Length == c.Args.Length && !x.GetParameters().Any(p => p.ParameterType == typeof(decimal)) && x.ReturnType != typeof(decimal));
                    object?[] args = c.Args.Select((a, k) => ToClr(a, c.Export.Params[k].Repr, asm, rt)).ToArray();
                    try
                    {
                        results[i] = SerClr(m.Invoke(null, args), c.Export.Result);
                    }
                    catch (TargetInvocationException te)
                    {
                        results[i] = "error: " + te.InnerException?.GetType().Name;
                    }
                }
            }
            catch (Exception e)
            {
                failure = e;
            }
            finally
            {
                alc.Unload();
            }
        }, 512 * 1024 * 1024);
        t.Start();
        t.Join();
        if (failure is not null)
        {
            throw new CompileError("the differential test could not run the IL: " + failure.Message);
        }
        return results;
    }

    private static Type ClrOf(Repr r, Assembly asm, Assembly rt) => r.Kind switch
    {
        Kind.Nat or Kind.Int => typeof(BigInteger),
        Kind.Bool => typeof(bool),
        Kind.String => typeof(string),
        Kind.List => rt.GetType("LeanToDotNet.Runtime.LeanList`1", true)!.MakeGenericType(ClrOf(r.Elem!, asm, rt)),
        Kind.Option => rt.GetType("LeanToDotNet.Runtime.LeanOption`1", true)!.MakeGenericType(ClrOf(r.Elem!, asm, rt)),
        _ => asm.GetType(r.Layout!.ClrName, true)!,
    };

    private static object? ToClr(V v, Repr r, Assembly asm, Assembly rt)
    {
        switch (v)
        {
            case NumV n: return n.X;
            case BoolV b: return b.X;
            case StrV s: return s.X;
            case EnumV e: return Enum.ToObject(asm.GetType(e.L.ClrName, true)!, e.I);
            case StructV s:
                return Activator.CreateInstance(asm.GetType(s.L.ClrName, true)!, s.Fields.Select((f, i) => ToClr(f, s.L.Fields[i].Repr, asm, rt)).ToArray());
            case ListV l:
            {
                Type elem = ClrOf(r.Elem!, asm, rt);
                Array a = Array.CreateInstance(elem, l.Items.Length);
                for (int i = 0; i < l.Items.Length; i++)
                {
                    a.SetValue(ToClr(l.Items[i], r.Elem!, asm, rt), i);
                }
                return ClrOf(r, asm, rt).GetMethod("From")!.Invoke(null, [a]);
            }
            case OptV o:
                return o.X is null
                    ? ClrOf(r, asm, rt).GetProperty("None")!.GetValue(null)
                    : ClrOf(r, asm, rt).GetMethod("Some")!.Invoke(null, [ToClr(o.X, r.Elem!, asm, rt)]);
            default: throw new InvalidOperationException();
        }
    }

    /// <summary>The same canonical text as <see cref="Ser"/>, from a .NET value.</summary>
    private static string SerClr(object? x, Repr r) => r.Kind switch
    {
        Kind.Nat or Kind.Int => ((BigInteger)x!).ToString(CultureInfo.InvariantCulture),
        Kind.Bool => (bool)x! ? "true" : "false",
        Kind.String => "\"" + (string)x! + "\"",
        Kind.Enum => Convert.ToInt32(x, CultureInfo.InvariantCulture).ToString(CultureInfo.InvariantCulture),
        Kind.Struct => "{" + string.Join(",", r.Layout!.Fields.Select(f => SerClr(x!.GetType().GetField(f.ClrName)!.GetValue(x), f.Repr))) + "}",
        Kind.List => "[" + string.Join(",", ((System.Collections.IEnumerable)x!).Cast<object?>().Select(e => SerClr(e, r.Elem!))) + "]",
        Kind.Option => (bool)x!.GetType().GetProperty("IsSome")!.GetValue(x)! ? "some " + SerClr(x.GetType().GetProperty("Value")!.GetValue(x), r.Elem!) : "none",
        _ => throw new InvalidOperationException(),
    };
}
