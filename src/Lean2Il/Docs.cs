using System.Numerics;
using System.Reflection;
using System.Runtime.Loader;
using System.Security;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using LeanToDotNet.Vendor;
using Tenet.Kernel;
using ConstructorInfo = Tenet.Kernel.ConstructorInfo;
using Tenet.Olean;
using Environment = Tenet.Kernel.Environment;

namespace LeanToDotNet;

/// <summary>
/// The documentation of a compiled assembly, written from the Lean it came from and nothing else.
///
/// Lean already keeps everything a caller needs: the docstring of each definition, the theorems stated about it,
/// and, in any theorem of the form <c>f a b = c</c> with literal arguments, a worked example that the kernel has
/// checked. So the summary of each .NET method is its Lean docstring, its remarks list the documented theorems
/// that mention it with their statements and the axioms under them, and its examples are the proved equations,
/// rewritten as C# calls. Before any example is written down it is run against the emitted IL, through both
/// overloads, and must give the proved answer, so a documented call is one the assembly is known to get right.
///
/// A theorem is documented when it has a docstring. That is the whole rule: a helper lemma stays out of the .NET
/// docs by not having one.
/// </summary>
internal sealed partial class Docs
{
    private readonly OleanChecker _loader;
    private readonly Environment _env;
    private readonly Compiler _compiler;
    private readonly HashSet<Name> _modules;
    private readonly HashSet<Name> _own;
    private readonly Verdict _verdict;
    private readonly Options _o;
    private readonly string _asm;
    private readonly Pretty _pretty;
    private readonly Dictionary<Name, Name[]> _refs = new();

    private readonly List<Theorem> _theorems = new();
    private readonly List<Example> _examples = new();
    private readonly Dictionary<Name, string> _moduleDocs = new();

    public int TheoremCount => _theorems.Count;

    /// <summary>What the differential test found, when it ran.</summary>
    public string? DifferentialLine { get; set; }

    public IReadOnlyList<string> TheoremNames => _theorems.Select(t => t.Name.ToString()).ToList();

    public Docs(OleanChecker loader, Environment env, Compiler compiler, HashSet<Name> modules, HashSet<Name> own, Verdict verdict, Options o, string asm)
    {
        _loader = loader;
        _env = env;
        _compiler = compiler;
        _modules = modules;
        _own = own;
        _verdict = verdict;
        _o = o;
        _asm = asm;
        _pretty = new Pretty(loader.Resolve) { MaxLength = 600 };
    }

    private sealed record Theorem(Name Name, Name Module, string Statement, string Doc, string[] Axioms, SourceRange? Range, Name[] Mentions);

    /// <summary>A proved <c>f args = result</c> with literal arguments: a documented, tested call.</summary>
    private sealed record Example(Name Theorem, Export Export, Val[] Args, Val Result);

    private abstract record Val;
    private sealed record Num(BigInteger V) : Val;
    private sealed record BoolV(bool V) : Val;
    private sealed record Fix(FixedWidth F, BigInteger V) : Val;
    private sealed record EnumV(Layout L, int Index) : Val;
    private sealed record StructV(Layout L, Val[] Fields) : Val;
    private sealed record StrV(string V) : Val;
    private sealed record ListV(Val[] Items) : Val;
    private sealed record ArrV(Val[] Items) : Val;
    private sealed record OptV(Val? V) : Val;
    private sealed record UnionV(Layout L, int Variant, Val[] Fields) : Val;

    // ------------------------------------------------------------------ collecting

    public void Collect()
    {
        foreach (Name m in _modules.OrderBy(m => m.ToString(), StringComparer.Ordinal))
        {
            OleanModule om = _loader.Modules[m];
            string? src = SourceFile(m);
            if (src is not null && ModuleDocRegex().Match(File.ReadAllText(src)) is { Success: true } md)
            {
                _moduleDocs[m] = md.Groups[1].Value.Trim();
            }
            foreach (Name n in om.ConstantNames)
            {
                if (_loader.Resolve(n) is not TheoremInfo t || om.DocStringOf(n) is not string doc)
                {
                    continue;
                }
                var mentions = new HashSet<Name>();
                ExprOps.ForEach(t.Type, (e, _) =>
                {
                    if (e is ConstExpr c && _compiler.Exports.ContainsKey(c.Name))
                    {
                        mentions.Add(c.Name);
                    }
                    return true;
                });
                var th = new Theorem(n, m, _pretty.Statement(t), doc.Trim(), AxiomsOf(n), om.SourceRangeOf(n), mentions.OrderBy(x => x.ToString()).ToArray());
                _theorems.Add(th);
                if (AsExample(t) is Example ex)
                {
                    _examples.Add(ex);
                }
            }
        }
    }

    private string? SourceFile(Name module)
    {
        string p = Path.Combine(Path.GetFullPath(_o.Project), Path.Combine(module.ToString().Split('.')) + ".lean");
        return File.Exists(p) ? p : null;
    }

    [GeneratedRegex(@"/-!\s*(.*?)-/", RegexOptions.Singleline)]
    private static partial Regex ModuleDocRegex();

    /// <summary>Every axiom <paramref name="n"/> rests on, through everything it refers to.</summary>
    private string[] AxiomsOf(Name n)
    {
        var seen = new HashSet<Name>();
        var axioms = new SortedSet<string>(StringComparer.Ordinal);
        var stack = new Stack<Name>();
        stack.Push(n);
        while (stack.Count > 0)
        {
            Name c = stack.Pop();
            if (!seen.Add(c))
            {
                continue;
            }
            ConstantInfo? info = _loader.Resolve(c);
            if (info is AxiomInfo)
            {
                axioms.Add(c.ToString());
            }
            foreach (Name r in RefsOf(c, info))
            {
                stack.Push(r);
            }
        }
        return axioms.ToArray();
    }

    private Name[] RefsOf(Name n, ConstantInfo? info)
    {
        if (_refs.TryGetValue(n, out Name[]? known))
        {
            return known;
        }
        var set = new HashSet<Name>();
        void Scan(Expr? e)
        {
            if (e is null)
            {
                return;
            }
            ExprOps.ForEach(e, (x, _) =>
            {
                if (x is ConstExpr c)
                {
                    set.Add(c.Name);
                }
                return true;
            });
        }
        if (info is not null)
        {
            Scan(info.Type);
            Scan(info.Value);
            switch (info)
            {
                case InductiveInfo ind: set.UnionWith(ind.Ctors); break;
                case ConstructorInfo ci: set.Add(ci.Induct); break;
                case RecursorInfo ri: foreach (RecursorRule rule in ri.Rules) { Scan(rule.Rhs); } break;
            }
        }
        return _refs[n] = set.ToArray();
    }

    /// <summary>The theorem as a worked example, when it says <c>export arg… = value</c> with literal arguments.</summary>
    private Example? AsExample(TheoremInfo t)
    {
        if (!t.Type.IsAppOfArity(Name.Parse("Eq"), 3))
        {
            return null;
        }
        t.Type.GetAppArgs(out Expr[] eq);
        Expr head = eq[1].GetAppArgs(out Expr[] args);
        if (head is not ConstExpr c || !_compiler.Exports.TryGetValue(c.Name, out Export? ex) || args.Length != ex.Params.Count)
        {
            return null;
        }
        var reducer = _compiler.NewReducer();
        var vals = new List<Val>();
        for (int i = 0; i < args.Length; i++)
        {
            if (!ex.Params[i].Repr.IsData)
            {
                continue;
            }
            if (Eval(args[i], reducer) is not Val v)
            {
                return null;
            }
            vals.Add(v);
        }
        return Eval(eq[2], reducer) is Val r ? new Example(t.Name, ex, vals.ToArray(), r) : null;
    }

    /// <summary>A closed term as a value, when it is literals and constructors once instances are unfolded.</summary>
    private Val? Eval(Expr e, Compiler.Body reducer)
    {
        e = reducer.Reduce(e);
        if (e is LitExpr { Value: NatLiteral n })
        {
            return new Num(n.Value);
        }
        if (e is LitExpr { Value: StrLiteral str })
        {
            return new StrV(str.Value);
        }
        Expr head = e.GetAppArgs(out Expr[] args);
        if (head is not ConstExpr c)
        {
            return null;
        }
        BigInteger? Arg(int i) => i < args.Length && Eval(args[i], reducer) is Num x ? x.V : null;
        string cn = c.Name.ToString();
        if (cn.LastIndexOf('.') is int dot and > 0 && FixedWidth.OfLean(cn[..dot]) is FixedWidth fw)
        {
            Val? Fx(int i) => i < args.Length ? Eval(args[i], reducer) : null;
            switch (cn[(dot + 1)..])
            {
                case "ofNat" or "ofInt": return Arg(0) is BigInteger k ? new Fix(fw, fw.Wrap(k)) : null;
                case "neg": return Fx(0) is Fix x ? new Fix(fw, fw.Wrap(-x.V)) : null;
            }
            return null;
        }
        switch (cn)
        {
            case "Int.ofNat": return Arg(0) is BigInteger a ? new Num(a) : null;
            case "Int.negSucc": return Arg(0) is BigInteger b ? new Num(-(b + 1)) : null;
            case "Int.neg": return Arg(0) is BigInteger d ? new Num(-d) : null;
            case "Nat.succ": return Arg(0) is BigInteger s ? new Num(s + 1) : null;
            case "Nat.zero": return new Num(0);
            case "Bool.true": return new BoolV(true);
            case "Bool.false": return new BoolV(false);
            case "List.nil": return new ListV([]);
            case "List.cons":
                return args.Length == 3 && Eval(args[1], reducer) is Val h && Eval(args[2], reducer) is ListV t ? new ListV([h, .. t.Items]) : null;
            case "Array.mk": return args.Length == 2 && Eval(args[1], reducer) is ListV items ? new ArrV(items.Items) : null;
            case "Option.none": return new OptV(null);
            case "Option.some": return args.Length == 2 && Eval(args[1], reducer) is Val v1 ? new OptV(v1) : null;
        }
        if (_env.Find(c.Name) is not ConstructorInfo ci)
        {
            return null;
        }
        Layout? l;
        try
        {
            l = _compiler.ReprOf(reducer.Tc.Infer(e), reducer.Tc).Layout;
        }
        catch (Exception)
        {
            return null;
        }
        if (l is null)
        {
            return null;
        }
        if (l.Kind == Kind.Enum)
        {
            return new EnumV(l, ci.Cidx);
        }
        List<FieldSlot> slots = l.Kind == Kind.Union ? l.Variants[ci.Cidx].Fields : l.Fields;
        var fields = new List<Val>();
        for (int i = 0; i < ci.NumFields; i++)
        {
            if (slots[i].Field is null)
            {
                continue;
            }
            if (Eval(args[ci.NumParams + i], reducer) is not Val v)
            {
                return null;
            }
            fields.Add(v);
        }
        return l.Kind == Kind.Union ? new UnionV(l, ci.Cidx, fields.ToArray()) : new StructV(l, fields.ToArray());
    }

    // ------------------------------------------------------------------ replaying the examples against the IL

    /// <summary>
    /// Load the assembly just written and run every example through the exact method and, where there is one, the
    /// decimal overload. Any disagreement with the proved value is fatal: the docs would be promising a result the
    /// assembly does not give.
    /// </summary>
    public int Replay(string dll)
    {
        var alc = new AssemblyLoadContext("lean2il-replay", isCollectible: true);
        string dir = Path.GetDirectoryName(dll)!;
        alc.Resolving += (ctx, name) =>
        {
            string p = Path.Combine(dir, name.Name + ".dll");
            return File.Exists(p) ? ctx.LoadFromAssemblyPath(p) : null;
        };
        try
        {
            Assembly asm = alc.LoadFromStream(new MemoryStream(File.ReadAllBytes(dll)));
            Type cls = asm.GetType(_compiler.ClassName, throwOnError: true)!;
            int n = 0;
            foreach (Example ex in _examples)
            {
                MethodInfo raw = FindMethod(cls, ex.Export, decimalForm: false);
                Param[] ps = ex.Export.Params.Where(p => p.Repr.IsData).ToArray();
                object? got = raw.Invoke(null, ex.Args.Select((a, i) => ToClr(a, ps[i].Repr, asm, decimalForm: false)).ToArray());
                if (!Same(got, ex.Result, decimalForm: false))
                {
                    throw new CompileError($"the IL disagrees with {ex.Theorem}: {ex.Export.ClrName} gave {Show(got)}, the theorem says {CSharp(ex.Result, false)}");
                }
                if (ex.Export.HasDecimalForm)
                {
                    MethodInfo dec = FindMethod(cls, ex.Export, decimalForm: true);
                    object? got2 = dec.Invoke(null, ex.Args.Select((a, i) => ToClr(a, ps[i].Repr, asm, decimalForm: true)).ToArray());
                    if (!Same(got2, ex.Result, decimalForm: true))
                    {
                        throw new CompileError($"the decimal overload disagrees with {ex.Theorem}: gave {Show(got2)}, the theorem says {CSharp(ex.Result, true)}");
                    }
                }
                n++;
            }
            return n;
        }
        finally
        {
            alc.Unload();
        }
    }

    private static MethodInfo FindMethod(Type cls, Export ex, bool decimalForm) =>
        cls.GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Where(m => m.Name == ex.ClrName)
            .First(m => m.GetParameters().Any(p => p.ParameterType == typeof(decimal)) || m.ReturnType == typeof(decimal) ? decimalForm : !decimalForm);

    /// <summary>The run-time type of a representation, in the replay's load context.</summary>
    private static Type RuntimeType(Repr r, Assembly asm) => r.Kind switch
    {
        Kind.Nat or Kind.Int => typeof(BigInteger),
        Kind.Bool => typeof(bool),
        Kind.String => typeof(string),
        Kind.Fixed => Type.GetType(FixedWidth.OfClr(r.ClrType).Clr, true)!,
        Kind.List => RuntimeAssembly(asm).GetType("LeanToDotNet.Runtime.LeanList`1", true)!.MakeGenericType(RuntimeType(r.Elem!, asm)),
        Kind.Option => RuntimeAssembly(asm).GetType("LeanToDotNet.Runtime.LeanOption`1", true)!.MakeGenericType(RuntimeType(r.Elem!, asm)),
        Kind.Array => RuntimeAssembly(asm).GetType("LeanToDotNet.Runtime.LeanArray`1", true)!.MakeGenericType(RuntimeType(r.Elem!, asm)),
        _ => asm.GetType(r.Layout!.ClrName, true)!,
    };

    private static Assembly RuntimeAssembly(Assembly asm) =>
        AssemblyLoadContext.GetLoadContext(asm)!.LoadFromAssemblyName(asm.GetReferencedAssemblies().First(a => a.Name == "LeanToDotNet.Runtime"));

    private static object ToClr(Val v, Repr r, Assembly asm, bool decimalForm) => v switch
    {
        Num n => decimalForm && r.Kind == Kind.Nat ? (object)(int)n.V : n.V,
        StrV str => str.V,
        Fix f => f.F.Box(f.V),
        ListV l => ListOf(l, r, asm),
        ArrV a => ListOf(new ListV(a.Items), r, asm),
        OptV o => o.V is null
            ? RuntimeType(r, asm).GetProperty("None")!.GetValue(null)!
            : RuntimeType(r, asm).GetMethod("Some")!.Invoke(null, [ToClr(o.V, r.Elem!, asm, false)])!,
        BoolV b => b.V,
        EnumV e => Enum.ToObject(asm.GetType(e.L.ClrName, true)!, e.Index),
        StructV s when decimalForm && s.L.DecimalShaped => Runtime.DecimalBridge.FromParts(((Num)s.Fields[0]).V, ((Num)s.Fields[1]).V),
        StructV s => Activator.CreateInstance(asm.GetType(s.L.ClrName, true)!, s.Fields.Select((f, i) => ToClr(f, s.L.RuntimeFields[i].Repr, asm, false)).ToArray())!,
        UnionV u => Activator.CreateInstance(asm.GetType(u.L.ClrName + "+" + u.L.Variants[u.Variant].ClrName, true)!,
            u.Fields.Select((f, i) => ToClr(f, u.L.Variants[u.Variant].RuntimeFields[i].Repr, asm, false)).ToArray())!,
        _ => throw new InvalidOperationException(),
    };

    private static object ListOf(ListV l, Repr r, Assembly asm)
    {
        Type elem = RuntimeType(r.Elem!, asm);
        Array items = Array.CreateInstance(elem, l.Items.Length);
        for (int i = 0; i < l.Items.Length; i++)
        {
            items.SetValue(ToClr(l.Items[i], r.Elem!, asm, false), i);
        }
        return RuntimeType(r, asm).GetMethod("From")!.Invoke(null, [items])!;
    }

    private static bool Same(object? got, Val want, bool decimalForm) => (got, want) switch
    {
        (string g, StrV w) => g == w.V,
        (System.Collections.IEnumerable g, ListV w) when got is not string => g.Cast<object?>().ToArray() is object?[] a
            && a.Length == w.Items.Length && a.Select((x, i) => Same(x, w.Items[i], false)).All(x => x),
        (System.Collections.IEnumerable, ArrV w) when got is not string => Same(got, new ListV(w.Items), false),
        (not null, OptV w) => (bool)got.GetType().GetProperty("IsSome")!.GetValue(got)! == (w.V is not null)
            && (w.V is null || Same(got.GetType().GetProperty("Value")!.GetValue(got), w.V, false)),
        (BigInteger g, Num w) => g == w.V,
        (bool g, BoolV w) => g == w.V,
        (not null, Fix w) => got.GetType().FullName == w.F.Clr && Convert.ToString(got, System.Globalization.CultureInfo.InvariantCulture) == w.V.ToString(),
        (Enum g, EnumV w) => Convert.ToInt32(g) == w.Index,
        (decimal g, StructV w) => Runtime.DecimalBridge.Mantissa(g) == ((Num)w.Fields[0]).V && g.Scale == ((Num)w.Fields[1]).V,
        (not null, UnionV w) => (int)got.GetType().GetField("Tag")!.GetValue(got)! == w.Variant
            && w.L.Variants[w.Variant].RuntimeFields.Select((f, i) => Same(got.GetType().GetField(f.ClrName)!.GetValue(got), w.Fields[i], false)).All(x => x),
        (not null, StructV w) => w.L.RuntimeFields.Select((f, i) => Same(got.GetType().GetField(f.ClrName)!.GetValue(got), w.Fields[i], false)).All(x => x),
        _ => false,
    };

    private static string Show(object? o) => o switch
    {
        null => "null",
        decimal d => d.ToString(System.Globalization.CultureInfo.InvariantCulture),
        _ when o.GetType().GetFields().Length > 0 && o is not Enum => "{" + string.Join(", ", o.GetType().GetFields().Select(f => f.Name + " = " + f.GetValue(o))) + "}",
        _ => o.ToString() ?? "",
    };

    // ------------------------------------------------------------------ C#

    /// <summary>A Lean value as a C# expression, for the overload taking <c>decimal</c> or the exact one.</summary>
    private static string CSharp(Val v, bool decimalForm, Repr? r = null) => v switch
    {
        StrV str => Quote(str.V),
        ListV l when r?.Elem is Repr el => l.Items.Length == 0 ? $"new {TypeName(el, false)}[0]"
            : $"new {TypeName(el, false)}[] {{ {string.Join(", ", l.Items.Select(x => CSharp(x, false, el)))} }}",
        ListV l => "[" + string.Join(", ", l.Items.Select(x => CSharp(x, false))) + "]",
        ArrV a => CSharp(new ListV(a.Items), false, r),
        OptV o => o.V is null ? "none" : "some " + CSharp(o.V, false),
        Num n => n.V >= long.MinValue && n.V <= long.MaxValue ? n.V.ToString() : $"BigInteger.Parse(\"{n.V}\")",
        BoolV b => b.V ? "true" : "false",
        Fix f when f.V == f.F.Min && f.F.Signed => $"{f.F.CSharp}.MinValue",
        Fix f when f.V.Sign < 0 => $"({f.F.CSharp})({f.V})",
        Fix f => f.F.Bits < 32 ? $"({f.F.CSharp}){f.V}" : f.V + (f.F.Bits, f.F.Signed) switch { (32, false) => "u", (64, false) => "ul", (64, true) => "L", _ => "" },
        EnumV e => $"{Short(e.L.ClrName)}.{e.L.Cases[e.Index].ClrName}",
        StructV s when decimalForm && s.L.DecimalShaped => DecimalLiteral(((Num)s.Fields[0]).V, ((Num)s.Fields[1]).V) + "m",
        StructV s => $"new {Short(s.L.ClrName)}({string.Join(", ", s.Fields.Select(f => CSharp(f, false)))})",
        UnionV u => $"new {Short(u.L.ClrName)}.{u.L.Variants[u.Variant].ClrName}({string.Join(", ", u.Fields.Select((f, i) => CSharp(f, false, u.L.Variants[u.Variant].RuntimeFields[i].Repr)))})",
        _ => "?",
    };

    private static string Short(string clrName) => clrName[(clrName.LastIndexOf('.') + 1)..];

    private static string Quote(string s) => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\n", "\\n") + "\"";

    /// <summary>The C# name of a representation's type.</summary>
    private static string TypeName(Repr r, bool decimalForm) =>
        decimalForm && r.Layout?.DecimalShaped == true ? "decimal"
        : decimalForm && r.Kind == Kind.Nat ? "int"
        : r.Kind switch
        {
            Kind.Nat or Kind.Int => "BigInteger",
            Kind.Bool => "bool",
            Kind.String => "string",
            Kind.Fixed => FixedWidth.OfClr(r.ClrType).CSharp,
            Kind.List => $"LeanList<{TypeName(r.Elem!, false)}>",
            Kind.Option => $"LeanOption<{TypeName(r.Elem!, false)}>",
            Kind.Array => $"LeanArray<{TypeName(r.Elem!, false)}>",
            _ => Short(r.Layout!.ClrName),
        };

    /// <summary><c>2675, 3</c> as <c>2.675</c>; <c>-125, 3</c> as <c>-0.125</c>; <c>13, 0</c> as <c>13</c>.</summary>
    public static string DecimalLiteral(BigInteger mantissa, BigInteger scale)
    {
        string digits = BigInteger.Abs(mantissa).ToString().PadLeft((int)scale + 1, '0');
        int s = (int)scale;
        string body = s == 0 ? digits : digits[..^s] + "." + digits[^s..];
        return (mantissa.Sign < 0 ? "-" : "") + body;
    }

    private string Call(Example ex, bool decimalForm)
    {
        Param[] ps = ex.Export.Params.Where(p => p.Repr.IsData).ToArray();
        return $"{Short(_compiler.ClassName)}.{ex.Export.ClrName}({string.Join(", ", ex.Args.Select((a, i) => CSharp(a, decimalForm, ps[i].Repr)))})";
    }

    private static string ResultComment(Val v, bool decimalForm) => v switch
    {
        StructV s when decimalForm && s.L.DecimalShaped => DecimalLiteral(((Num)s.Fields[0]).V, ((Num)s.Fields[1]).V),
        ListV l => "[" + string.Join(", ", l.Items.Select(x => ResultComment(x, false))) + "]",
        ArrV a => "[" + string.Join(", ", a.Items.Select(x => ResultComment(x, false))) + "]",
        Fix f => f.V.ToString(),
        _ => CSharp(v, decimalForm),
    };

    private string Signature(Export e, bool decimalForm)
    {
        string T(Repr r) => TypeName(r, decimalForm);
        var ps = e.Params.Where(p => p.Repr.IsData).Select(p => $"{T(p.Repr)} {p.ClrName}");
        return $"public static {T(e.Result)} {e.ClrName}({string.Join(", ", ps)})";
    }

    // ------------------------------------------------------------------ writing

    public void Write(string outDir)
    {
        File.WriteAllText(Path.Combine(outDir, _asm + ".xml"), Xml());
        File.WriteAllText(Path.Combine(outDir, _asm + ".md"), Markdown());
        File.WriteAllText(Path.Combine(outDir, _asm + ".proof.json"), Json());
    }

    private string? DocOf(Name n)
    {
        foreach (Name m in _modules)
        {
            if (_loader.Modules[m].DocStringOf(n) is string d)
            {
                return d.Trim();
            }
        }
        return null;
    }

    private SourceRange? RangeOf(Name n) => _modules.Select(m => _loader.Modules[m].SourceRangeOf(n)).FirstOrDefault(r => r is not null);

    private string? LeanVizLink(Name n) => _o.LeanViz is null ? null
        : (_o.LeanViz.Contains('?') ? _o.LeanViz : _o.LeanViz.TrimEnd('/') + "/") + "#/d/" + Uri.EscapeDataString(n.ToString());

    private string? SourceLink(Name n, Name module)
    {
        if (_o.Source is null || RangeOf(n) is not SourceRange r)
        {
            return null;
        }
        return $"{_o.Source.TrimEnd('/')}/{module.ToString().Replace('.', '/')}.lean#L{r.Line}-L{r.EndLine}";
    }

    public string VerdictLine() => _verdict.Checked
        ? $"Every proof was re-checked by Tenet, an independent Lean kernel: {_verdict.Declarations:N0} declarations in {_verdict.Modules:N0} modules{(_verdict.WithImports ? ", Lean's own library under the project included" : ", the project's own modules")}, none rejected (Lean {_verdict.Lean})."
        : "The proofs were NOT re-checked by Tenet for this build (--no-check). Lean's kernel accepted them when the project was built.";

    private IEnumerable<Theorem> TheoremsAbout(Export e) => _theorems.Where(t => t.Mentions.Contains(e.Name)).OrderBy(t => t.Range?.Line ?? int.MaxValue);

    // Markdown in a docstring to XML-doc text: `code` to <c>, **bold** kept as text, everything else escaped.
    private static string XmlText(string md)
    {
        string esc = SecurityElement.Escape(md)!;
        esc = Regex.Replace(esc, "`([^`]+)`", "<c>$1</c>");
        esc = Regex.Replace(esc, @"\*\*([^*]+)\*\*", "$1");
        return esc;
    }

    private string Xml()
    {
        var sb = new StringBuilder();
        sb.AppendLine("<?xml version=\"1.0\"?>");
        sb.AppendLine("<doc>");
        sb.AppendLine($"  <assembly><name>{_asm}</name></assembly>");
        sb.AppendLine("  <members>");
        string cls = _compiler.ClassName;
        sb.AppendLine($"    <member name=\"T:{cls}\">");
        sb.AppendLine($"      <summary>Functions compiled from Lean by lean2il. {XmlText(VerdictLine())}</summary>");
        sb.AppendLine("    </member>");
        foreach (Export e in _compiler.Exports.Values)
        {
            foreach (bool dec in e.HasDecimalForm ? new[] { true, false } : [false])
            {
                sb.AppendLine($"    <member name=\"M:{cls}.{e.ClrName}({string.Join(",", e.Params.Where(p => p.Repr.IsData).Select(p => DocId(p.Repr, dec)))})\">");
                sb.AppendLine($"      <summary>{XmlText(DocOf(e.Name) ?? $"Compiled from the Lean definition {e.Name}.")}</summary>");
                foreach (Param p in e.Params.Where(p => p.Repr.IsData))
                {
                    sb.AppendLine($"      <param name=\"{p.ClrName}\">{XmlText(ParamDoc(p, dec))}</param>");
                }
                sb.AppendLine("      <remarks>");
                sb.AppendLine($"        <para>Compiled from the Lean definition <c>{e.Name}</c>. {XmlText(VerdictLine())}</para>");
                if (dec)
                {
                    sb.AppendLine("        <para>This overload moves the <c>decimal</c> in and out exactly, then calls the overload over the Lean structure. It throws <see cref=\"T:System.OverflowException\"/> only if the result has no <c>decimal</c> form, and never rounds on the way out.</para>");
                }
                var ths = TheoremsAbout(e).ToList();
                if (ths.Count > 0)
                {
                    sb.AppendLine("        <para>Proved about it:</para>");
                    sb.AppendLine("        <list type=\"bullet\">");
                    foreach (Theorem t in ths)
                    {
                        string link = LeanVizLink(t.Name) is string u ? $" <see href=\"{u}\">See it in LeanViz.</see>" : "";
                        sb.AppendLine($"          <item><term>{t.Name.LastString}</term><description>{XmlText(FirstParagraph(t.Doc))} <c>{SecurityElement.Escape(t.Statement)}</c>{link}</description></item>");
                    }
                    sb.AppendLine("        </list>");
                }
                sb.AppendLine("      </remarks>");
                foreach (Example ex in _examples.Where(x => x.Export == e))
                {
                    sb.AppendLine($"      <example><code>{SecurityElement.Escape(Call(ex, dec))} // {SecurityElement.Escape(ResultComment(ex.Result, dec))}, proved by {ex.Theorem.LastString}</code></example>");
                }
                sb.AppendLine("    </member>");
            }
        }
        foreach (Layout l in _compiler.Layouts)
        {
            sb.AppendLine($"    <member name=\"T:{l.ClrName}\"><summary>{XmlText(DocOf(l.Name) ?? $"The Lean type {l.Name}.")}</summary></member>");
            foreach (var (ctor, cn, _) in l.Cases)
            {
                sb.AppendLine($"    <member name=\"F:{l.ClrName}.{cn}\"><summary>{XmlText(DocOf(ctor) ?? ctor.ToString())}</summary></member>");
            }
            foreach (FieldSlot f in l.RuntimeFields)
            {
                sb.AppendLine($"    <member name=\"F:{l.ClrName}.{f.ClrName}\"><summary>{XmlText(DocOf(f.Name) ?? f.Name.ToString())}</summary></member>");
            }
            if (l.Kind == Kind.Struct)
            {
                sb.AppendLine($"    <member name=\"M:{l.ClrName}.#ctor{CtorIds(l.RuntimeFields)}\"><summary>{XmlText($"A {l.LeanType?.ToString() ?? l.Name.ToString()}, from its fields.")}</summary></member>");
            }
            if (l.Kind == Kind.Union)
            {
                string cases = string.Join(", ", l.Variants.Select((v, i) => $"{i} for {v.ClrName}"));
                sb.AppendLine($"    <member name=\"F:{l.ClrName}.Tag\"><summary>{XmlText($"Which case this is: {cases}. Or test the type: value is {Short(l.ClrName)}.{l.Variants[0].ClrName}.")}</summary></member>");
                foreach (Variant v in l.Variants)
                {
                    string vt = l.ClrName + "." + v.ClrName;
                    string doc = DocOf(v.Ctor) ?? $"The case {v.Ctor.LastString} of {l.Name}.";
                    sb.AppendLine($"    <member name=\"T:{vt}\"><summary>{XmlText(doc)}</summary></member>");
                    sb.AppendLine($"    <member name=\"M:{vt}.#ctor{CtorIds(v.RuntimeFields)}\"><summary>{XmlText(doc)}</summary></member>");
                    foreach (FieldSlot f in v.RuntimeFields)
                    {
                        sb.AppendLine($"    <member name=\"F:{vt}.{f.ClrName}\"><summary>{XmlText(DocOf(f.Name) ?? $"The {f.Name.LastString ?? f.ClrName} of a {v.Ctor.LastString}.")}</summary></member>");
                    }
                }
            }
        }
        sb.AppendLine("  </members>");
        sb.AppendLine("</doc>");
        return sb.ToString();
    }

    private static string CtorIds(FieldSlot[] fields) =>
        fields.Length == 0 ? "" : "(" + string.Join(",", fields.Select(f => DocId(f.Repr, false))) + ")";

    private static string DocId(Repr r, bool dec) =>
        dec && r.Layout?.DecimalShaped == true ? "System.Decimal"
        : dec && r.Kind == Kind.Nat ? "System.Int32"
        : r.Kind switch
        {
            Kind.Nat or Kind.Int => "System.Numerics.BigInteger",
            Kind.Bool => "System.Boolean",
            Kind.String => "System.String",
            Kind.Fixed => FixedWidth.OfClr(r.ClrType).Clr,
            Kind.List => "LeanToDotNet.Runtime.LeanList{" + DocId(r.Elem!, false) + "}",
            Kind.Option => "LeanToDotNet.Runtime.LeanOption{" + DocId(r.Elem!, false) + "}",
            Kind.Array => "LeanToDotNet.Runtime.LeanArray{" + DocId(r.Elem!, false) + "}",
            _ => r.Layout!.ClrName,
        };

    private static string ParamDoc(Param p, bool dec) => p.Repr.Kind switch
    {
        Kind.Nat => dec ? "A Lean Nat: zero or more. A negative value throws ArgumentOutOfRangeException." : "A Lean Nat: zero or more. A negative BigInteger throws ArgumentOutOfRangeException.",
        Kind.Int => "A Lean Int.",
        Kind.Fixed => $"A Lean {FixedWidth.OfClr(p.Repr.ClrType).Lean}: the same bits as a {FixedWidth.OfClr(p.Repr.ClrType).CSharp}.",
        Kind.String => "A Lean String.",
        Kind.List => $"A Lean List. Pass a LeanList, or an array, which converts to one.",
        Kind.Option => "A Lean Option.",
        Kind.Array => "A Lean Array. Pass a LeanArray, or a .NET array, which converts to one.",
        Kind.Struct when dec && p.Repr.Layout!.DecimalShaped => $"The value, as a decimal. It becomes a {p.Repr.Layout.Name} with the same mantissa and scale.",
        _ => $"A Lean {p.LeanName}.",
    };

    private static string FirstParagraph(string doc) => doc.Split("\n\n")[0].Replace('\n', ' ').Trim();

    private string Markdown()
    {
        var sb = new StringBuilder();
        string cls = _compiler.ClassName;
        sb.AppendLine($"# {_asm}");
        sb.AppendLine();
        sb.AppendLine($"Generated by lean2il from the Lean project `{Path.GetFileName(Path.GetFullPath(_o.Project))}`. Every word below comes from the Lean source: docstrings, theorem statements, and proved examples. Do not edit this file; edit the Lean and run lean2il again.");
        sb.AppendLine();
        sb.AppendLine($"> {VerdictLine()}");
        sb.AppendLine($"> Every example on this page was run against `{_asm}.dll` when it was built and returned the proved value.");
        if (DifferentialLine is not null)
        {
            sb.AppendLine("> " + DifferentialLine);
        }
        sb.AppendLine();
        foreach (var (m, doc) in _moduleDocs)
        {
            sb.AppendLine($"## From `{m}`");
            sb.AppendLine();
            sb.AppendLine(Regex.Replace(doc, "^#+ ", "### ", RegexOptions.Multiline));
            sb.AppendLine();
        }
        sb.AppendLine("## Calling it from C#");
        sb.AppendLine();
        sb.AppendLine("Reference the two assemblies (the second is lean2il's small runtime):");
        sb.AppendLine();
        sb.AppendLine("```xml");
        sb.AppendLine("<ItemGroup>");
        sb.AppendLine($"  <Reference Include=\"{_asm}\" HintPath=\"path/to/{_asm}.dll\" />");
        sb.AppendLine("  <Reference Include=\"LeanToDotNet.Runtime\" HintPath=\"path/to/LeanToDotNet.Runtime.dll\" />");
        sb.AppendLine("</ItemGroup>");
        sb.AppendLine("```");
        sb.AppendLine();
        string ns = cls.Contains('.') ? cls[..cls.LastIndexOf('.')] : "";
        foreach (Export e in _compiler.Exports.Values)
        {
            sb.AppendLine($"### `{Short(cls)}.{e.ClrName}`");
            sb.AppendLine();
            sb.AppendLine("```csharp");
            if (e.HasDecimalForm)
            {
                sb.AppendLine(Signature(e, true));
            }
            sb.AppendLine(Signature(e, false));
            sb.AppendLine("```");
            sb.AppendLine();
            sb.AppendLine(DocOf(e.Name) ?? $"Compiled from `{e.Name}`.");
            sb.AppendLine();
            var exs = _examples.Where(x => x.Export == e).ToList();
            if (exs.Count > 0)
            {
                sb.AppendLine("Proved examples, each one a theorem in the Lean and a call that was run against the IL:");
                sb.AppendLine();
                sb.AppendLine("```csharp");
                if (ns.Length > 0)
                {
                    sb.AppendLine($"using {ns};");
                    sb.AppendLine();
                }
                int w = exs.Max(x => Call(x, e.HasDecimalForm).Length);
                foreach (Example ex in exs)
                {
                    string call = Call(ex, e.HasDecimalForm);
                    sb.AppendLine($"{call};{new string(' ', w - call.Length)} // {ResultComment(ex.Result, e.HasDecimalForm)}   ({ex.Theorem.LastString})");
                }
                sb.AppendLine("```");
                sb.AppendLine();
            }
            var ths = TheoremsAbout(e).Where(t => !_examples.Any(x => x.Theorem.Equals(t.Name))).ToList();
            if (ths.Count > 0)
            {
                sb.AppendLine("What is proved about it:");
                sb.AppendLine();
                sb.AppendLine("| Theorem | Says | Rests on |");
                sb.AppendLine("|---|---|---|");
                foreach (Theorem t in ths)
                {
                    string name = LeanVizLink(t.Name) is string u ? $"[`{t.Name.LastString}`]({u})" : $"`{t.Name.LastString}`";
                    string src = SourceLink(t.Name, t.Module) is string s ? $" ([source]({s}))" : "";
                    string axioms = t.Axioms.Length == 0 ? "no axioms" : string.Join(", ", t.Axioms.Select(a => $"`{a}`"));
                    sb.AppendLine($"| {name}{src} | {MdCell(FirstParagraph(t.Doc))}<br>`{MdCell(t.Statement)}` | {axioms} |");
                }
                sb.AppendLine();
            }
        }
        var types = _compiler.Layouts.ToList();
        if (types.Count > 0)
        {
            sb.AppendLine("## Types");
            sb.AppendLine();
            foreach (Layout l in types)
            {
                sb.AppendLine($"### `{l.ClrName}`");
                sb.AppendLine();
                sb.AppendLine(DocOf(l.Name) ?? $"The Lean type `{l.Name}`.");
                sb.AppendLine();
                string Item(string code, Name n) => DocOf(n) is string d ? $"- `{code}`: {d.Replace('\n', ' ')}" : $"- `{code}`";
                foreach (var (ctor, cn, _) in l.Cases)
                {
                    sb.AppendLine(Item(cn, ctor));
                }
                foreach (Variant v in l.Variants)
                {
                    string fields = string.Join(", ", v.RuntimeFields.Select(f => $"{TypeName(f.Repr, false)} {f.ClrName}"));
                    sb.AppendLine(Item($"new {Short(l.ClrName)}.{v.ClrName}({fields})", v.Ctor));
                }
                foreach (FieldSlot f in l.RuntimeFields)
                {
                    sb.AppendLine(Item($"{TypeName(f.Repr, false)} {f.ClrName}", f.Name));
                }
                if (l.DecimalShaped)
                {
                    sb.AppendLine();
                    sb.AppendLine($"A `{Short(l.ClrName)}` has the shape of a `System.Decimal`, so every function over it also takes and returns `decimal`.");
                }
                sb.AppendLine();
            }
        }
        sb.AppendLine("## What this rests on");
        sb.AppendLine();
        sb.AppendLine("- Lean's kernel, which accepted every proof when the project was built.");
        sb.AppendLine("- " + VerdictLine());
        sb.AppendLine("- The axioms listed next to each theorem. `propext`, `Quot.sound` and `Classical.choice` are Lean's standard three; `sorryAx` would mean an unfinished proof and lean2il reports it.");
        sb.AppendLine("- lean2il's translation from the kernel term to IL, which the proved examples above test on every build" + (DifferentialLine is not null ? ", along with random inputs compared against Lean's own compiler" : "") + ", and `LeanToDotNet.Runtime`: `BigInteger` arithmetic with Lean's meaning for `Nat` and `Int`, Lean's meaning for fixed-width integers where it differs from C#'s (division by zero, shift counts), and the exact `decimal` conversion.");
        sb.AppendLine("- For recursive functions, the equation lemmas Lean proves for them (`f.eq_def`), which Tenet re-checks with everything else; each method is compiled from its equation's right-hand side.");
        sb.AppendLine();
        return sb.ToString();
    }

    private string? FileOf(Name n) => _modules.Where(m => _loader.Modules[m].Contains(n)).Select(RelFile).FirstOrDefault();

    /// <summary>The module's source file relative to the Lake project, e.g. <c>Finance/Rounding.lean</c>.</summary>
    private string RelFile(Name module) => string.Join('/', module.ToString().Split('.')) + ".lean";

    private static string MdCell(string s) => s.Replace("|", "\\|");

    private string Json()
    {
        var doc = new
        {
            assembly = _asm,
            dll = _asm + ".dll",
            markdown = _asm + ".md",
            @class = _compiler.ClassName,
            verdict = new { _verdict.Checked, _verdict.WithImports, _verdict.Declarations, _verdict.Modules, _verdict.Failed, seconds = Math.Round(_verdict.Elapsed.TotalSeconds, 1), lean = _verdict.Lean },
            differential = DifferentialLine,
            functions = _compiler.Exports.Values.Select(e => new
            {
                lean = e.Name.ToString(),
                method = e.ClrName,
                call = Short(_compiler.ClassName) + "." + e.ClrName,
                file = FileOf(e.Name),
                signatures = (e.HasDecimalForm ? new[] { Signature(e, true), Signature(e, false) } : [Signature(e, false)]),
                doc = DocOf(e.Name),
                source = RangeOf(e.Name) is SourceRange r ? new { line = r.Line, endLine = r.EndLine } : null,
                theorems = TheoremsAbout(e).Select(t => t.Name.ToString()).ToArray(),
                examples = _examples.Where(x => x.Export == e).Select(x => new { theorem = x.Theorem.ToString(), call = Call(x, e.HasDecimalForm), result = ResultComment(x.Result, e.HasDecimalForm) }).ToArray(),
            }),
            theorems = _theorems.Select(t => new
            {
                name = t.Name.ToString(),
                module = t.Module.ToString(),
                file = RelFile(t.Module),
                statement = t.Statement,
                doc = t.Doc,
                axioms = t.Axioms,
                line = t.Range?.Line,
                about = t.Mentions.Select(m => m.ToString()).ToArray(),
                leanviz = LeanVizLink(t.Name),
            }),
        };
        return JsonSerializer.Serialize(doc, new JsonSerializerOptions { WriteIndented = true, Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping });
    }
}
