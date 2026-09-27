using System.Numerics;
using System.Reflection;
using System.Reflection.Emit;
using Tenet.Kernel;
using ConstructorInfo = Tenet.Kernel.ConstructorInfo;
using Tenet.Olean;
using Environment = Tenet.Kernel.Environment;

namespace LeanToDotNet;

/// <summary>One parameter of an exported function.</summary>
internal sealed record Param(Name LeanName, string ClrName, Repr Repr);

/// <summary>An exported Lean definition and the .NET methods made from it.</summary>
internal sealed class Export
{
    public required Name Name { get; init; }
    public required DefinitionInfo Info { get; init; }
    public required string ClrName { get; init; }
    public required List<Param> Params { get; init; }
    public required Repr Result { get; init; }
    public required MethodBuilder Raw { get; init; }
    public MethodBuilder? DecimalOverload { get; set; }

    /// <summary>
    /// For an export: the internal method holding its body. The public method checks its arguments, calls this,
    /// and reruns it on a big stack if the recursion under it runs out of room. Calls between compiled functions go
    /// straight here. Null for a helper, whose body is in <see cref="Raw"/>.
    /// </summary>
    public MethodBuilder? Impl { get; init; }

    public MethodBuilder Target => Impl ?? Raw;

    /// <summary>False for a recursive helper compiled because an export needs it: an internal method, no docs.</summary>
    public bool IsPublic { get; init; } = true;

    /// <summary>The universe levels this copy is instantiated at.</summary>
    public Level[] Levels { get; init; } = [];

    /// <summary>
    /// For a helper with type or instance parameters: the arguments this copy is specialized to, one per parameter
    /// that is neither data nor a proof (null in the other positions). A helper used at two types is two methods.
    /// </summary>
    public Expr?[]? Fixed { get; init; }

    /// <summary>
    /// For a helper specialized to a lambda that uses local variables: those variables, as extra parameters after
    /// the helper's own. Each fixed argument is closed over all of them, so the body applies it to them. This is how
    /// <c>xs.map (fun x => x + k)</c> compiles without a delegate: <c>k</c> becomes a parameter of the copy of
    /// <c>List.map</c> made for that lambda.
    /// </summary>
    public List<(Name Name, Expr Type, Repr Repr)> Captures { get; init; } = [];

    /// <summary>
    /// For a recursive definition: the statement of its equation lemma, <c>∀ xs, f xs = rhs</c>, proved by Lean and
    /// re-checked by Tenet. The method's body is compiled from <c>rhs</c>, where the recursive calls are ordinary calls.
    /// </summary>
    public Expr? Equation { get; init; }

    /// <summary>Whether the decimal overload exists: some parameter or the result is a decimal-shaped structure.</summary>
    public bool HasDecimalForm => Params.Any(p => p.Repr.Layout?.DecimalShaped == true) || Result.Layout?.DecimalShaped == true;
}

/// <summary>
/// Compiles Lean definitions, as Tenet decodes them from <c>.olean</c> files, to IL.
///
/// The input is the kernel's term, the one Tenet re-checked, not Lean's compiler IR. That keeps the claim short:
/// the IL computes the same function the theorems are about, because it was produced from the very term they
/// mention. The price is that kernel terms are not written for running. Type-class instances, coercions and
/// numerals are all definitions to unfold, a <c>match</c> is a recursor application, and a proof can sit anywhere
/// a value can. So compilation is mostly partial evaluation: unfold everything that is not a primitive, an exported
/// function or a recursor, reduce a recursor whose target is a known constructor, and turn the recursors left over
/// into branches. Types and proofs are erased; <c>Decidable</c> keeps its answer and loses its proof.
///
/// Recursion is compiled from equations, not from recursors. Lean elaborates a recursive definition into a term built
/// on <c>brecOn</c> or <c>WellFounded.fix</c>, which says nothing a machine can run efficiently; but it can prove, for
/// every recursive <c>f</c>, the equation <c>f.eq_def : ∀ xs, f xs = rhs</c>, where <c>rhs</c> is the body as written,
/// calling <c>f</c> directly. The build asks Lean for those equations, Tenet re-checks their proofs, and each method's
/// body is compiled from its <c>rhs</c>. So the IL computes something both kernels agree is equal to <c>f</c>.
///
/// What it does not do yet, and says so rather than miscompiling: function values, and inductive types with
/// parameters, indices or recursive fields beyond the built-in ones.
/// </summary>
internal sealed class Compiler
{
    private readonly OleanChecker _loader;
    private readonly Environment _env;
    private readonly Clr _clr;
    private readonly ModuleBuilder _module;
    private readonly Dictionary<Name, Primitive> _prims;
    private readonly Dictionary<string, Layout?> _layouts = new();
    private readonly Dictionary<string, string> _layoutFailures = new();
    private readonly Dictionary<Name, Export> _exports = new();
    /// <summary>Every compiled function, keyed by name and specialization: the exports and the helpers they need.</summary>
    private readonly Dictionary<string, Export> _functions = new();
    private readonly Queue<Export> _pending = new();
    private readonly IReadOnlyDictionary<Name, Expr> _equations;
    internal readonly IReadOnlyDictionary<Name, (Expr Rhs, Name[] Levels)> _replacements;
    private readonly string _namespace;
    private readonly TypeBuilder _class;
    private readonly MethodInfo _bigFromLong;
    private readonly MethodInfo _bigParse;
    private readonly MethodInfo _bigZero;
    private readonly MethodInfo _natCheck;

    public IReadOnlyDictionary<Name, Export> Exports => _exports;
    public IEnumerable<Layout> Layouts => _layouts.Values.OfType<Layout>();
    public string ClassName { get; }

    private readonly HashSet<Name> _own;

    public Compiler(OleanChecker loader, Environment env, Clr clr, ModuleBuilder module, string ns, string className, HashSet<Name> own,
        IReadOnlyDictionary<Name, Expr> equations, IReadOnlyDictionary<Name, (Expr Rhs, Name[] Levels)> replacements)
    {
        _own = own;
        _equations = equations;
        _replacements = replacements;
        _loader = loader;
        _env = env;
        _clr = clr;
        _module = module;
        _namespace = ns;
        ClassName = ns.Length == 0 ? className : ns + "." + className;
        _prims = Primitives.Build(clr);
        _class = module.DefineType(ClassName, TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.Class, clr.Object);
        _bigFromLong = clr.Static(clr.BigInteger, "op_Implicit", clr.Int64);
        _bigParse = clr.Static(clr.BigInteger, "Parse", clr.String);
        _bigZero = clr.BigInteger.GetProperty("Zero")!.GetGetMethod()!;
        _natCheck = clr.Static(clr.LeanNat, "Check", clr.BigInteger, clr.String);
    }

    // ------------------------------------------------------------------ names

    /// <summary><c>roundCents</c> to <c>RoundCents</c>, <c>to_even</c> to <c>ToEven</c>.</summary>
    public static string Pascal(string s)
    {
        // Lean allows ' ? ! in names (gcd', isEmpty?, get!); .NET does not.
        s = s.Trim('«', '»').Replace("'", "_prime").Replace("?", "_opt").Replace("!", "_bang");
        s = new string(s.Select(ch => char.IsLetterOrDigit(ch) || ch == '_' ? ch : '_').ToArray());
        var parts = s.Split('_', StringSplitOptions.RemoveEmptyEntries);
        string r = string.Concat(parts.Select(p => char.ToUpperInvariant(p[0]) + p[1..]));
        return r.Length > 0 && char.IsDigit(r[0]) ? "_" + r : r;
    }

    private static string[] Components(Name n)
    {
        var parts = new List<string>();
        for (Name m = n; !m.IsAnonymous; m = m.Prefix)
        {
            parts.Add(m.LastString ?? m.ToString());
        }
        parts.Reverse();
        return parts.ToArray();
    }

    /// <summary>
    /// A C# parameter name for a Lean binder: its own name in camelCase, or, when Lean made it up (the argument a
    /// definition by pattern matching takes, shown as <c>x✝</c>), a name from its type: <c>Tree tree</c>,
    /// <c>LeanList&lt;T&gt; items</c>, <c>BigInteger n</c>. Never the same as an earlier one.
    /// </summary>
    private string ParamName(Name binder, Expr domain, Repr r, TypeChecker tc, HashSet<string> taken)
    {
        string raw = binder.ToString();
        bool madeUp = binder.LastString is null || raw.Contains("_hyg", StringComparison.Ordinal) || raw.Contains('✝') || raw.StartsWith('_');
        string name = madeUp
            ? r.Kind switch
            {
                Kind.Nat => "n",
                Kind.Int or Kind.Fixed => "value",
                Kind.Bool => "flag",
                Kind.String => "text",
                Kind.List or Kind.Array => "items",
                Kind.Option => "option",
                _ when r.Layout is not null => Camel(Components(r.Layout.Name)[^1]),
                _ => "arg",
            }
            : Camel(binder.LastString!);
        if (name.Length == 0 || CSharpKeywords.Contains(name))
        {
            name += "Value";
        }
        string unique = name;
        for (int i = 2; !taken.Add(unique); i++)
        {
            unique = name + i;
        }
        return unique;
    }

    private static string Camel(string s)
    {
        string p = Pascal(s);
        return p.Length == 0 ? p : char.ToLowerInvariant(p[0]) + p[1..];
    }

    private static readonly HashSet<string> CSharpKeywords =
    [
        "abstract", "as", "base", "bool", "break", "byte", "case", "catch", "char", "checked", "class", "const", "continue",
        "decimal", "default", "delegate", "do", "double", "else", "enum", "event", "explicit", "extern", "false", "finally",
        "fixed", "float", "for", "foreach", "goto", "if", "implicit", "in", "int", "interface", "internal", "is", "lock",
        "long", "namespace", "new", "null", "object", "operator", "out", "override", "params", "private", "protected",
        "public", "readonly", "ref", "return", "sbyte", "sealed", "short", "sizeof", "stackalloc", "static", "string",
        "struct", "switch", "this", "throw", "true", "try", "typeof", "uint", "ulong", "unchecked", "unsafe", "ushort",
        "using", "virtual", "void", "volatile", "while",
    ];

    /// <summary>The .NET name of a Lean name: each component in PascalCase, the namespace kept.</summary>
    public static string ClrTypeName(Name n) => string.Join('.', Components(n).Select(Pascal));

    /// <summary>The method name for an export: the part of its name after the namespace, in PascalCase.</summary>
    private string MethodName(Name n)
    {
        string full = n.ToString();
        string rest = _namespace.Length > 0 && full.StartsWith(_namespace + ".", StringComparison.Ordinal) ? full[(_namespace.Length + 1)..] : full;
        return string.Concat(rest.Split('.').Select(Pascal));
    }

    // ------------------------------------------------------------------ representations

    private ConstantInfo? Resolve(Name n) => _env.Find(n);

    /// <summary>How a value of this type is held at run time, given the local context <paramref name="tc"/> sees.</summary>
    internal Repr ReprOf(Expr type, TypeChecker tc)
    {
        if (tc.IsProp(type))
        {
            return Repr.Erased;
        }
        Expr w = tc.Whnf(type);
        if (w is SortExpr)
        {
            return Repr.Erased;
        }
        if (w is PiExpr)
        {
            return EndsInSort(w, tc) ? Repr.Erased : new Repr(Kind.Unsupported, Why: $"a function value (of type {type}) would be needed at run time");
        }
        if (w.GetAppFn() is ConstExpr c)
        {
            switch (c.Name.ToString())
            {
                case "Nat": return new Repr(Kind.Nat, _clr.BigInteger);
                case "Int": return new Repr(Kind.Int, _clr.BigInteger);
                case "Bool": return new Repr(Kind.Bool, _clr.Bool);
                case "Decidable": return new Repr(Kind.Bool, _clr.Bool);
                case "String": return new Repr(Kind.String, _clr.String);
                case "UInt8" or "UInt16" or "UInt32" or "UInt64" or "Int8" or "Int16" or "Int32" or "Int64":
                    return new Repr(Kind.Fixed, _clr.Fixed[c.Name.ToString()]);
                case "Float" or "Float32":
                    return new Repr(Kind.Unsupported, Why: $"{c.Name} is not compiled yet: Lean's kernel does not model floating point, so there is nothing proved about it to preserve");
                case "Char":
                    return new Repr(Kind.Unsupported, Why: "Char is not compiled yet; use String, or the code point as a Nat or UInt32");
                // A value and a proof about it: at run time just the value, as in Lean's own compiler.
                case "Fin": return new Repr(Kind.Nat, _clr.BigInteger) { Constrained = true };
                case "Subtype":
                {
                    w.GetAppArgs(out Expr[] sargs);
                    return sargs.Length == 2 ? ReprOf(sargs[0], tc) with { Constrained = true } : new Repr(Kind.Unsupported, Why: "unexpected shape");
                }
                case "List" or "Option" or "Array":
                {
                    w.GetAppArgs(out Expr[] targs);
                    Repr elem = targs.Length == 1 ? ReprOf(targs[0], tc) : Repr.Erased;
                    if (!elem.IsData)
                    {
                        return new Repr(Kind.Unsupported, Why: $"a {c.Name} of {targs.FirstOrDefault()} has no run-time form: {elem.Why ?? "its elements are not data"}");
                    }
                    Kind k = c.Name.ToString() switch { "List" => Kind.List, "Option" => Kind.Option, _ => Kind.Array };
                    Type generic = k switch { Kind.List => _clr.LeanList, Kind.Option => _clr.LeanOption, _ => _clr.LeanArray };
                    return new Repr(k, GenericInst.Of(generic, elem.ClrType), Elem: elem);
                }
            }
            if (Resolve(c.Name) is InductiveInfo ind)
            {
                w.GetAppArgs(out Expr[] iargs);
                Expr[] parms = iargs.Take(ind.NumParams).ToArray();
                Layout? l = LayoutFor(ind, c.Levels, parms, tc);
                if (l is not null)
                {
                    return new Repr(l.Kind, l.Builder, l);
                }
                return new Repr(Kind.Unsupported, Why: $"the type {c.Name} is not compiled: {_layoutFailures.GetValueOrDefault(LayoutKey(ind, parms), "unsupported shape")}");
            }
        }
        return new Repr(Kind.Unsupported, Why: $"no run-time form for the type {type}");
    }

    private static bool EndsInSort(Expr pi, TypeChecker tc)
    {
        Expr t = pi;
        while (true)
        {
            t = tc.Whnf(t);
            if (t is PiExpr p)
            {
                Expr fv = tc.Lctx.MkLocalDecl(p.BinderName, p.Domain, p.Info);
                t = ExprOps.Instantiate1(p.Body, fv);
                continue;
            }
            return t is SortExpr;
        }
    }

    private static string LayoutKey(InductiveInfo ind, Expr[] parms) =>
        parms.Length == 0 ? ind.Name.ToString() : ind.Name + "(" + string.Join(", ", parms.Select(p => p.ToString())) + ")";

    /// <summary>The constructor's field telescope at these levels and parameters.</summary>
    private static Expr CtorFields(ConstructorInfo ctor, InductiveInfo ind, Level[] levels, Expr[] parms, TypeChecker tc)
    {
        Expr t = ExprOps.InstantiateLevelParams(ctor.Type, ind.LevelParams, levels.Length == ind.LevelParams.Length ? levels : ind.LevelParams.Select(_ => Level.Zero).ToArray());
        foreach (Expr p in parms)
        {
            t = ExprOps.Instantiate1(((PiExpr)tc.Whnf(t)).Body, p);
        }
        return t;
    }

    /// <summary>Whether a field's type is the inductive itself at the same parameters: a recursive field.</summary>
    private static bool IsSelf(Expr type, InductiveInfo ind, Expr[] parms, TypeChecker tc)
    {
        Expr w = tc.Whnf(type);
        if (w.GetAppFn() is not ConstExpr c || !c.Name.Equals(ind.Name))
        {
            return false;
        }
        w.GetAppArgs(out Expr[] a);
        return a.Length == parms.Length && a.Zip(parms).All(x => Expr.Eq(x.First, x.Second));
    }

    /// <summary>
    /// Why this type cannot become a .NET type, or null when it can: checked over everything it contains before any
    /// .NET type is defined, so a type that fails halfway never leaves a half-built class in the assembly.
    /// </summary>
    private string? WhyNotLayout(InductiveInfo ind, Level[] levels, Expr[] parms, TypeChecker tc, HashSet<string> visiting)
    {
        string key = LayoutKey(ind, parms);
        if (_layouts.TryGetValue(key, out Layout? known))
        {
            return known is null ? _layoutFailures.GetValueOrDefault(key, "unsupported shape") : null;
        }
        if (!visiting.Add(key))
        {
            return null; // recursion through itself: fine, it is being checked
        }
        string? why =
            !_own.Contains(ind.Name) && ind.Name.ToString() != "Prod" ? "only types declared in the compiled project become .NET types" :
            ind.NumIndices > 0 ? "it has indices (it is a family of types)" :
            ind.All.Length > 1 ? "it is mutually inductive" :
            ind.NumNested > 0 ? "it contains itself inside another type" :
            parms.Any(p => p.HasFVar) ? "it is used at a type that depends on a local value" : null;
        if (why is not null)
        {
            return why;
        }
        Expr sort = ind.Type;
        foreach (Expr p in parms)
        {
            sort = ExprOps.Instantiate1(((PiExpr)tc.Whnf(ExprOps.InstantiateLevelParams(sort, ind.LevelParams, ind.LevelParams.Select(_ => Level.One).ToArray()))).Body, p);
        }
        if (tc.Whnf(sort) is SortExpr srt && srt.Level.NormalizesToZero())
        {
            return "it is a proposition";
        }
        if (ind.Ctors.Length == 0)
        {
            return "it has no constructors";
        }
        foreach (Name cn in ind.Ctors)
        {
            var ctor = (ConstructorInfo)Resolve(cn)!;
            Expr t = CtorFields(ctor, ind, levels, parms, tc);
            for (int i = 0; i < ctor.NumFields; i++)
            {
                var p = (PiExpr)tc.Whnf(t);
                if (!IsSelf(p.Domain, ind, parms, tc) && WhyNotField(p.Domain, tc, visiting) is string w)
                {
                    return $"field {p.BinderName} of {cn.LastString}: {w}";
                }
                t = ExprOps.Instantiate1(p.Body, tc.Lctx.MkLocalDecl(p.BinderName, p.Domain));
            }
        }
        return null;
    }

    private string? WhyNotField(Expr type, TypeChecker tc, HashSet<string> visiting)
    {
        if (tc.IsProp(type))
        {
            return null;
        }
        Expr w = tc.Whnf(type);
        if (w is SortExpr)
        {
            return null;
        }
        if (w is PiExpr)
        {
            return EndsInSort(w, tc) ? null : "a function stored in a field is not compiled yet";
        }
        if (w.GetAppFn() is not ConstExpr c)
        {
            return $"no run-time form for {type}";
        }
        w.GetAppArgs(out Expr[] a);
        switch (c.Name.ToString())
        {
            case "Nat" or "Int" or "Bool" or "String" or "Decidable" or "UInt8" or "UInt16" or "UInt32" or "UInt64" or "Int8" or "Int16" or "Int32" or "Int64":
                return null;
            case "List" or "Option" or "Array":
                return a.Length == 1 ? WhyNotField(a[0], tc, visiting) : "unexpected shape";
            case "Fin":
                return null;
            case "Subtype":
                return a.Length == 2 ? WhyNotField(a[0], tc, visiting) : "unexpected shape";
        }
        if (Resolve(c.Name) is InductiveInfo ind)
        {
            return WhyNotLayout(ind, c.Levels, a.Take(ind.NumParams).ToArray(), tc, visiting);
        }
        return $"no run-time form for {c.Name}";
    }

    /// <summary>The .NET type for an inductive at these parameters, made the first time it is needed, or null with the reason recorded.</summary>
    private Layout? LayoutFor(InductiveInfo ind, Level[] levels, Expr[] parms, TypeChecker tc)
    {
        string key = LayoutKey(ind, parms);
        if (_layouts.TryGetValue(key, out Layout? known))
        {
            return known;
        }
        if (WhyNotLayout(ind, levels, parms, new TypeChecker(_env, tc.Lctx), new HashSet<string>()) is string why)
        {
            _layoutFailures[key] = why;
            _layouts[key] = null;
            return null;
        }
        string clrName = ClrTypeName(ind.Name) + (parms.Length > 0 ? "Of" + string.Concat(parms.Select(TypeArgName)) : "");
        var ctors = ind.Ctors.Select(n => (ConstructorInfo)Resolve(n)!).ToArray();
        Expr leanType = Expr.MkApp(Expr.Const(ind.Name, levels), parms);
        if (parms.Length == 0 && ctors.All(c => c.NumFields == 0))
        {
            // Built by hand rather than with DefineEnum, whose base type is the running process's System.Enum and would
            // leave the assembly referring to System.Private.CoreLib.
            TypeBuilder eb = _module.DefineType(clrName, TypeAttributes.Public | TypeAttributes.Sealed, _clr.Enum);
            eb.DefineField("value__", _clr.Int32, FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName);
            var layout = new Layout { Name = ind.Name, Info = ind, Kind = Kind.Enum, Builder = eb, ClrName = clrName, LeanType = leanType };
            for (int i = 0; i < ctors.Length; i++)
            {
                string cn = Pascal(ctors[i].Name.LastString!);
                FieldBuilder lit = eb.DefineField(cn, eb, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault);
                lit.SetConstant(i);
                layout.Cases.Add((ctors[i].Name, cn, lit));
            }
            _layouts[key] = layout;
            _structs.Add(eb);
            return layout;
        }
        if (ctors.Length == 1)
        {
            ConstructorInfo ctor = ctors[0];
            TypeBuilder tb = _module.DefineType(clrName, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.Class, _clr.Object);
            var st = new Layout { Name = ind.Name, Info = ind, Kind = Kind.Struct, Builder = tb, ClrName = clrName, Params = parms, Levels = levels, LeanType = leanType };
            _layouts[key] = st;   // before the fields, so a field of this very type finds it
            _structs.Add(tb);
            var (fields, self) = DefineFields(tb, ctor, ind, levels, parms, tc);
            st.Fields.AddRange(fields);
            st.SelfFields = self;
            st.Ctor = DefineCtor(tb, st.RuntimeFields, _clr.Object.GetConstructor(Type.EmptyTypes)!, null);
            DefineDataMethods(tb);
            return st;
        }
        // A union: an abstract class with a Tag, and a sealed nested class per constructor.
        TypeBuilder baseType = _module.DefineType(clrName, TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Class, _clr.Object);
        var un = new Layout { Name = ind.Name, Info = ind, Kind = Kind.Union, Builder = baseType, ClrName = clrName, Params = parms, Levels = levels, LeanType = leanType };
        _layouts[key] = un;
        _structs.Add(baseType);
        un.TagField = baseType.DefineField("Tag", _clr.Int32, FieldAttributes.Public | FieldAttributes.InitOnly);
        ConstructorBuilder baseCtor = baseType.DefineConstructor(MethodAttributes.Family, CallingConventions.Standard, [_clr.Int32]);
        {
            ILGenerator il = baseCtor.GetILGenerator();
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Call, _clr.Object.GetConstructor(Type.EmptyTypes)!);
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Stfld, un.TagField);
            il.Emit(OpCodes.Ret);
        }
        for (int i = 0; i < ctors.Length; i++)
        {
            string cn = Pascal(ctors[i].Name.LastString!);
            TypeBuilder nt = baseType.DefineNestedType(cn, TypeAttributes.NestedPublic | TypeAttributes.Sealed | TypeAttributes.Class, baseType);
            _nested.Add(nt);
            var (fields, self) = DefineFields(nt, ctors[i], ind, levels, parms, tc);
            ConstructorBuilder cb = DefineCtor(nt, fields.Where(f => f.Field is not null).ToArray(), baseCtor, i);
            DefineDataMethods(nt);
            un.Variants.Add(new Variant(ctors[i].Name, cn, nt, fields, cb, self));
        }
        return un;
    }

    private readonly List<TypeBuilder> _nested = new();

    /// <summary>Short text for a type argument in a class name: <c>Int</c>, <c>ListInt</c>.</summary>
    private static string TypeArgName(Expr e) => e switch
    {
        ConstExpr c => Pascal(c.Name.LastString ?? "T"),
        AppExpr => string.Concat(new[] { e.GetAppFn() }.Concat(e.GetAppNumArgs() > 0 ? GetArgs(e) : []).Select(TypeArgName)),
        _ => "T",
    };

    private static Expr[] GetArgs(Expr e)
    {
        e.GetAppArgs(out Expr[] a);
        return a;
    }

    private (List<FieldSlot> Fields, int Self) DefineFields(TypeBuilder tb, ConstructorInfo ctor, InductiveInfo ind, Level[] levels, Expr[] parms, TypeChecker tc0)
    {
        var tc = new TypeChecker(_env, tc0.Lctx);
        var fields = new List<FieldSlot>();
        int self = 0;
        Expr t = CtorFields(ctor, ind, levels, parms, tc);
        for (int i = 0; i < ctor.NumFields; i++)
        {
            var p = (PiExpr)tc.Whnf(t);
            Repr r = ReprOf(p.Domain, tc);
            if (IsSelf(p.Domain, ind, parms, tc))
            {
                self++;
            }
            string fn = Pascal(p.BinderName.LastString ?? $"field{i}");
            if (fn.Length == 0 || fn == "Tag")
            {
                fn = "Field" + i;
            }
            FieldBuilder? fb = r.IsData ? tb.DefineField(fn, r.ClrType, FieldAttributes.Public | FieldAttributes.InitOnly) : null;
            fields.Add(new FieldSlot(Name.Parse(ind.Name + "." + p.BinderName), fn, r.IsData ? r : Repr.Erased, fb));
            t = ExprOps.Instantiate1(p.Body, tc.Lctx.MkLocalDecl(p.BinderName, p.Domain));
        }
        return (fields, self);
    }

    /// <summary>ToString, Equals and GetHashCode over the fields, through LeanToDotNet.Runtime.LeanData.</summary>
    private void DefineDataMethods(TypeBuilder tb)
    {
        void Override(string name, Type result, Type[] ps, string helper)
        {
            MethodBuilder m = tb.DefineMethod(name, MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.HideBySig, result, ps);
            ILGenerator il = m.GetILGenerator();
            il.Emit(OpCodes.Ldarg_0);
            if (ps.Length == 1)
            {
                il.Emit(OpCodes.Ldarg_1);
            }
            il.Emit(OpCodes.Call, _clr.Static(_clr.LeanData, helper, [_clr.Object, .. ps]));
            il.Emit(OpCodes.Ret);
        }
        Override("ToString", _clr.String, [], "Show");
        Override("Equals", _clr.Bool, [_clr.Object], "Equal");
        Override("GetHashCode", _clr.Int32, [], "Hash");
    }

    private ConstructorBuilder DefineCtor(TypeBuilder tb, FieldSlot[] rt, System.Reflection.ConstructorInfo baseCtor, int? tag)
    {
        ConstructorBuilder cb = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, rt.Select(f => f.Repr.ClrType).ToArray());
        for (int i = 0; i < rt.Length; i++)
        {
            cb.DefineParameter(i + 1, ParameterAttributes.None, char.ToLowerInvariant(rt[i].ClrName[0]) + rt[i].ClrName[1..]);
        }
        ILGenerator il = cb.GetILGenerator();
        il.Emit(OpCodes.Ldarg_0);
        if (tag is int k)
        {
            il.Emit(OpCodes.Ldc_I4, k);
        }
        il.Emit(OpCodes.Call, baseCtor);
        for (int i = 0; i < rt.Length; i++)
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg, i + 1);
            il.Emit(OpCodes.Stfld, rt[i].Field!);
        }
        il.Emit(OpCodes.Ret);
        return cb;
    }

    private readonly List<TypeBuilder> _structs = new();

    /// <summary>Reduction without code generation, for evaluating closed terms such as the arguments of an example.</summary>
    internal Body NewReducer() => new(this, null);

    /// <summary>The layout already made for an inductive, if it became a .NET type.</summary>
    internal Layout? LayoutOf(Name n) => _layouts.GetValueOrDefault(n.ToString());

    /// <summary>Lean marks every recursive definition by also emitting <c>f._unsafe_rec</c>, the version its own compiler runs.</summary>
    internal bool IsRecursive(Name n) => Resolve(Name.Parse(n + "._unsafe_rec")) is not null;

    /// <summary>The recursive definitions an export reaches, whose equation lemmas the build has to ask Lean for.</summary>
    public HashSet<Name> RecursiveReachableFrom(IEnumerable<Name> roots, HashSet<Name> replaced)
    {
        var found = new HashSet<Name>();
        var seen = new HashSet<Name>();
        var stack = new Stack<Name>(roots);
        while (stack.Count > 0)
        {
            Name n = stack.Pop();
            if (!seen.Add(n) || _prims.ContainsKey(n) || Body.ArrayOps.Contains(n.ToString()))
            {
                continue;
            }
            string sn = n.ToString();
            if (Equations.Replacements.TryGetValue(sn, out Equations.Replacement? rep))
            {
                replaced.Add(n);
                foreach (string u in rep.Uses)
                {
                    stack.Push(Name.Parse(u));
                }
                continue;
            }
            if (sn.EndsWith("._unsafe_rec", StringComparison.Ordinal) || sn.EndsWith("._sunfold", StringComparison.Ordinal)
                || sn.EndsWith(".brecOn", StringComparison.Ordinal) || sn.EndsWith(".below", StringComparison.Ordinal))
            {
                continue;
            }
            if (Resolve(n) is not DefinitionInfo d)
            {
                continue;
            }
            if (IsRecursive(n))
            {
                found.Add(n);
            }
            ExprOps.ForEach(d.Value!, (x, _) =>
            {
                if (x is ConstExpr c)
                {
                    stack.Push(c.Name);
                }
                return true;
            });
        }
        return found;
    }

    /// <summary>
    /// The method for a recursive helper at these arguments, declared the first time it is needed, and the local
    /// variables the call has to pass along. Data arguments are parameters; proofs are erased; type, instance and
    /// function arguments are fixed into the copy, closed over any local variables they use, which become extra
    /// parameters.
    /// </summary>
    internal (Export Fn, Expr[] Captured) Helper(ConstExpr c, Expr[] args, TypeChecker caller)
    {
        if (Resolve(c.Name) is not DefinitionInfo def)
        {
            throw new CompileError($"internal: {c.Name} is not a definition");
        }
        if (!_equations.TryGetValue(c.Name, out Expr? equation))
        {
            throw new CompileError($"{c.Name} is recursive and Lean gave no equation lemma for it, so it cannot be compiled");
        }

        // Which arguments are fixed into the copy, and which local variables they use.
        var tc = new TypeChecker(_env, new LocalContext());
        var kinds = new Repr[args.Length];
        var isProof = new bool[args.Length];
        {
            var probe = new TypeChecker(_env, caller.Lctx);
            Expr pt = def.InstantiateTypeLevelParams(c.Levels);
            for (int i = 0; i < args.Length; i++)
            {
                if (probe.Whnf(pt) is not PiExpr p)
                {
                    throw new CompileError($"{c.Name} is applied to more arguments than it takes");
                }
                kinds[i] = ReprOf(p.Domain, probe);
                isProof[i] = !kinds[i].IsData && probe.IsProp(p.Domain);
                pt = ExprOps.Instantiate1(p.Body, args[i]);
            }
        }
        var captured = new List<Expr>();
        for (int i = 0; i < args.Length; i++)
        {
            if (kinds[i].IsData || isProof[i] || !args[i].HasFVar)
            {
                continue;
            }
            ExprOps.ForEach(args[i], (x, _) =>
            {
                if (x is FVarExpr f && !captured.Any(y => ((FVarExpr)y).Id.Equals(f.Id)))
                {
                    captured.Add(f);
                }
                return x.HasFVar;
            });
        }
        // Mirror the captured variables in a fresh context, in order, and close each fixed argument over them.
        var mirrorCtx = new LocalContext();
        var mirror = new List<Expr>();
        var captures = new List<(Name, Expr, Repr)>();
        Expr Remap(Expr e) => ExprOps.Replace(e, (x, _) => x is FVarExpr f && captured.FindIndex(y => ((FVarExpr)y).Id.Equals(f.Id)) is int k && k >= 0 ? mirror[k] : null);
        var mtc = new TypeChecker(_env, mirrorCtx);
        foreach (Expr f in captured)
        {
            LocalDecl d = caller.Lctx.Get(f);
            Expr type = Remap(d.Type);
            Repr r = ReprOf(type, mtc);
            if (!r.IsData && !mtc.IsProp(type))
            {
                throw new CompileError($"{c.Name} is passed a function that uses the local {(r.Kind == Kind.Erased ? "type" : "function")} {d.UserName}, which is not compiled yet");
            }
            mirror.Add(mirrorCtx.MkLocalDecl(d.UserName, type));
            captures.Add((d.UserName, type, r.IsData ? r : Repr.Erased));
        }
        var fixedArgs = new Expr?[args.Length];
        for (int i = 0; i < args.Length; i++)
        {
            if (!kinds[i].IsData && !isProof[i])
            {
                fixedArgs[i] = mirror.Count == 0 ? args[i] : mirrorCtx.MkLambda(mirror, Remap(args[i]));
            }
        }

        // The signature of the copy.
        var ps = new List<Param>();
        Expr t = def.InstantiateTypeLevelParams(c.Levels);
        var capFvars = captures.Select(cp => tc.Lctx.MkLocalDecl(cp.Item1, cp.Item2)).ToList();
        for (int i = 0; i < args.Length; i++)
        {
            var p = (PiExpr)tc.Whnf(t);
            Expr bound = fixedArgs[i] is Expr fx
                ? (captures.Count == 0 ? fx : Expr.MkApp(fx, capFvars))
                : tc.Lctx.MkLocalDecl(p.BinderName, p.Domain, p.Info);
            ps.Add(new Param(p.BinderName, p.BinderName.LastString ?? "arg", kinds[i].IsData ? ReprOf(p.Domain, tc) : Repr.Erased));
            t = ExprOps.Instantiate1(p.Body, bound);
        }
        if (tc.Whnf(t) is PiExpr)
        {
            throw new CompileError($"{c.Name} is partially applied; a function value would be needed at run time");
        }
        Repr result = ReprOf(t, tc);
        if (!result.IsData)
        {
            throw new CompileError($"{c.Name}: {result.Why ?? "its result is not data"}");
        }
        string key = c.Name + "|" + string.Join(",", c.Levels.Select(l => l.ToString())) + "|" + string.Join(",", fixedArgs.Select(a => a?.ToString() ?? "_"))
            + "|" + string.Join(",", captures.Select(cp => cp.Item2.ToString()));
        if (!_functions.TryGetValue(key, out Export? e))
        {
            var runtime = ps.Where(p => p.Repr.IsData).Select(p => p.Repr.ClrType).Concat(captures.Where(cp => cp.Item3.IsData).Select(cp => cp.Item3.ClrType)).ToArray();
            string clrName = "Rec" + string.Concat(c.Name.ToString().Split('.').Select(Pascal)) + (_functions.Count(kv => kv.Value.Name.Equals(c.Name)) is int k && k > 0 ? "_" + k : "");
            MethodBuilder mb = _class.DefineMethod(clrName, MethodAttributes.Assembly | MethodAttributes.Static, result.ClrType, runtime);
            e = new Export
            {
                Name = c.Name, Info = def, ClrName = clrName, Params = ps, Result = result, Raw = mb,
                IsPublic = false, Levels = c.Levels, Fixed = fixedArgs, Captures = captures,
                Equation = ExprOps.InstantiateLevelParams(equation, def.LevelParams, c.Levels),
            };
            _functions[key] = e;
            _pending.Enqueue(e);
        }
        return (e, captured.ToArray());
    }

    private static bool IsInstanceLike(Expr type, TypeChecker tc) => tc.Whnf(type) is not PiExpr;

    /// <summary>Compile the helpers the compiled bodies have asked for, until none are left.</summary>
    public void CompilePending()
    {
        while (_pending.Count > 0)
        {
            CompileBody(_pending.Dequeue());
        }
    }

    // ------------------------------------------------------------------ signatures

    /// <summary>Declare the .NET method for an exported definition. Bodies come later, so exports can call each other.</summary>
    public Export Declare(Name name)
    {
        if (Resolve(name) is not DefinitionInfo def)
        {
            throw new CompileError($"{name} is marked @[export] but is not a definition");
        }
        if (def.LevelParams.Length > 0)
        {
            throw new CompileError($"{name} is universe polymorphic; lean2il compiles monomorphic definitions only");
        }
        var tc = new TypeChecker(_env);
        var ps = new List<Param>();
        var taken = new HashSet<string>();
        Expr t = def.Type;
        while (tc.Whnf(t) is PiExpr p)
        {
            Repr r = ReprOf(p.Domain, tc);
            if (r.Kind == Kind.Unsupported)
            {
                throw new CompileError($"{name}, parameter {p.BinderName}: {r.Why}");
            }
            ps.Add(new Param(p.BinderName, r.IsData ? ParamName(p.BinderName, p.Domain, r, tc, taken) : "_", r));
            t = ExprOps.Instantiate1(p.Body, tc.Lctx.MkLocalDecl(p.BinderName, p.Domain, p.Info));
        }
        Repr result = ReprOf(t, tc);
        if (!result.IsData)
        {
            throw new CompileError($"{name}: {(result.Why ?? "its result is a type or a proof, so there is nothing to compute")}");
        }
        var runtime = ps.Where(p => p.Repr.IsData).ToArray();
        MethodBuilder mb = _class.DefineMethod(MethodName(name), MethodAttributes.Public | MethodAttributes.Static,
            result.ClrType, runtime.Select(p => p.Repr.ClrType).ToArray());
        for (int i = 0; i < runtime.Length; i++)
        {
            mb.DefineParameter(i + 1, ParameterAttributes.None, runtime[i].ClrName);
        }
        MethodBuilder impl = _class.DefineMethod(MethodName(name) + "_Impl", MethodAttributes.Assembly | MethodAttributes.Static,
            result.ClrType, runtime.Select(p => p.Repr.ClrType).ToArray());
        var e = new Export
        {
            Name = name, Info = def, ClrName = MethodName(name), Params = ps, Result = result, Raw = mb, Impl = impl,
            Equation = IsRecursive(name)
                ? _equations.GetValueOrDefault(name) ?? throw new CompileError($"{name} is recursive and Lean gave no equation lemma for it, so it cannot be compiled")
                : null,
        };
        _exports[name] = e;
        _functions[name + "||"] = e;
        return e;
    }

    // ------------------------------------------------------------------ bodies

    public void CompileBody(Export e)
    {
        var body = new Body(this, e.Target.GetILGenerator()) { Self = e };
        var capFvars = new List<Expr>();
        if (e.Equation is not null)
        {
            // A recursive function: make sure a few more frames fit before taking one (see LeanStack).
            body.Il.Emit(OpCodes.Call, _clr.Static(_clr.LeanStack, "Check"));
        }
        var tc = body.Tc;
        Expr t = e.Info.InstantiateTypeLevelParams(e.Levels);
        foreach (var (cn, ct, _) in e.Captures)
        {
            capFvars.Add(tc.Lctx.MkLocalDecl(cn, ct));
        }
        var fvars = new List<Expr>();
        int arg = 0;
        for (int i = 0; i < e.Params.Count; i++)
        {
            Param p = e.Params[i];
            var pi = (PiExpr)tc.Whnf(t);
            Expr bound = e.Fixed?[i] is Expr fx
                ? (capFvars.Count == 0 ? fx : Expr.MkApp(fx, capFvars))
                : tc.Lctx.MkLocalDecl(pi.BinderName, pi.Domain, pi.Info);
            fvars.Add(bound);
            t = ExprOps.Instantiate1(pi.Body, bound);
            if (e.Fixed?[i] is not null)
            {
                continue;
            }
            if (p.Repr.IsData)
            {
                body.Bind(bound, new Slot.Arg(arg, p.Repr));
                arg++;
            }
            else
            {
                body.Bind(bound, Slot.Erased.Instance);
            }
        }
        for (int i = 0; i < e.Captures.Count; i++)
        {
            if (e.Captures[i].Repr.IsData)
            {
                body.Bind(capFvars[i], new Slot.Arg(arg++, e.Captures[i].Repr));
            }
            else
            {
                body.Bind(capFvars[i], Slot.Erased.Instance);
            }
        }
        Expr app = e.Equation is Expr eq ? EquationRhs(eq, fvars, e.Name) : Expr.MkApp(e.Info.InstantiateValueLevelParams(e.Levels), fvars);
        body.MarkLoopStart();
        try
        {
            Repr r = body.Emit(app, tail: true);
            body.Coerce(r, e.Result);
        }
        catch (CompileError ce)
        {
            throw new CompileError($"{e.Name}: {ce.Message}");
        }
        body.Il.Emit(OpCodes.Ret);
        if (e.Impl is not null)
        {
            CompileEntry(e);
        }
    }

    /// <summary>
    /// The public method of an export: refuse a negative <c>Nat</c>, call the body, and if the recursion under it runs
    /// out of stack, run the same call again on a thread with a 1 GB stack (see <c>LeanStack</c>).
    /// </summary>
    private void CompileEntry(Export e)
    {
        ILGenerator il = e.Raw.GetILGenerator();
        Param[] runtime = e.Params.Where(p => p.Repr.IsData).ToArray();
        for (int i = 0; i < runtime.Length; i++)
        {
            if (runtime[i].Repr.Kind == Kind.Nat)
            {
                // .NET has no unsigned BigInteger: refuse a negative Nat at the door.
                il.Emit(OpCodes.Ldarg, i);
                il.Emit(OpCodes.Ldstr, runtime[i].ClrName);
                il.Emit(OpCodes.Call, _natCheck);
                il.Emit(OpCodes.Starg, i);
            }
        }
        LocalBuilder result = il.DeclareLocal(e.Result.ClrType);
        Label done = il.BeginExceptionBlock();
        for (int i = 0; i < runtime.Length; i++)
        {
            il.Emit(OpCodes.Ldarg, i);
        }
        il.Emit(OpCodes.Call, e.Impl!);
        il.Emit(OpCodes.Stloc, result);
        il.BeginCatchBlock(_clr.LeanStackOverflow);
        il.Emit(OpCodes.Pop);
        il.Emit(OpCodes.Ldtoken, e.Impl!);
        il.Emit(OpCodes.Ldc_I4, runtime.Length);
        il.Emit(OpCodes.Newarr, _clr.Object);
        for (int i = 0; i < runtime.Length; i++)
        {
            il.Emit(OpCodes.Dup);
            il.Emit(OpCodes.Ldc_I4, i);
            il.Emit(OpCodes.Ldarg, i);
            if (runtime[i].Repr.ClrType.IsValueType)
            {
                il.Emit(OpCodes.Box, runtime[i].Repr.ClrType);
            }
            il.Emit(OpCodes.Stelem_Ref);
        }
        il.Emit(OpCodes.Call, _clr.Static(_clr.LeanStack, "RunDeep", _clr.RuntimeMethodHandle, _clr.Object.MakeArrayType()));
        il.Emit(OpCodes.Unbox_Any, e.Result.ClrType);
        il.Emit(OpCodes.Stloc, result);
        il.EndExceptionBlock();
        il.Emit(OpCodes.Ldloc, result);
        il.Emit(OpCodes.Ret);
    }

    /// <summary>The right-hand side of <c>∀ xs, f xs = rhs</c> at these arguments.</summary>
    private static Expr EquationRhs(Expr equation, List<Expr> args, Name name)
    {
        Expr t = equation;
        foreach (Expr a in args)
        {
            if (t is not PiExpr p)
            {
                throw new CompileError($"internal: the equation lemma of {name} binds fewer variables than {name} takes");
            }
            t = ExprOps.Instantiate1(p.Body, a);
        }
        if (!t.IsAppOfArity(Name.Parse("Eq"), 3))
        {
            throw new CompileError($"internal: the equation lemma of {name} is not an equation");
        }
        t.GetAppArgs(out Expr[] eqArgs);
        return eqArgs[2];
    }

    /// <summary>
    /// For an export over a decimal-shaped structure: the same function taking and returning <c>decimal</c>, and
    /// taking <c>int</c> where the Lean takes a <c>Nat</c>, so it reads like <c>Math.Round(decimal, int, ...)</c>.
    /// It converts with <c>DecimalBridge</c> and calls the exact version.
    /// </summary>
    public void CompileDecimalOverload(Export e)
    {
        if (!e.HasDecimalForm)
        {
            return;
        }
        var runtime = e.Params.Where(p => p.Repr.IsData).ToArray();
        Type Outer(Repr r) => r.Layout?.DecimalShaped == true ? _clr.Decimal : r.Kind == Kind.Nat ? _clr.Int32 : r.ClrType;
        MethodBuilder mb = _class.DefineMethod(e.ClrName, MethodAttributes.Public | MethodAttributes.Static,
            Outer(e.Result), runtime.Select(p => Outer(p.Repr)).ToArray());
        for (int i = 0; i < runtime.Length; i++)
        {
            mb.DefineParameter(i + 1, ParameterAttributes.None, runtime[i].ClrName);
        }
        ILGenerator il = mb.GetILGenerator();
        MethodInfo mant = _clr.Static(_clr.DecimalBridge, "Mantissa", _clr.Decimal);
        MethodInfo scale = _clr.Static(_clr.DecimalBridge, "Scale", _clr.Decimal);
        MethodInfo join = _clr.Static(_clr.DecimalBridge, "FromParts", _clr.BigInteger, _clr.BigInteger);
        MethodInfo fromInt = _clr.Static(_clr.BigInteger, "op_Implicit", _clr.Int32);
        for (int i = 0; i < runtime.Length; i++)
        {
            Repr r = runtime[i].Repr;
            if (r.Layout?.DecimalShaped == true)
            {
                il.Emit(OpCodes.Ldarg, i);
                il.Emit(OpCodes.Call, mant);
                il.Emit(OpCodes.Ldarg, i);
                il.Emit(OpCodes.Call, scale);
                il.Emit(OpCodes.Newobj, r.Layout.Ctor!);
            }
            else if (r.Kind == Kind.Nat)
            {
                il.Emit(OpCodes.Ldarg, i);
                il.Emit(OpCodes.Call, fromInt);
            }
            else
            {
                il.Emit(OpCodes.Ldarg, i);
            }
        }
        il.Emit(OpCodes.Call, e.Raw);
        if (e.Result.Layout?.DecimalShaped == true)
        {
            FieldSlot[] f = e.Result.Layout.RuntimeFields;
            LocalBuilder tmp = il.DeclareLocal(e.Result.ClrType);
            il.Emit(OpCodes.Stloc, tmp);
            il.Emit(OpCodes.Ldloc, tmp);
            il.Emit(OpCodes.Ldfld, f[0].Field!);
            il.Emit(OpCodes.Ldloc, tmp);
            il.Emit(OpCodes.Ldfld, f[1].Field!);
            il.Emit(OpCodes.Call, join);
        }
        il.Emit(OpCodes.Ret);
        e.DecimalOverload = mb;
    }

    /// <summary>
    /// Finish every type, then add <c>ProvenInfo</c>: what Tenet said and which theorems stand behind the assembly,
    /// readable at run time. It is defined last on purpose. <c>PersistedAssemblyBuilder</c> gives the last type in
    /// the table the method and field rows that follow it, so a last type with none (an enum, say) would be handed
    /// someone else's; a last type that has both of its own is always right.
    /// </summary>
    public void Finish(string verdict, string lean, IReadOnlyList<string> theorems)
    {
        string name = _namespace.Length == 0 ? "ProvenInfo" : _namespace + ".ProvenInfo";
        TypeBuilder info = _module.DefineType(name, TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.Class, _clr.Object);
        FieldBuilder v = info.DefineField("Verdict", _clr.String, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault);
        v.SetConstant(verdict);
        FieldBuilder l = info.DefineField("LeanVersion", _clr.String, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault);
        l.SetConstant(lean);
        MethodBuilder m = info.DefineMethod("Theorems", MethodAttributes.Public | MethodAttributes.Static, _clr.String.MakeArrayType(), Type.EmptyTypes);
        ILGenerator il = m.GetILGenerator();
        il.Emit(OpCodes.Ldc_I4, theorems.Count);
        il.Emit(OpCodes.Newarr, _clr.String);
        for (int i = 0; i < theorems.Count; i++)
        {
            il.Emit(OpCodes.Dup);
            il.Emit(OpCodes.Ldc_I4, i);
            il.Emit(OpCodes.Ldstr, theorems[i]);
            il.Emit(OpCodes.Stelem_Ref);
        }
        il.Emit(OpCodes.Ret);
        foreach (TypeBuilder tb in _structs)
        {
            tb.CreateType();
        }
        foreach (TypeBuilder tb in _nested)
        {
            tb.CreateType();
        }
        _class.CreateType();
        info.CreateType();
    }

    // ------------------------------------------------------------------ one method body

    internal abstract record Slot
    {
        public sealed record Arg(int Index, Repr Repr) : Slot;
        public sealed record Local(LocalBuilder Builder, Repr Repr) : Slot;
        public sealed record Unavailable(string Why) : Slot;
        public sealed record ErasedSlot : Slot;
        public static class Erased
        {
            public static readonly ErasedSlot Instance = new();
        }
    }

    internal sealed class Body
    {
        private readonly Compiler _c;
        private readonly Dictionary<FVarId, Slot> _slots = new();
        private int _unfolds;
        private const int UnfoldLimit = 200_000;

        private readonly ILGenerator? _il;
        public ILGenerator Il => _il ?? throw new InvalidOperationException("a reducer emits no code");
        public TypeChecker Tc { get; }

        /// <summary>The function being compiled, so a call to it in tail position can become a jump.</summary>
        public Export? Self { get; init; }
        private Label? _loopStart;

        public void MarkLoopStart()
        {
            _loopStart = Il.DefineLabel();
            Il.MarkLabel(_loopStart.Value);
        }

        public Body(Compiler c, ILGenerator? il)
        {
            _c = c;
            _il = il;
            Tc = new TypeChecker(c._env, new LocalContext());
        }

        public void Bind(Expr fvar, Slot s) => _slots[((FVarExpr)fvar).Id] = s;

        private Expr Fresh(Name n, Expr type, Slot s)
        {
            Expr fv = Tc.Lctx.MkLocalDecl(n, type);
            Bind(fv, s);
            return fv;
        }

        /// <summary>Check a value's form against the form expected, and fail loudly on a mismatch.</summary>
        public void Coerce(Repr have, Repr want)
        {
            bool same = have.Kind == want.Kind && (have.Kind is not (Kind.Enum or Kind.Struct) || have.Layout == want.Layout)
                && (have.Kind is not Kind.Fixed || have.Clr == want.Clr);
            bool bothBig = have.Kind is Kind.Nat or Kind.Int && want.Kind is Kind.Nat or Kind.Int;
            if (!same && !bothBig)
            {
                throw new CompileError($"internal: produced a {have.Kind} where a {want.Kind} was expected");
            }
        }

        // -------------------------------------------------------------- reduction

        /// <summary>
        /// Beta-reduce the head. <c>(fun x => b) a</c> becomes <c>let x := a; b</c> when <c>a</c> is data and <c>b</c>
        /// uses <c>x</c> more than once, so it is computed once; otherwise <c>a</c> is substituted. Substituting is what
        /// lets an instance, a proof or a numeral be seen through at compile time, and it keeps a branch that uses
        /// its argument once as lazy as the source: the two arms of an <c>if</c> are never both computed.
        /// </summary>
        private Expr HeadBeta(Expr e)
        {
            while (true)
            {
                Expr f = e.GetAppArgs(out Expr[] args);
                if (f is not LamExpr lam || args.Length == 0)
                {
                    return e;
                }
                Expr a = args[0];
                Expr[] rest = args.AsSpan(1).ToArray();
                if (IsCheap(a) || CountBVar(lam.Body, 0) <= 1 || !IsData(lam.Domain))
                {
                    e = Expr.MkApp(ExprOps.Instantiate1(lam.Body, a), rest);
                    continue;
                }
                return Expr.Let(lam.BinderName, lam.Domain, a, Expr.MkApp(lam.Body, rest.Select(r => ExprOps.LiftLooseBVars(r, 1)).ToArray()));
            }
        }

        private static bool IsCheap(Expr a) => a is FVarExpr or LitExpr or ConstExpr or SortExpr;

        private static int CountBVar(Expr body, int idx)
        {
            int n = 0;
            ExprOps.ForEach(body, (x, offset) =>
            {
                if (x is BVarExpr b && b.Idx == idx + offset)
                {
                    n++;
                }
                return x.LooseBVarRange > idx + offset;
            });
            return n;
        }

        private bool IsData(Expr type)
        {
            if (type.HasLooseBVars)
            {
                return false;
            }
            try
            {
                return _c.ReprOf(type, Tc).IsData;
            }
            catch (KernelException)
            {
                return false;
            }
        }

        /// <summary>
        /// The constants Lean's equation compiler leaves in a recursive definition's kernel term: <c>brecOn</c> for
        /// structural recursion, <c>WellFounded.fix</c> for well-founded recursion. Seeing one is the honest
        /// moment to stop, before the unfolding reaches the <c>PProd</c> tables they are built from.
        /// </summary>
        private static string? RecursionMarker(Name n)
        {
            string s = n.ToString();
            if (s.EndsWith(".brecOn", StringComparison.Ordinal) || s.EndsWith(".binductionOn", StringComparison.Ordinal))
            {
                return "structural recursion (" + s + ")";
            }
            if (s is "WellFounded.fix" or "WellFounded.fixF" || s.EndsWith("._unary", StringComparison.Ordinal))
            {
                return "well-founded recursion (" + s + ")";
            }
            return null;
        }

        private bool IsCtorApp(Expr e, out ConstructorInfo? ctor, out Expr[] args)
        {
            Expr f = e.GetAppArgs(out args);
            ctor = f is ConstExpr c ? _c.Resolve(c.Name) as ConstructorInfo : null;
            return ctor is not null && args.Length == ctor.NumParams + ctor.NumFields;
        }

        /// <summary>A Nat literal as the constructor application a recursor can reduce: <c>3</c> as <c>Nat.succ 2</c>.</summary>
        private static Expr NatLitAsCtor(Expr e) =>
            e is LitExpr { Value: NatLiteral n }
                ? n.Value.IsZero ? Expr.Const(Name.Parse("Nat.zero"), []) : Expr.App(Expr.Const(Name.Parse("Nat.succ"), []), Expr.NatLit(n.Value - 1))
                : e;

        /// <summary>Unfold and reduce at the head until a primitive, a constructor, an export, a stuck recursor or a variable is on top.</summary>
        public Expr Reduce(Expr e)
        {
            while (true)
            {
                e = HeadBeta(e);
                Expr head = e.GetAppArgs(out Expr[] args);
                if (head is LetExpr l && args.Length > 0)
                {
                    return Expr.Let(l.Name, l.Type, l.Value, Expr.MkApp(l.Body, args.Select(a => ExprOps.LiftLooseBVars(a, 1)).ToArray()), l.NonDep);
                }
                if (head is ProjExpr p)
                {
                    Expr s = Reduce(p.Struct);
                    if (IsCtorApp(s, out ConstructorInfo? ci, out Expr[] cargs))
                    {
                        e = Expr.MkApp(cargs[ci!.NumParams + p.Idx], args);
                        continue;
                    }
                    return ReferenceEquals(s, p.Struct) ? e : Expr.MkApp(Expr.Proj(p.StructName, p.Idx, s), args);
                }
                if (head is not ConstExpr c || _c._prims.ContainsKey(c.Name) || ArrayOps.Contains(c.Name.ToString()) || _c._exports.ContainsKey(c.Name) || _c.IsRecursive(c.Name))
                {
                    return e;
                }
                if (_c._replacements.TryGetValue(c.Name, out var rep))
                {
                    e = Expr.MkApp(ExprOps.InstantiateLevelParams(rep.Rhs, rep.Levels, c.Levels), args);
                    continue;
                }
                ConstantInfo? info = _c.Resolve(c.Name);
                if (info is DefinitionInfo d)
                {
                    if (RecursionMarker(c.Name) is string how)
                    {
                        throw new CompileError($"it is defined by {how}, which lean2il does not compile yet");
                    }
                    if (d.Safety != DefinitionSafety.Safe)
                    {
                        throw new CompileError($"{c.Name} is partial or unsafe; lean2il compiles only what the kernel checked");
                    }
                    if (++_unfolds > UnfoldLimit)
                    {
                        throw new CompileError($"unfolding does not stop at {c.Name}; lean2il does not compile recursive definitions yet");
                    }
                    e = Expr.MkApp(d.InstantiateValueLevelParams(c.Levels), args);
                    continue;
                }
                if (info is RecursorInfo ri && args.Length > ri.MajorIdx)
                {
                    Expr major = NatLitAsCtor(Reduce(args[ri.MajorIdx]));
                    if (IsCtorApp(major, out ConstructorInfo? mc, out Expr[] margs) && mc!.Induct.Equals(ri.GetMajorInduct()))
                    {
                        RecursorRule rule = ri.Rules[mc.Cidx];
                        Expr rhs = ExprOps.InstantiateLevelParams(rule.Rhs, ri.LevelParams, c.Levels);
                        rhs = Expr.MkApp(rhs, args.AsSpan(0, ri.NumParams + ri.NumMotives + ri.NumMinors).ToArray());
                        rhs = Expr.MkApp(rhs, margs.AsSpan(mc.NumParams).ToArray());
                        e = Expr.MkApp(rhs, args.AsSpan(ri.MajorIdx + 1).ToArray());
                        continue;
                    }
                }
                return e;
            }
        }

        // -------------------------------------------------------------- emission

        public Repr Emit(Expr e, bool tail = false)
        {
            e = Reduce(e);
            switch (e)
            {
                case FVarExpr f:
                    return Load(f);
                case LitExpr { Value: NatLiteral n }:
                    PushBig(n.Value);
                    return new Repr(Kind.Nat, _c._clr.BigInteger);
                case LitExpr { Value: StrLiteral str }:
                    Il.Emit(OpCodes.Ldstr, str.Value);
                    return new Repr(Kind.String, _c._clr.String);
                case LetExpr l:
                    return EmitLet(l, tail);
                case ProjExpr p:
                    return EmitProj(p);
                case LamExpr:
                    throw new CompileError("a function value would be needed at run time; apply it, or export it on its own");
                case SortExpr or PiExpr:
                    throw new CompileError("internal: a type reached code generation");
            }
            Expr head = e.GetAppArgs(out Expr[] args);
            if (head is FVarExpr hv)
            {
                throw new CompileError($"calling the local function {Tc.Lctx.Find(hv)?.UserName} is not compiled yet");
            }
            if (head is not ConstExpr c)
            {
                throw new CompileError($"cannot compile {e}");
            }
            if (ArrayOps.Contains(c.Name.ToString()))
            {
                return EmitArrayOp(c, args);
            }
            if (_c._prims.TryGetValue(c.Name, out Primitive? prim))
            {
                int arity = prim.Args.Max() + 1;
                if (args.Length != arity)
                {
                    throw new CompileError($"{c.Name} applied to {args.Length} arguments, expected {arity}");
                }
                if (prim.Result == Kind.Fixed && c.Name.ToString().EndsWith(".ofNat", StringComparison.Ordinal)
                    && Reduce(args[0]) is LitExpr { Value: NatLiteral lit })
                {
                    // A numeral: wrap it now, as ofNat would, and load the constant.
                    PushFixed(FixedWidth.OfClr(prim.ResultClr!), lit.Value);
                    return new Repr(Kind.Fixed, prim.ResultClr);
                }
                foreach (int i in prim.Args)
                {
                    Emit(args[i]);
                }
                prim.Emit(Il);
                return prim.Result switch
                {
                    Kind.Bool => new Repr(Kind.Bool, _c._clr.Bool),
                    Kind.String => new Repr(Kind.String, _c._clr.String),
                    Kind.Fixed => new Repr(Kind.Fixed, prim.ResultClr),
                    _ => new Repr(prim.Result, _c._clr.BigInteger),
                };
            }
            if (_c._exports.TryGetValue(c.Name, out Export? ex))
            {
                return EmitCall(ex, args, tail);
            }
            if (_c.IsRecursive(c.Name))
            {
                var (fn, captured) = _c.Helper(c, args, Tc);
                return EmitCall(fn, args, tail, captured);
            }
            return _c.Resolve(c.Name) switch
            {
                ConstructorInfo ci => EmitCtor(ci, args, e),
                RecursorInfo ri => EmitRec(ri, args, e, tail),
                TheoremInfo => throw new CompileError($"the theorem {c.Name} is used as data"),
                AxiomInfo => throw new CompileError($"the axiom {c.Name} has no computational content"),
                OpaqueInfo => throw new CompileError($"{c.Name} is opaque; its value cannot be compiled"),
                QuotInfo => throw new CompileError($"quotients ({c.Name}) are not compiled yet"),
                null => throw new CompileError($"unknown constant {c.Name}"),
                var other => throw new CompileError($"cannot compile {other.KindName} {c.Name}"),
            };
        }

        private Repr Load(FVarExpr f)
        {
            if (!_slots.TryGetValue(f.Id, out Slot? s))
            {
                throw new CompileError("internal: unbound variable");
            }
            switch (s)
            {
                case Slot.Arg a:
                    Il.Emit(OpCodes.Ldarg, a.Index);
                    return a.Repr;
                case Slot.Local l:
                    Il.Emit(OpCodes.Ldloc, l.Builder);
                    return l.Repr;
                case Slot.Unavailable u:
                    throw new CompileError(u.Why);
                default:
                    throw new CompileError($"internal: {Tc.Lctx.Find(f)?.UserName} is a type or a proof but is used as data");
            }
        }

        private void PushBig(BigInteger v)
        {
            if (v >= long.MinValue && v <= long.MaxValue)
            {
                Il.Emit(OpCodes.Ldc_I8, (long)v);
                Il.Emit(OpCodes.Call, _c._bigFromLong);
            }
            else
            {
                Il.Emit(OpCodes.Ldstr, v.ToString(System.Globalization.CultureInfo.InvariantCulture));
                Il.Emit(OpCodes.Call, _c._bigParse);
            }
        }

        private void PushFixed(FixedWidth f, BigInteger n)
        {
            BigInteger low = f.Wrap(n);
            if (f.Bits == 64)
            {
                Il.Emit(OpCodes.Ldc_I8, f.Signed ? (long)low : unchecked((long)(ulong)low));
            }
            else
            {
                Il.Emit(OpCodes.Ldc_I4, f.Signed ? (int)low : unchecked((int)(uint)low));
            }
        }

        private Repr EmitLet(LetExpr l, bool tail)
        {
            Repr r = _c.ReprOf(l.Type, Tc);
            if (!r.IsData)
            {
                return Emit(ExprOps.Instantiate1(l.Body, l.Value), tail);
            }
            Repr vr = Emit(l.Value);
            Coerce(vr, r);
            LocalBuilder lb = Il.DeclareLocal(r.ClrType);
            Il.Emit(OpCodes.Stloc, lb);
            Expr fv = Tc.Lctx.MkLetDecl(l.Name, l.Type, l.Value);
            Bind(fv, new Slot.Local(lb, r));
            return Emit(ExprOps.Instantiate1(l.Body, fv), tail);
        }

        private Repr EmitProj(ProjExpr p)
        {
            if (p.StructName.ToString() is "Fin" or "Subtype" && p.Idx == 0)
            {
                return Emit(p.Struct);
            }
            if (p.StructName.ToString() == "Array")
            {
                Repr list = _c.ReprOf(Tc.Infer(p), Tc);
                Emit(p.Struct);
                Il.Emit(OpCodes.Callvirt, _c._clr.ILeanArray.GetMethod("ToList")!);
                Il.Emit(OpCodes.Castclass, list.ClrType);
                return list;
            }
            Layout l = LayoutOfValue(p.Struct, $"the structure {p.StructName}");
            FieldSlot f = l.Fields[p.Idx];
            if (f.Field is null)
            {
                throw new CompileError($"internal: field {f.Name} is erased but used as data");
            }
            Emit(p.Struct);
            Il.Emit(OpCodes.Ldfld, f.Field);
            return f.Repr;
        }

        private Repr EmitCall(Export ex, Expr[] args, bool tail, Expr[]? captured = null)
        {
            if (args.Length != ex.Params.Count)
            {
                throw new CompileError($"{ex.Name} is applied to {args.Length} arguments but takes {ex.Params.Count}; partial application is not compiled yet");
            }
            int n = 0;
            for (int i = 0; i < args.Length; i++)
            {
                if (ex.Params[i].Repr.IsData)
                {
                    Coerce(Emit(args[i]), ex.Params[i].Repr);
                    n++;
                }
            }
            for (int i = 0; i < (captured?.Length ?? 0); i++)
            {
                if (ex.Captures[i].Repr.IsData)
                {
                    Coerce(Emit(captured![i]), ex.Captures[i].Repr);
                    n++;
                }
            }
            if (tail && ReferenceEquals(ex, Self) && _loopStart is Label start)
            {
                // A call to itself in tail position: store the new arguments over the old ones and jump back. Every
                // argument was computed before any is stored, so none sees another's new value. gcd, loops and
                // accumulators run in constant stack.
                for (int k = n - 1; k >= 0; k--)
                {
                    Il.Emit(OpCodes.Starg, k);
                }
                Il.Emit(OpCodes.Br, start);
                return ex.Result;
            }
            Il.Emit(OpCodes.Call, ex.Target);
            return ex.Result;
        }

        private Repr EmitCtor(ConstructorInfo ci, Expr[] args, Expr whole)
        {
            if (args.Length != ci.NumParams + ci.NumFields)
            {
                throw new CompileError($"{ci.Name} is applied to {args.Length} arguments; partial application is not compiled yet");
            }
            switch (ci.Name.ToString())
            {
                case "Nat.zero":
                    Il.Emit(OpCodes.Call, _c._bigZero);
                    return new Repr(Kind.Nat, _c._clr.BigInteger);
                case "Bool.false" or "Decidable.isFalse":
                    Il.Emit(OpCodes.Ldc_I4_0);
                    return new Repr(Kind.Bool, _c._clr.Bool);
                case "Bool.true" or "Decidable.isTrue":
                    Il.Emit(OpCodes.Ldc_I4_1);
                    return new Repr(Kind.Bool, _c._clr.Bool);
                case "List.nil" or "List.cons" or "Option.none" or "Option.some":
                {
                    Repr r = _c.ReprOf(Tc.Infer(whole), Tc);
                    if (!r.IsData)
                    {
                        throw new CompileError(r.Why ?? $"no run-time form for {whole}");
                    }
                    Type t = r.ClrType;
                    Type el = r.Elem!.ClrType;
                    switch (ci.Name.ToString())
                    {
                        case "List.nil":
                        case "Option.none":
                            Il.Emit(OpCodes.Ldtoken, t);
                            Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanOps, ci.Name.ToString() == "List.nil" ? "Nil" : "None", _c._clr.RuntimeTypeHandle));
                            break;
                        case "List.cons":
                            Coerce(Emit(args[2]), r);
                            Coerce(Emit(args[1]), r.Elem!);
                            BoxIfValue(el);
                            Il.Emit(OpCodes.Callvirt, _c._clr.ILeanList.GetMethod("Prepend")!);
                            break;
                        default:
                            Il.Emit(OpCodes.Ldtoken, t);
                            Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanOps, "None", _c._clr.RuntimeTypeHandle));
                            Il.Emit(OpCodes.Castclass, _c._clr.ILeanOption);
                            Coerce(Emit(args[1]), r.Elem!);
                            BoxIfValue(el);
                            Il.Emit(OpCodes.Callvirt, _c._clr.ILeanOption.GetMethod("Some")!);
                            break;
                    }
                    Il.Emit(OpCodes.Castclass, t);
                    return r;
                }
            }
            if (ci.Name.ToString() is "Fin.mk" or "Subtype.mk")
            {
                return Emit(args[ci.NumParams]);
            }
            if (ci.Name.ToString() == "Array.mk")
            {
                Repr ar = _c.ReprOf(Tc.Infer(whole), Tc);
                if (!ar.IsData)
                {
                    throw new CompileError(ar.Why ?? $"no run-time form for {whole}");
                }
                Emit(args[1]);
                Il.Emit(OpCodes.Ldtoken, ar.ClrType);
                Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanOps, "ArrayOf", _c._clr.ILeanList, _c._clr.RuntimeTypeHandle));
                Il.Emit(OpCodes.Castclass, ar.ClrType);
                return ar;
            }
            Layout l = LayoutOfValue(whole, $"the type {ci.Induct}");
            if (l.Kind == Kind.Enum)
            {
                Il.Emit(OpCodes.Ldc_I4, ci.Cidx);
                return new Repr(Kind.Enum, l.Builder, l);
            }
            if (l.Kind == Kind.Union)
            {
                Variant v = l.Variants[ci.Cidx];
                for (int i = 0; i < ci.NumFields; i++)
                {
                    FieldSlot f = v.Fields[i];
                    if (f.Field is not null)
                    {
                        Coerce(Emit(args[ci.NumParams + i]), f.Repr);
                    }
                }
                Il.Emit(OpCodes.Newobj, v.Constructor);
                return new Repr(Kind.Union, l.Builder, l);
            }
            for (int i = 0; i < ci.NumFields; i++)
            {
                FieldSlot f = l.Fields[i];
                if (f.Field is not null)
                {
                    Coerce(Emit(args[ci.NumParams + i]), f.Repr);
                }
            }
            Il.Emit(OpCodes.Newobj, l.Ctor!);
            return new Repr(Kind.Struct, l.Builder, l);
        }

        /// <summary>A recursor whose target is only known at run time: a branch per constructor.</summary>
        private Repr EmitRec(RecursorInfo ri, Expr[] args, Expr whole, bool tail)
        {
            if (args.Length <= ri.MajorIdx)
            {
                throw new CompileError($"{ri.Name} is not applied to its target; partial application is not compiled yet");
            }
            if (ri.NumMotives != 1)
            {
                throw new CompileError($"{ri.Name} belongs to a mutual inductive, which is not compiled yet");
            }
            Expr major = args[ri.MajorIdx];
            Expr[] extra = args.AsSpan(ri.MajorIdx + 1).ToArray();
            Expr[] minors = args.AsSpan(ri.NumParams + ri.NumMotives, ri.NumMinors).ToArray();
            Name indName = ri.GetMajorInduct();
            var ind = (InductiveInfo)_c.Resolve(indName)!;

            // Eliminating a proof: Eq.rec, And.rec, True.rec. The one branch runs with its fields erased; with no
            // branch (False.rec) the code is unreachable.
            if (Tc.IsProp(Tc.Infer(major)))
            {
                if (ind.Ctors.Length == 1)
                {
                    return EmitMinor(minors[0], [], extra, erasedFields: ((ConstructorInfo)_c.Resolve(ind.Ctors[0])!).NumFields, tail: tail);
                }
                Repr rr = _c.ReprOf(Tc.Infer(whole), Tc);
                Throw("System.InvalidOperationException", "unreachable: a proof of an empty proposition");
                return rr;
            }
            switch (indName.ToString())
            {
                case "Bool":
                case "Decidable":
                {
                    int fields = indName.ToString() == "Decidable" ? 1 : 0;
                    Emit(major);
                    return Branch2(
                        () => EmitMinor(minors[1], [], extra, erasedFields: fields, tail: tail),
                        () => EmitMinor(minors[0], [], extra, erasedFields: fields, tail: tail));
                }
                case "Nat":
                {
                    LocalBuilder m = Spill(major, _c._clr.BigInteger);
                    Il.Emit(OpCodes.Ldloca, m);
                    Il.Emit(OpCodes.Call, _c._clr.BigInteger.GetProperty("IsZero")!.GetGetMethod()!);
                    return Branch2(
                        () => EmitMinor(minors[0], [], extra, tail: tail),
                        () =>
                        {
                            Il.Emit(OpCodes.Ldloc, m);
                            Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanNat, "Pred", _c._clr.BigInteger));
                            LocalBuilder pred = Il.DeclareLocal(_c._clr.BigInteger);
                            Il.Emit(OpCodes.Stloc, pred);
                            return EmitMinor(minors[1], [new Slot.Local(pred, new Repr(Kind.Nat, _c._clr.BigInteger)),
                                new Slot.Unavailable("this uses the recursor's induction hypothesis directly; write the recursion as a recursive definition instead")], extra, tail: tail);
                        });
                }
                case "Fin":
                case "Subtype":
                {
                    Repr val = _c.ReprOf(Tc.Infer(Expr.Proj(indName, 0, major)), Tc);
                    LocalBuilder v = Spill(major, val.ClrType);
                    return EmitMinor(minors[0], [new Slot.Local(v, val)], extra, erasedFields: 2, tail: tail);
                }
                case "Array":
                {
                    Repr list = _c.ReprOf(Tc.Infer(Expr.Proj(Name.Parse("Array"), 0, major)), Tc);
                    Emit(major);
                    Il.Emit(OpCodes.Callvirt, _c._clr.ILeanArray.GetMethod("ToList")!);
                    Il.Emit(OpCodes.Castclass, list.ClrType);
                    LocalBuilder items = Il.DeclareLocal(list.ClrType);
                    Il.Emit(OpCodes.Stloc, items);
                    return EmitMinor(minors[0], [new Slot.Local(items, list)], extra, tail: tail);
                }
                case "List":
                case "Option":
                {
                    Repr r = _c.ReprOf(Tc.Infer(major), Tc);
                    if (!r.IsData)
                    {
                        throw new CompileError(r.Why ?? $"no run-time form for {major}");
                    }
                    Type t = r.ClrType;
                    bool isList = r.Kind == Kind.List;
                    LocalBuilder cell = Spill(major, t);
                    Type el = r.Elem!.ClrType;
                    Type iface = isList ? _c._clr.ILeanList : _c._clr.ILeanOption;
                    Il.Emit(OpCodes.Ldloc, cell);
                    Il.Emit(OpCodes.Callvirt, _c._clr.Getter(iface, isList ? "IsNil" : "IsSome"));
                    Func<Repr> empty = () => EmitMinor(minors[0], [], extra, tail: tail);
                    Func<Repr> full = () =>
                    {
                        Il.Emit(OpCodes.Ldloc, cell);
                        Il.Emit(OpCodes.Callvirt, _c._clr.Getter(iface, isList ? "HeadObject" : "ValueObject"));
                        Il.Emit(OpCodes.Unbox_Any, el);
                        LocalBuilder head = Il.DeclareLocal(r.Elem!.ClrType);
                        Il.Emit(OpCodes.Stloc, head);
                        if (!isList)
                        {
                            return EmitMinor(minors[1], [new Slot.Local(head, r.Elem)], extra, tail: tail);
                        }
                        Il.Emit(OpCodes.Ldloc, cell);
                        Il.Emit(OpCodes.Callvirt, _c._clr.Getter(iface, "TailObject"));
                        Il.Emit(OpCodes.Castclass, t);
                        LocalBuilder rest = Il.DeclareLocal(t);
                        Il.Emit(OpCodes.Stloc, rest);
                        return EmitMinor(minors[1], [new Slot.Local(head, r.Elem), new Slot.Local(rest, r),
                            new Slot.Unavailable("this uses the recursor's induction hypothesis directly; write the recursion as a recursive definition instead")], extra, tail: tail);
                    };
                    // IsNil true -> the nil branch; IsSome true -> the some branch.
                    return isList ? Branch2(empty, full) : Branch2(full, empty);
                }
                case "Int":
                {
                    LocalBuilder m = Spill(major, _c._clr.BigInteger);
                    Il.Emit(OpCodes.Ldloca, m);
                    Il.Emit(OpCodes.Call, _c._clr.BigInteger.GetProperty("Sign")!.GetGetMethod()!);
                    Il.Emit(OpCodes.Ldc_I4_0);
                    Il.Emit(OpCodes.Clt);  // sign < 0: negSucc
                    return Branch2(
                        () =>
                        {
                            Il.Emit(OpCodes.Ldloc, m);
                            Il.Emit(OpCodes.Call, _c._clr.Big1("op_UnaryNegation"));
                            Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanNat, "Pred", _c._clr.BigInteger));
                            LocalBuilder n = Il.DeclareLocal(_c._clr.BigInteger);
                            Il.Emit(OpCodes.Stloc, n);
                            return EmitMinor(minors[1], [new Slot.Local(n, new Repr(Kind.Nat, _c._clr.BigInteger))], extra, tail: tail);
                        },
                        () => EmitMinor(minors[0], [new Slot.Local(m, new Repr(Kind.Nat, _c._clr.BigInteger))], extra, tail: tail));
                }
            }
            Layout l = LayoutOfValue(major, $"matching on {indName}");
            if (l.Kind == Kind.Union)
            {
                // Read the tag, then take the value apart as the constructor's class.
                LocalBuilder u = Spill(major, l.Builder);
                Il.Emit(OpCodes.Ldloc, u);
                Il.Emit(OpCodes.Ldfld, l.TagField!);
                Label[] cases = l.Variants.Select(_ => Il.DefineLabel()).ToArray();
                Label done = Il.DefineLabel();
                Il.Emit(OpCodes.Switch, cases);
                Throw("System.ArgumentException", $"not a {l.ClrName}");
                Repr? res = null;
                for (int i = 0; i < cases.Length; i++)
                {
                    Il.MarkLabel(cases[i]);
                    Variant v = l.Variants[i];
                    Il.Emit(OpCodes.Ldloc, u);
                    Il.Emit(OpCodes.Castclass, v.Type);
                    LocalBuilder cell = Il.DeclareLocal(v.Type);
                    Il.Emit(OpCodes.Stloc, cell);
                    var fslots = FieldSlots(cell, v.Fields);
                    for (int k = 0; k < v.SelfFields; k++)
                    {
                        fslots.Add(new Slot.Unavailable("this uses the recursor's induction hypothesis directly; write the recursion as a recursive definition instead"));
                    }
                    Repr r = EmitMinor(minors[i], fslots, extra, tail: tail);
                    if (res is not null)
                    {
                        Coerce(r, res);
                    }
                    res ??= r;
                    Il.Emit(OpCodes.Br, done);
                }
                Il.MarkLabel(done);
                return res!;
            }
            if (l.Kind == Kind.Enum)
            {
                Emit(major);
                Label[] labels = l.Cases.Select(_ => Il.DefineLabel()).ToArray();
                Label end = Il.DefineLabel();
                Il.Emit(OpCodes.Switch, labels);
                Throw("System.ArgumentException", $"not a defined {l.ClrName} value");
                Repr? result = null;
                for (int i = 0; i < labels.Length; i++)
                {
                    Il.MarkLabel(labels[i]);
                    Repr r = EmitMinor(minors[i], [], extra, tail: tail);
                    if (result is not null)
                    {
                        Coerce(r, result);
                    }
                    result ??= r;
                    Il.Emit(OpCodes.Br, end);
                }
                Il.MarkLabel(end);
                return result!;
            }
            // A structure: take it apart once, and bind each field the branch uses.
            LocalBuilder obj = Spill(major, l.Builder);
            var slots = FieldSlots(obj, l.Fields);
            for (int k = 0; k < l.SelfFields; k++)
            {
                slots.Add(new Slot.Unavailable("this uses the recursor's induction hypothesis directly; write the recursion as a recursive definition instead"));
            }
            return EmitMinor(minors[0], slots, extra, tail: tail);
        }

        private List<Slot> FieldSlots(LocalBuilder obj, List<FieldSlot> fields)
        {
            var slots = new List<Slot>();
            foreach (FieldSlot f in fields)
            {
                if (f.Field is null)
                {
                    slots.Add(Slot.Erased.Instance);
                    continue;
                }
                Il.Emit(OpCodes.Ldloc, obj);
                Il.Emit(OpCodes.Ldfld, f.Field);
                LocalBuilder lb = Il.DeclareLocal(f.Repr.ClrType);
                Il.Emit(OpCodes.Stloc, lb);
                slots.Add(new Slot.Local(lb, f.Repr));
            }
            return slots;
        }

        /// <summary>The layout of the type of <paramref name="value"/>, or an error naming what could not be compiled.</summary>
        private Layout LayoutOfValue(Expr value, string what)
        {
            Repr r = _c.ReprOf(Tc.Infer(value), Tc);
            return r.Layout ?? throw new CompileError($"{what} is not compiled: {r.Why ?? "it has no run-time form"}");
        }

        private void Throw(string exceptionType, string message)
        {
            Type t = _c._clr.CoreAssembly.GetType(exceptionType, throwOnError: true)!;
            Il.Emit(OpCodes.Ldstr, message);
            Il.Emit(OpCodes.Newobj, t.GetConstructor([_c._clr.String])!);
            Il.Emit(OpCodes.Throw);
        }

        /// <summary>
        /// The <c>Array</c> operations Lean's runtime implements natively and the kernel defines through
        /// <c>toList</c>: compiled to the array's own constant-time operations instead of a walk down a list.
        /// </summary>
        internal static readonly HashSet<string> ArrayOps =
            ["Array.size", "Array.getInternal", "Array.get!Internal", "Array.push", "Array.set", "Array.setIfInBounds"];

        private Repr EmitArrayOp(ConstExpr c, Expr[] args)
        {
            string op = c.Name.ToString();
            int arrayArg = op == "Array.get!Internal" ? 2 : 1;
            int arity = op switch { "Array.size" => 2, "Array.push" or "Array.setIfInBounds" => op == "Array.push" ? 3 : 4, "Array.set" => 5, _ => 4 };
            if (args.Length != arity)
            {
                throw new CompileError($"{op} is applied to {args.Length} arguments; partial application is not compiled yet");
            }
            Repr ar = _c.ReprOf(Tc.Infer(args[arrayArg]), Tc);
            if (!ar.IsData)
            {
                throw new CompileError(ar.Why ?? $"no run-time form for {args[arrayArg]}");
            }
            Repr el = ar.Elem!;
            Type ia = _c._clr.ILeanArray;
            var nat = new Repr(Kind.Nat, _c._clr.BigInteger);
            Coerce(Emit(args[arrayArg]), ar);
            switch (op)
            {
                case "Array.size":
                    Il.Emit(OpCodes.Callvirt, _c._clr.Getter(ia, "Size"));
                    return nat;
                case "Array.getInternal":
                    Coerce(Emit(args[2]), nat);
                    Il.Emit(OpCodes.Callvirt, ia.GetMethod("Get")!);
                    Il.Emit(OpCodes.Unbox_Any, el.ClrType);
                    return el;
                case "Array.get!Internal":
                {
                    // a[i]! is a[i] in range and the type's default value out of it, as Lean's getD makes it.
                    LocalBuilder a = Il.DeclareLocal(ar.ClrType);
                    Il.Emit(OpCodes.Stloc, a);
                    Coerce(Emit(args[3]), nat);
                    LocalBuilder i = Il.DeclareLocal(_c._clr.BigInteger);
                    Il.Emit(OpCodes.Stloc, i);
                    Il.Emit(OpCodes.Ldloc, a);
                    Il.Emit(OpCodes.Ldloc, i);
                    Il.Emit(OpCodes.Callvirt, ia.GetMethod("InBounds")!);
                    return Branch2(
                        () =>
                        {
                            Il.Emit(OpCodes.Ldloc, a);
                            Il.Emit(OpCodes.Ldloc, i);
                            Il.Emit(OpCodes.Callvirt, ia.GetMethod("Get")!);
                            Il.Emit(OpCodes.Unbox_Any, el.ClrType);
                            return el;
                        },
                        () =>
                        {
                            Repr d = Emit(Expr.MkApp(Expr.Const(Name.Parse("Inhabited.default"), c.Levels), args[0], args[1]));
                            Coerce(d, el);
                            return el;
                        });
                }
                case "Array.push":
                    Coerce(Emit(args[2]), el);
                    BoxIfValue(el.ClrType);
                    Il.Emit(OpCodes.Callvirt, ia.GetMethod("Push")!);
                    break;
                default:
                    Coerce(Emit(args[2]), nat);
                    Coerce(Emit(args[3]), el);
                    BoxIfValue(el.ClrType);
                    Il.Emit(OpCodes.Callvirt, ia.GetMethod(op == "Array.set" ? "Set" : "SetIfInBounds")!);
                    break;
            }
            Il.Emit(OpCodes.Castclass, ar.ClrType);
            return ar;
        }

        private void BoxIfValue(Type t)
        {
            if (t.IsValueType)
            {
                Il.Emit(OpCodes.Box, t);
            }
        }

        private LocalBuilder Spill(Expr e, Type t)
        {
            Emit(e);
            LocalBuilder lb = Il.DeclareLocal(t);
            Il.Emit(OpCodes.Stloc, lb);
            return lb;
        }

        /// <summary>With a bool on the stack: the first branch when true, the second when false.</summary>
        private Repr Branch2(Func<Repr> whenTrue, Func<Repr> whenFalse)
        {
            Label no = Il.DefineLabel(), end = Il.DefineLabel();
            Il.Emit(OpCodes.Brfalse, no);
            Repr a = whenTrue();
            Il.Emit(OpCodes.Br, end);
            Il.MarkLabel(no);
            Repr b = whenFalse();
            Coerce(b, a);
            Il.MarkLabel(end);
            return a;
        }

        /// <summary>Apply a recursor's branch to its fields, bound to <paramref name="fieldSlots"/>, then to the extra arguments.</summary>
        private Repr EmitMinor(Expr minor, IReadOnlyList<Slot> fieldSlots, Expr[] extra, int erasedFields = 0, bool tail = false)
        {
            int n = Math.Max(fieldSlots.Count, erasedFields);
            Expr cur = minor;
            var fvs = new List<Expr>();
            for (int i = 0; i < n; i++)
            {
                var pi = Tc.Whnf(Tc.Infer(Expr.MkApp(minor, fvs))) as PiExpr
                    ?? throw new CompileError("internal: a recursor branch takes fewer arguments than its constructor has fields");
                Slot s = i < fieldSlots.Count ? fieldSlots[i] : Slot.Erased.Instance;
                fvs.Add(Fresh(pi.BinderName, pi.Domain, s));
            }
            return Emit(Expr.MkApp(Expr.MkApp(minor, fvs), extra), tail);
        }
    }
}
