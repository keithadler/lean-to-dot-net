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
/// What it does not do yet, and says so rather than miscompiling: recursion (structural or well-founded), function
/// values, and inductive types with parameters, indices or recursive fields.
/// </summary>
internal sealed class Compiler
{
    private readonly OleanChecker _loader;
    private readonly Environment _env;
    private readonly Clr _clr;
    private readonly ModuleBuilder _module;
    private readonly Dictionary<Name, Primitive> _prims;
    private readonly Dictionary<Name, Layout?> _layouts = new();
    private readonly Dictionary<Name, string> _layoutFailures = new();
    private readonly Dictionary<Name, Export> _exports = new();
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

    public Compiler(OleanChecker loader, Environment env, Clr clr, ModuleBuilder module, string ns, string className, HashSet<Name> own)
    {
        _own = own;
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
        var parts = s.Trim('«', '»').Split('_', StringSplitOptions.RemoveEmptyEntries);
        return string.Concat(parts.Select(p => char.ToUpperInvariant(p[0]) + p[1..]));
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
            }
            if (Resolve(c.Name) is InductiveInfo ind)
            {
                Layout? l = LayoutFor(ind);
                if (l is not null)
                {
                    return new Repr(l.Kind, l.Builder, l);
                }
                return new Repr(Kind.Unsupported, Why: $"the type {c.Name} is not compiled: {_layoutFailures.GetValueOrDefault(c.Name, "unsupported shape")}");
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

    /// <summary>The .NET type for an inductive, made the first time it is needed, or null with the reason recorded.</summary>
    private Layout? LayoutFor(InductiveInfo ind)
    {
        if (_layouts.TryGetValue(ind.Name, out Layout? known))
        {
            return known;
        }
        _layouts[ind.Name] = null; // a structure that contains itself finds this and is refused
        string? why =
            !_own.Contains(ind.Name) ? "only types declared in the compiled project become .NET types" :
            ind.NumParams > 0 ? "it has parameters" :
            ind.NumIndices > 0 ? "it has indices" :
            ind.All.Length > 1 ? "it is mutually inductive" :
            ind.IsRec ? "it is recursive" :
            ind.LevelParams.Length > 0 ? "it is universe polymorphic" : null;
        var tc = new TypeChecker(_env);
        if (why is null && tc.Whnf(ind.Type) is SortExpr s && s.Level.NormalizesToZero())
        {
            why = "it is a proposition";
        }
        var ctors = ind.Ctors.Select(n => (ConstructorInfo)Resolve(n)!).ToArray();
        if (why is null && ctors.Length == 0)
        {
            why = "it has no constructors";
        }
        if (why is not null)
        {
            _layoutFailures[ind.Name] = why;
            return null;
        }
        string clrName = ClrTypeName(ind.Name);
        if (ctors.All(c => c.NumFields == 0))
        {
            // Built by hand rather than with DefineEnum, whose base type is the running process's System.Enum and would
            // leave the assembly referring to System.Private.CoreLib.
            TypeBuilder eb = _module.DefineType(clrName, TypeAttributes.Public | TypeAttributes.Sealed, _clr.Enum);
            eb.DefineField("value__", _clr.Int32, FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName);
            var layout = new Layout { Name = ind.Name, Info = ind, Kind = Kind.Enum, Builder = eb, ClrName = clrName };
            for (int i = 0; i < ctors.Length; i++)
            {
                string cn = Pascal(ctors[i].Name.LastString!);
                FieldBuilder lit = eb.DefineField(cn, eb, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault);
                lit.SetConstant(i);
                layout.Cases.Add((ctors[i].Name, cn, lit));
            }
            _layouts[ind.Name] = layout;
            _structs.Add(eb);
            return layout;
        }
        if (ctors.Length != 1)
        {
            _layoutFailures[ind.Name] = "it has more than one constructor and some take arguments";
            return null;
        }
        ConstructorInfo ctor = ctors[0];
        TypeBuilder tb = _module.DefineType(clrName, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.Class, _clr.Object);
        var st = new Layout { Name = ind.Name, Info = ind, Kind = Kind.Struct, Builder = tb, ClrName = clrName };
        Expr t = ctor.Type;
        for (int i = 0; i < ctor.NumFields; i++)
        {
            var p = (PiExpr)tc.Whnf(t);
            Repr r = ReprOf(p.Domain, tc);
            if (r.Kind == Kind.Unsupported)
            {
                _layoutFailures[ind.Name] = $"field {p.BinderName}: {r.Why}";
                return null;
            }
            string fn = Pascal(p.BinderName.LastString ?? $"field{i}");
            FieldBuilder? fb = r.Kind == Kind.Erased ? null : tb.DefineField(fn, r.ClrType, FieldAttributes.Public | FieldAttributes.InitOnly);
            st.Fields.Add(new FieldSlot(Name.Parse(ind.Name + "." + p.BinderName), fn, r, fb));
            t = ExprOps.Instantiate1(p.Body, tc.Lctx.MkLocalDecl(p.BinderName, p.Domain));
        }
        FieldSlot[] rt = st.RuntimeFields;
        ConstructorBuilder cb = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, rt.Select(f => f.Repr.ClrType).ToArray());
        for (int i = 0; i < rt.Length; i++)
        {
            cb.DefineParameter(i + 1, ParameterAttributes.None, char.ToLowerInvariant(rt[i].ClrName[0]) + rt[i].ClrName[1..]);
        }
        ILGenerator il = cb.GetILGenerator();
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Call, _clr.Object.GetConstructor(Type.EmptyTypes)!);
        for (int i = 0; i < rt.Length; i++)
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg, i + 1);
            il.Emit(OpCodes.Stfld, rt[i].Field!);
        }
        il.Emit(OpCodes.Ret);
        st.Ctor = cb;
        _layouts[ind.Name] = st;
        _structs.Add(tb);
        return st;
    }

    private readonly List<TypeBuilder> _structs = new();

    /// <summary>Reduction without code generation, for evaluating closed terms such as the arguments of an example.</summary>
    internal Body NewReducer() => new(this, null);

    /// <summary>The layout already made for an inductive, if it became a .NET type.</summary>
    internal Layout? LayoutOf(Name n) => _layouts.GetValueOrDefault(n);

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
        Expr t = def.Type;
        while (tc.Whnf(t) is PiExpr p)
        {
            Repr r = ReprOf(p.Domain, tc);
            if (r.Kind == Kind.Unsupported)
            {
                throw new CompileError($"{name}, parameter {p.BinderName}: {r.Why}");
            }
            ps.Add(new Param(p.BinderName, p.BinderName.LastString ?? "arg", r));
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
        var e = new Export { Name = name, Info = def, ClrName = MethodName(name), Params = ps, Result = result, Raw = mb };
        _exports[name] = e;
        return e;
    }

    // ------------------------------------------------------------------ bodies

    public void CompileBody(Export e)
    {
        var body = new Body(this, e.Raw.GetILGenerator());
        var tc = body.Tc;
        Expr v = e.Info.Value!;
        Expr t = e.Info.Type;
        var fvars = new List<Expr>();
        int arg = 0;
        foreach (Param p in e.Params)
        {
            var pi = (PiExpr)tc.Whnf(t);
            Expr fv = tc.Lctx.MkLocalDecl(pi.BinderName, pi.Domain, pi.Info);
            fvars.Add(fv);
            t = ExprOps.Instantiate1(pi.Body, fv);
            if (p.Repr.IsData)
            {
                body.Bind(fv, new Slot.Arg(arg, p.Repr));
                if (p.Repr.Kind == Kind.Nat)
                {
                    // .NET has no unsigned BigInteger: refuse a negative Nat at the door.
                    body.Il.Emit(OpCodes.Ldarg, arg);
                    body.Il.Emit(OpCodes.Ldstr, p.ClrName);
                    body.Il.Emit(OpCodes.Call, _natCheck);
                    body.Il.Emit(OpCodes.Starg, arg);
                }
                arg++;
            }
            else
            {
                body.Bind(fv, Slot.Erased.Instance);
            }
        }
        Expr app = Expr.MkApp(v, fvars);
        try
        {
            Repr r = body.Emit(app);
            body.Coerce(r, e.Result);
        }
        catch (CompileError ce)
        {
            throw new CompileError($"{e.Name}: {ce.Message}");
        }
        body.Il.Emit(OpCodes.Ret);
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
            bool same = have.Kind == want.Kind && (have.Kind is not (Kind.Enum or Kind.Struct) || have.Layout == want.Layout);
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
                if (head is not ConstExpr c || _c._prims.ContainsKey(c.Name) || _c._exports.ContainsKey(c.Name))
                {
                    return e;
                }
                ConstantInfo? info = _c.Resolve(c.Name);
                if (info is DefinitionInfo d)
                {
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

        public Repr Emit(Expr e)
        {
            e = Reduce(e);
            switch (e)
            {
                case FVarExpr f:
                    return Load(f);
                case LitExpr { Value: NatLiteral n }:
                    PushBig(n.Value);
                    return new Repr(Kind.Nat, _c._clr.BigInteger);
                case LitExpr:
                    throw new CompileError("string literals are not compiled yet");
                case LetExpr l:
                    return EmitLet(l);
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
            if (_c._prims.TryGetValue(c.Name, out Primitive? prim))
            {
                int arity = prim.Args.Max() + 1;
                if (args.Length != arity)
                {
                    throw new CompileError($"{c.Name} applied to {args.Length} arguments, expected {arity}");
                }
                foreach (int i in prim.Args)
                {
                    Emit(args[i]);
                }
                prim.Emit(Il);
                return prim.Result == Kind.Bool ? new Repr(Kind.Bool, _c._clr.Bool) : new Repr(prim.Result, _c._clr.BigInteger);
            }
            if (_c._exports.TryGetValue(c.Name, out Export? ex))
            {
                return EmitCall(ex, args);
            }
            return _c.Resolve(c.Name) switch
            {
                ConstructorInfo ci => EmitCtor(ci, args, e),
                RecursorInfo ri => EmitRec(ri, args, e),
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

        private Repr EmitLet(LetExpr l)
        {
            Repr r = _c.ReprOf(l.Type, Tc);
            if (!r.IsData)
            {
                return Emit(ExprOps.Instantiate1(l.Body, l.Value));
            }
            Repr vr = Emit(l.Value);
            Coerce(vr, r);
            LocalBuilder lb = Il.DeclareLocal(r.ClrType);
            Il.Emit(OpCodes.Stloc, lb);
            Expr fv = Tc.Lctx.MkLetDecl(l.Name, l.Type, l.Value);
            Bind(fv, new Slot.Local(lb, r));
            return Emit(ExprOps.Instantiate1(l.Body, fv));
        }

        private Repr EmitProj(ProjExpr p)
        {
            var ind = _c.Resolve(p.StructName) as InductiveInfo ?? throw new CompileError($"unknown structure {p.StructName}");
            Layout l = _c.LayoutFor(ind) ?? throw new CompileError($"the structure {p.StructName} is not compiled: {_c._layoutFailures.GetValueOrDefault(p.StructName)}");
            FieldSlot f = l.Fields[p.Idx];
            if (f.Field is null)
            {
                throw new CompileError($"internal: field {f.Name} is erased but used as data");
            }
            Emit(p.Struct);
            Il.Emit(OpCodes.Ldfld, f.Field);
            return f.Repr;
        }

        private Repr EmitCall(Export ex, Expr[] args)
        {
            if (args.Length != ex.Params.Count)
            {
                throw new CompileError($"{ex.Name} is applied to {args.Length} arguments but takes {ex.Params.Count}; partial application is not compiled yet");
            }
            for (int i = 0; i < args.Length; i++)
            {
                if (ex.Params[i].Repr.IsData)
                {
                    Coerce(Emit(args[i]), ex.Params[i].Repr);
                }
            }
            Il.Emit(OpCodes.Call, ex.Raw);
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
            }
            var ind = (InductiveInfo)_c.Resolve(ci.Induct)!;
            Layout l = _c.LayoutFor(ind) ?? throw new CompileError($"the type {ci.Induct} is not compiled: {_c._layoutFailures.GetValueOrDefault(ci.Induct)}");
            if (l.Kind == Kind.Enum)
            {
                Il.Emit(OpCodes.Ldc_I4, ci.Cidx);
                return new Repr(Kind.Enum, l.Builder, l);
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
        private Repr EmitRec(RecursorInfo ri, Expr[] args, Expr whole)
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
                    return EmitMinor(minors[0], [], extra, erasedFields: ((ConstructorInfo)_c.Resolve(ind.Ctors[0])!).NumFields);
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
                        () => EmitMinor(minors[1], [], extra, erasedFields: fields),
                        () => EmitMinor(minors[0], [], extra, erasedFields: fields));
                }
                case "Nat":
                {
                    LocalBuilder m = Spill(major, _c._clr.BigInteger);
                    Il.Emit(OpCodes.Ldloca, m);
                    Il.Emit(OpCodes.Call, _c._clr.BigInteger.GetProperty("IsZero")!.GetGetMethod()!);
                    return Branch2(
                        () => EmitMinor(minors[0], [], extra),
                        () =>
                        {
                            Il.Emit(OpCodes.Ldloc, m);
                            Il.Emit(OpCodes.Call, _c._clr.Static(_c._clr.LeanNat, "Pred", _c._clr.BigInteger));
                            LocalBuilder pred = Il.DeclareLocal(_c._clr.BigInteger);
                            Il.Emit(OpCodes.Stloc, pred);
                            return EmitMinor(minors[1], [new Slot.Local(pred, new Repr(Kind.Nat, _c._clr.BigInteger)),
                                new Slot.Unavailable("this is structural recursion, which lean2il does not compile yet")], extra);
                        });
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
                            return EmitMinor(minors[1], [new Slot.Local(n, new Repr(Kind.Nat, _c._clr.BigInteger))], extra);
                        },
                        () => EmitMinor(minors[0], [new Slot.Local(m, new Repr(Kind.Nat, _c._clr.BigInteger))], extra));
                }
            }
            Layout l = _c.LayoutFor(ind) ?? throw new CompileError($"matching on {indName} is not compiled: {_c._layoutFailures.GetValueOrDefault(indName)}");
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
                    Repr r = EmitMinor(minors[i], [], extra);
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
            var slots = new List<Slot>();
            foreach (FieldSlot f in l.Fields)
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
            return EmitMinor(minors[0], slots, extra);
        }

        private void Throw(string exceptionType, string message)
        {
            Type t = _c._clr.CoreAssembly.GetType(exceptionType, throwOnError: true)!;
            Il.Emit(OpCodes.Ldstr, message);
            Il.Emit(OpCodes.Newobj, t.GetConstructor([_c._clr.String])!);
            Il.Emit(OpCodes.Throw);
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
        private Repr EmitMinor(Expr minor, IReadOnlyList<Slot> fieldSlots, Expr[] extra, int erasedFields = 0)
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
            return Emit(Expr.MkApp(Expr.MkApp(minor, fvs), extra));
        }
    }
}
