// Vendored from LeanViz (https://github.com/keithadler/leanviz, MIT), generator/Pretty.cs at commit 39a4905.
// Namespace changed from LeanViz; otherwise unmodified. Update by copying the file again.
using System.Text;
using Tenet.Kernel;

namespace LeanToDotNet.Vendor;

/// <summary>
/// Prints a kernel term the way a reader expects to see a statement: universe levels hidden, implicit and
/// instance arguments dropped, Lean's and Mathlib's notation for the operators everyone knows, binders grouped.
/// The kernel's own printer shows every argument because a checker must; a page must not.
///
/// This is not Lean's delaborator and cannot be, because running that would mean running Lean, which is the
/// dependency this project exists without. It knows the tables below and the binder shapes of the constants it
/// sees, nothing more. What it does not know it prints as a plain application, which is always correct and only
/// less pretty, and attributes that change Lean's own printing (<c>@[pp_nodot]</c>) live in environment
/// extensions the reader does not decode, so a few names read differently from the Mathlib docs.
///
/// The way to extend it is in CONTRIBUTING.md: sample real statements, compare with the docs, pin the fix in
/// MathlibPrettyTests. Every entry in these tables arrived that way rather than by guessing.
///
/// Precedences follow Lean's: 1024 is an atom, applications bind at 1023, <c>∀</c> and <c>fun</c> at 0. A form
/// whose body runs to the end of the line needs no parentheses as a last operand, which is what IsLeading is for.
/// Instances of this class are shared across threads and cache per-constant facts, so every field is concurrent.
/// </summary>
public sealed class Pretty
{
    private readonly Func<Name, ConstantInfo?> _find;
    private readonly System.Collections.Concurrent.ConcurrentDictionary<Name, Binder[]> _binders = new();

    /// <summary>One leading binder of a constant's type: its kind, and the head constant of its domain if it has one.</summary>
    private readonly record struct Binder(BinderInfo Info, Name? DomainHead);

    /// <summary>Output longer than this is cut; a page shows the statement, not the whole term.</summary>
    public int MaxLength { get; init; } = 3000;

    public Pretty(Func<Name, ConstantInfo?> find) => _find = find;

    /// <summary>An infix operator: its symbol, Lean's precedence for it, and associativity ('l', 'r', or 'n' for neither).</summary>
    private sealed record Op(string Symbol, int Prec, char Assoc);

    private static readonly Dictionary<string, Op> Binary = new(StringComparer.Ordinal)
    {
        ["Eq"] = new("=", 50, 'n'), ["Ne"] = new("≠", 50, 'n'), ["HEq"] = new("≍", 50, 'n'),
        ["LE.le"] = new("≤", 50, 'n'), ["LT.lt"] = new("<", 50, 'n'), ["GE.ge"] = new("≥", 50, 'n'), ["GT.gt"] = new(">", 50, 'n'),
        ["Iff"] = new("↔", 20, 'n'), ["And"] = new("∧", 35, 'r'), ["Or"] = new("∨", 30, 'r'),
        ["HAdd.hAdd"] = new("+", 65, 'l'), ["HSub.hSub"] = new("-", 65, 'l'), ["HMul.hMul"] = new("*", 70, 'l'),
        ["HDiv.hDiv"] = new("/", 70, 'l'), ["HMod.hMod"] = new("%", 70, 'l'), ["HPow.hPow"] = new("^", 75, 'r'),
        ["HAppend.hAppend"] = new("++", 65, 'l'), ["HSMul.hSMul"] = new("•", 73, 'r'), ["HVAdd.hVAdd"] = new("+ᵥ", 65, 'r'),
        ["Function.comp"] = new("∘", 90, 'r'), ["Dvd.dvd"] = new("∣", 50, 'n'),
        ["HasSubset.Subset"] = new("⊆", 50, 'n'), ["HasSSubset.SSubset"] = new("⊂", 50, 'n'),
        ["Union.union"] = new("∪", 65, 'l'), ["Inter.inter"] = new("∩", 70, 'l'), ["SDiff.sdiff"] = new("\\", 70, 'l'),
        ["Sup.sup"] = new("⊔", 68, 'l'), ["Inf.inf"] = new("⊓", 69, 'l'), ["Max.max"] = new("⊔", 68, 'l'), ["Min.min"] = new("⊓", 69, 'l'),
        ["Prod"] = new("×", 35, 'r'), ["Sum"] = new("⊕", 30, 'r'), ["PProd"] = new("×'", 35, 'r'),
        ["Equiv"] = new("≃", 25, 'n'), ["Function.Embedding"] = new("↪", 25, 'n'),
        ["Set.image"] = new("''", 81, 'l'), ["Set.preimage"] = new("⁻¹'", 80, 'l'),
        ["List.cons"] = new("::", 67, 'r'), ["Quiver.Hom"] = new("⟶", 10, 'n'), ["CategoryTheory.Iso"] = new("≅", 25, 'n'),
        ["CategoryTheory.Functor.comp"] = new("⋙", 80, 'l'), ["CategoryTheory.CategoryStruct.comp"] = new("≫", 80, 'r'),
        ["Finsupp"] = new("→₀", 25, 'r'), ["MulHom"] = new("→ₙ*", 25, 'r'), ["AddHom"] = new("→ₙ+", 25, 'r'), ["NonUnitalRingHom"] = new("→ₙ+*", 25, 'r'),
        ["MulOneClass"] = new("", 0, 'n'), ["MonoidHom"] = new("→*", 25, 'r'), ["AddMonoidHom"] = new("→+", 25, 'r'),
        ["RingHom"] = new("→+*", 25, 'r'), ["MulEquiv"] = new("≃*", 25, 'n'), ["AddEquiv"] = new("≃+", 25, 'n'),
        ["RingEquiv"] = new("≃+*", 25, 'n'), ["OrderHom"] = new("→o", 25, 'r'), ["OrderIso"] = new("≃o", 25, 'n'),
        ["ContinuousMap"] = new("→ᶜ", 25, 'r'), ["HasEquiv.Equiv"] = new("≈", 50, 'n'), ["Setoid.r"] = new("≈", 50, 'n'),
    };

    /// <summary>Constants that print as a symbol when applied to nothing visible; Mathlib's spellings for the number types.</summary>
    private static readonly Dictionary<string, string> Atoms = new(StringComparer.Ordinal)
    {
        ["Nat"] = "ℕ", ["Int"] = "ℤ", ["Rat"] = "ℚ", ["Real"] = "ℝ", ["Complex"] = "ℂ", ["NNReal"] = "ℝ≥0", ["ENNReal"] = "ℝ≥0∞",
        ["EReal"] = "EReal", ["ENat"] = "ℕ∞", ["Real.pi"] = "π", ["EmptyCollection.emptyCollection"] = "∅", ["Top.top"] = "⊤", ["Bot.bot"] = "⊥",
        ["Zero.zero"] = "0", ["One.one"] = "1", ["Set.univ"] = "Set.univ", ["Finset.univ"] = "Finset.univ",
        ["Option.none"] = "none", ["List.nil"] = "[]", ["Bool.true"] = "true", ["Bool.false"] = "false", ["Unit.unit"] = "()",
    };

    /// <summary>Class methods Mathlib exports to the root namespace, so that is how they read.</summary>
    private static readonly Dictionary<string, string> Aliases = new(StringComparer.Ordinal)
    {
        ["Star.star"] = "star", ["SupSet.sSup"] = "sSup", ["InfSet.sInf"] = "sInf", ["Insert.insert"] = "insert",
        ["Inhabited.default"] = "default", ["SizeOf.sizeOf"] = "sizeOf", ["Singleton.singleton"] = "singleton",
        ["Nonempty.some"] = "Nonempty.some", ["Opposite.op"] = "op", ["Opposite.unop"] = "unop", ["HasDistribNeg.neg_neg"] = "neg_neg",
        ["Function.Injective"] = "Function.Injective", ["Setoid.r"] = "Setoid.r", ["Sum.inl"] = "Sum.inl",
    };

    /// <summary>Symbols that wrap their one visible argument.</summary>
    private static readonly Dictionary<string, (string Open, string Close)> Around = new(StringComparer.Ordinal)
    {
        ["abs"] = ("|", "|"), ["Norm.norm"] = ("‖", "‖"), ["NNNorm.nnnorm"] = ("‖", "‖₊"), ["ENorm.enorm"] = ("‖", "‖ₑ"),
        ["Nat.ceil"] = ("⌈", "⌉₊"), ["Nat.floor"] = ("⌊", "⌋₊"), ["Int.ceil"] = ("⌈", "⌉"), ["Int.floor"] = ("⌊", "⌋"),
        ["Int.fract"] = ("Int.fract ", ""), ["Finset.card"] = ("#", ""), ["Nat.card"] = ("Nat.card ", ""),
    };

    /// <summary>Postfix symbols on one visible argument.</summary>
    private static readonly Dictionary<string, string> Postfix = new(StringComparer.Ordinal)
    {
        ["Units"] = "ˣ", ["OrderDual"] = "ᵒᵈ", ["Inv.inv"] = "⁻¹", ["HasCompl.compl"] = "ᶜ", ["Nat.factorial"] = "!",
        ["Opposite"] = "ᵒᵖ", ["Multiplicative"] = "", ["Additive"] = "",
    };

    /// <summary>Big operators and binders over a lambda: symbol, and whether a set argument comes first.</summary>
    private static readonly Dictionary<string, string> BigOps = new(StringComparer.Ordinal)
    {
        ["Finset.sum"] = "∑", ["Finset.prod"] = "∏", ["tsum"] = "∑'", ["tprod"] = "∏'", ["iSup"] = "⨆", ["iInf"] = "⨅",
        ["Set.iUnion"] = "⋃", ["Set.iInter"] = "⋂", ["Filter.Eventually"] = "∀ᶠ", ["Filter.Frequently"] = "∃ᶠ",
    };

    private static readonly Dictionary<string, (string Symbol, int Prec)> Prefix = new(StringComparer.Ordinal)
    {
        ["Not"] = ("¬", 40), ["Neg.neg"] = ("-", 75),
        ["Nat.cast"] = ("↑", 1024), ["Int.cast"] = ("↑", 1024), ["Rat.cast"] = ("↑", 1024), ["NNReal.toReal"] = ("↑", 1024),
        ["Subtype.val"] = ("↑", 1024), ["Real.sqrt"] = ("√", 100), ["NNReal.sqrt"] = ("√", 100),
        ["Set.Elem"] = ("↑", 1024), ["Complex.ofReal"] = ("↑", 1024), ["WithTop.some"] = ("↑", 1024), ["WithBot.some"] = ("↑", 1024),
        ["Fin.val"] = ("↑", 1024), ["Units.val"] = ("↑", 1024), ["SetLike.coe"] = ("↑", 1024), ["ZMod.cast"] = ("↑", 1024),
        ["ENNReal.ofNNReal"] = ("↑", 1024), ["Int.ofNat"] = ("↑", 1024), ["Ordinal.type"] = ("Ordinal.type ", 1024),
    };
    private static readonly HashSet<string> Anonymous = new(StringComparer.Ordinal)
    {
        "Subtype.mk", "Sigma.mk", "PSigma.mk", "And.intro", "Iff.intro",
    };

    /// <summary>What a declaration claims: its type, printed for reading.</summary>
    public string Statement(ConstantInfo c) => Print(c.Type);

    /// <summary>
    /// How a definition is defined: the term the kernel stores, printed like a statement.
    ///
    /// Only definitions and opaques, never theorems. A theorem's value is its proof term, and a proof term is
    /// machine output: measured over a Mathlib sample they average 22,000 characters, four hundred of them run
    /// past 100,000, and some do not finish inside 400,000. Nobody reads those, and carrying them would cost
    /// more than the rest of the bundle put together. Definition bodies are small and are what a reader means
    /// when they ask how something is defined.
    ///
    /// This is the elaborated term, not the source text. Lean's structure instance syntax arrives here as
    /// <c>let __src✝ := …</c>, side conditions have been lifted into their own <c>_proof_1</c> declarations,
    /// and nothing that was inferred is written the way the author wrote it. It is the truth about what the
    /// kernel checked, which is a different and equally useful thing from what someone typed; the page says
    /// which of the two it is showing, and links to the source for the other.
    /// </summary>
    public string? Body(ConstantInfo c)
    {
        if (c is not DefinitionInfo && c is not OpaqueInfo)
        {
            return null;
        }
        Expr? v = c.Value ?? (c as OpaqueInfo)?.OpaqueValue;
        return v is null ? null : Print(v);
    }

    /// <summary>
    /// The constant a declaration's conclusion is about: strip the binders, then take the head of the
    /// application spine. `Continuous.comp` concludes `Continuous (g ∘ f)`, so its head is `Continuous`.
    ///
    /// One cheap field, three questions that were unanswerable without it: which declarations are instances of
    /// a class (an instance is a def whose conclusion is that class), what else concludes the same thing as
    /// this lemma, and "show me everything that concludes an equality about Finset.sum".
    /// </summary>
    public static Name? ConclusionHead(ConstantInfo c)
    {
        Expr at = c.Type;
        while (at is PiExpr pi)
        {
            at = pi.Body;
        }
        while (at is AppExpr app)
        {
            at = app.Fn;
        }
        return at is ConstExpr k ? k.Name : null;
    }

    /// <summary>
    /// The fields of a structure or class: the constructor's arguments after the type's own parameters.
    ///
    /// Lean does not store a field list; a structure is an inductive with one constructor, and its fields are
    /// that constructor's telescope past the parameters. doc-gen4 shows these and losing them was reported as a
    /// regression there (#229), which is a fair measure of how much people use them.
    /// </summary>
    public (string Name, string Type)[] FieldsOf(ConstantInfo c, Func<Name, ConstantInfo?> find)
    {
        if (c is not InductiveInfo ind || ind.Ctors.Length != 1 || ind.NumIndices != 0)
        {
            return [];
        }
        if (find(ind.Ctors[0]) is not ConstructorInfo ctor)
        {
            return [];
        }
        // Each field's type may mention the structure's parameters and the fields before it, which are binders
        // outside it. Printing with an empty stack turned those into `#4`, so the stack is carried along.
        var fields = new List<(string, string)>();
        var binders = new List<string>();
        int depth = 0;
        for (Expr e = ctor.Type; e is PiExpr pi; e = pi.Body, depth++)
        {
            string name = pi.BinderName.ToString();
            if (depth >= ind.NumParams)
            {
                fields.Add((name, PrintUnder(pi.Domain, binders)));
            }
            binders.Add(name);
        }
        return fields.ToArray();
    }

    /// <summary>
    /// Whether <see cref="Print"/> cut this string. A cut body is not a shorter body, it is a different term,
    /// and a page that shows one as if it were whole is lying about what the kernel checked. About one body in
    /// a hundred reaches the cap, so this is not a corner nobody meets.
    /// </summary>
    public static bool WasCut(string printed) => printed.EndsWith(" …", StringComparison.Ordinal);

    /// <summary>
    /// A statement split the way a paper states a theorem: the setting it is about, the hypotheses it assumes,
    /// and the claim. A Lean type is a telescope of binders ending in a conclusion, and those binders divide
    /// cleanly: a binder whose domain is a proposition is a hypothesis, anything else is part of the setting.
    /// Hypotheses are numbered so the page can refer to them.
    /// </summary>
    public sealed record Shape(string[] Setting, string[] Hypotheses, string Conclusion);

    /// <summary>Split a declaration's type into setting, hypotheses and conclusion.</summary>
    public Shape ShapeOf(ConstantInfo c)
    {
        var setting = new List<string>();
        var hypotheses = new List<string>();
        var names = new List<string>();
        Expr at = c.Type;
        var pending = new List<(string Name, BinderInfo Info, Expr Domain)>();

        void FlushSetting()
        {
            // group consecutive binders of the same kind and domain, the way the inline printer does
            int i = 0;
            while (i < pending.Count)
            {
                // Consecutive binders of the same kind and domain share a line. The domains are not equal as
                // written, because each sits one binder deeper than the last, so compare against the lifted one.
                int j = i + 1;
                while (j < pending.Count && pending[j].Info == pending[i].Info
                       && pending[j].Domain.Equals(ExprOps.LiftLooseBVars(pending[i].Domain, j - i)))
                {
                    j++;
                }
                var group = pending.GetRange(i, j - i);
                string dom = Sub(pending[i].Domain, names.GetRange(0, names.Count - (pending.Count - i)), 0);
                bool anonymous = pending[i].Info == BinderInfo.InstImplicit && group.All(g => IsHygienicName(g.Name));
                setting.Add(anonymous ? dom : string.Join(' ', group.Select(g => g.Name)) + " : " + dom);
                i = j;
            }
            pending.Clear();
        }

        while (at is PiExpr pi)
        {
            bool nondependent = !ExprOps.HasLooseBVar(pi.Body, 0);
            if (IsPropLike(pi.Domain))
            {
                FlushSetting();
                string text = Sub(pi.Domain, names, 0);
                string label = nondependent || IsHygienicName(Display(pi.BinderName)) ? "" : Display(pi.BinderName) + " : ";
                hypotheses.Add(label + text);
                names.Add(nondependent ? "_" : Display(pi.BinderName));
            }
            else
            {
                string nm = BinderName(pi.BinderName, names);
                pending.Add((nm, pi.Info, pi.Domain));
                names.Add(nm);
            }
            at = pi.Body;
        }
        FlushSetting();
        string conclusion = Sub(at, names, 0);
        return new Shape(setting.ToArray(), hypotheses.ToArray(), conclusion);
    }

    private static bool IsHygienicName(string shown) => shown.EndsWith('✝') || shown.Length == 0;

    private readonly System.Collections.Concurrent.ConcurrentDictionary<Name, bool> _propValued = new();

    /// <summary>
    /// Whether a constant's type ends in <c>Prop</c>, so an application of it is a proposition. Structural: walk
    /// the telescope to the final sort. No inference, and no kernel, which is the point of this whole project.
    /// </summary>
    private bool IsPropValued(Name n) => _propValued.GetOrAdd(n, k =>
    {
        if (_find(k) is not ConstantInfo c)
        {
            return false;
        }
        Expr at = c.Type;
        while (at is PiExpr p)
        {
            at = p.Body;
        }
        return at is SortExpr s && s.Level.Kind == LevelKind.Zero;
    });

    /// <summary>Whether a binder's domain is a proposition, and so a hypothesis rather than part of the setting.</summary>
    private bool IsPropLike(Expr domain)
    {
        Expr at = domain;
        while (at is PiExpr p)
        {
            at = p.Body; // ∀ x, P x is a hypothesis if P x is
        }
        return at.GetAppArgs(out _) is ConstExpr c && IsPropValued(c.Name);
    }

    /// <summary>
    /// Print a term that sits under binders the caller already knows the names of, so its loose de Bruijn
    /// indices come out as those names rather than as <c>#4</c>.
    /// </summary>
    public string PrintUnder(Expr e, IReadOnlyList<string> binders)
    {
        var sb = new StringBuilder();
        var names = new List<string>(binders);
        Go(e, sb, names, 0);
        if (sb.Length > MaxLength)
        {
            sb.Length = MaxLength;
            sb.Append(" …");
        }
        return sb.ToString();
    }

    /// <summary>Print any term, cut at <see cref="MaxLength"/>. Terms are shared graphs, so an unbounded printer can blow up.</summary>
    public string Print(Expr e)
    {
        var sb = new StringBuilder();
        var names = new List<string>();
        Go(e, sb, names, 0);
        if (sb.Length > MaxLength)
        {
            sb.Length = MaxLength;
            sb.Append(" …");
        }
        return sb.ToString();
    }

    /// <summary>The leading ∀s of a constant's type: which arguments an application of it hides, and what each expects.</summary>
    private Binder[] BindersOf(Name n) => _binders.GetOrAdd(n, k =>
    {
        ConstantInfo? c = _find(k);
        if (c is null)
        {
            return [];
        }
        var infos = new List<Binder>();
        for (Expr t = c.Type; t is PiExpr p; t = p.Body)
        {
            infos.Add(new Binder(p.Info, p.Domain.GetAppArgs(out _) is ConstExpr h ? h.Name : null));
        }
        return infos.ToArray();
    });

    /// <summary>
    /// How a name is written for a reader. Lean mangles two kinds: a hygienic name, made up during elaboration,
    /// carries the module and a counter after <c>_@</c> and shows as the user part with a dagger, the way Lean
    /// prints it; a private name is wrapped in <c>_private.&lt;module&gt;.0</c> and shows without that wrapper.
    /// Components needing quotation get French quotes, as in Lean's own output.
    /// </summary>
    public static string Display(Name n)
    {
        var parts = new List<string>();
        bool hygienic = false;
        for (Name at = n; !at.IsAnonymous; at = at.Prefix)
        {
            if (at.TryGetStr(out _, out string? s))
            {
                if (s == "_@")
                {
                    hygienic = true;
                    parts.Clear();
                    continue;
                }
                if (hygienic && parts.Count == 0 && (s == "_hyg" || s.StartsWith('_')))
                {
                    continue;
                }
                parts.Add(s);
            }
            else if (at.TryGetNum(out _, out ulong v))
            {
                if (!hygienic)
                {
                    parts.Add(v.ToString());
                }
            }
        }
        // the hygienic walk collected the suffix after `_@` first, then cleared; what is left is the user part
        if (hygienic)
        {
            parts.Clear();
            for (Name at = n; !at.IsAnonymous; at = at.Prefix)
            {
                if (at.TryGetStr(out _, out string? s) && s == "_@")
                {
                    for (Name u = at.Prefix; !u.IsAnonymous; u = u.Prefix)
                    {
                        if (u.TryGetStr(out _, out string? us))
                        {
                            parts.Add(us);
                        }
                        else if (u.TryGetNum(out _, out ulong uv))
                        {
                            parts.Add(uv.ToString());
                        }
                    }
                    break;
                }
            }
            parts.Reverse();
            return string.Join('.', parts) + "✝";
        }
        parts.Reverse();
        if (parts.Count > 2 && parts[0] == "_private")
        {
            int i = parts.FindIndex(1, p => p == "0");
            if (i > 0 && i + 1 < parts.Count)
            {
                parts = parts.Skip(i + 1).ToList();
            }
        }
        return string.Join('.', parts.Select(Escape));
    }

    /// <summary>A name component needs French quotes when it would not parse bare, as in Lean's own output.</summary>
    private static string Escape(string s) =>
        s.Length == 0 || s.Contains('.') || s.Contains(' ') || char.IsDigit(s[0]) ? "«" + s + "»" : s;

    /// <summary>Whether elaboration invented this name, marked by an <c>_@</c> component.</summary>
    private static bool IsHygienic(Name n)
    {
        for (Name at = n; !at.IsAnonymous; at = at.Prefix)
        {
            if (at.TryGetStr(out _, out string? s) && s == "_@")
            {
                return true;
            }
        }
        return false;
    }

    /// <summary>Parenthesize when a form of precedence <paramref name="own"/> sits where <paramref name="want"/> is required.</summary>
    private static string Wrap(string s, int own, int want) => own < want ? "(" + s + ")" : s;

    /// <summary>
    /// The printer proper. <paramref name="names"/> is the binder stack, innermost last, which is how a de Bruijn
    /// index becomes a name; <paramref name="prec"/> is the precedence the context requires.
    /// </summary>
    private void Go(Expr e, StringBuilder sb, List<string> names, int prec)
    {
        if (sb.Length > MaxLength)
        {
            return;
        }
        switch (e)
        {
            case BVarExpr b:
                {
                    int i = names.Count - 1 - b.Idx;
                    sb.Append(i >= 0 ? names[i] : "#" + b.Idx);
                    break;
                }
            case FVarExpr f:
                sb.Append(f.Id);
                break;
            case SortExpr s:
                sb.Append(SortText(s.Level, prec));
                break;
            case ConstExpr c:
                sb.Append(Atoms.TryGetValue(c.Name.ToString(), out string? atom) ? atom : Display(c.Name));
                break;
            case LitExpr lit:
                sb.Append(lit.Value is StrLiteral str ? Quote(str.Value) : lit.Value.ToString());
                break;
            case ProjExpr p:
                Go(p.Struct, sb, names, 1024);
                sb.Append('.').Append(p.Idx + 1);
                break;
            case AppExpr:
                App(e, sb, names, prec);
                break;
            case LamExpr:
                {
                    if (prec > 0)
                    {
                        sb.Append('(');
                    }
                    sb.Append("fun");
                    Expr body = e;
                    int pushed = 0;
                    while (body is LamExpr l)
                    {
                        string nm = BinderName(l.BinderName, names);
                        sb.Append(' ').Append(nm);
                        names.Add(nm);
                        pushed++;
                        body = l.Body;
                    }
                    sb.Append(" => ");
                    Go(body, sb, names, 0);
                    names.RemoveRange(names.Count - pushed, pushed);
                    if (prec > 0)
                    {
                        sb.Append(')');
                    }
                    break;
                }
            case PiExpr pi:
                Pi(pi, sb, names, prec);
                break;
            case LetExpr l:
                {
                    if (prec > 0)
                    {
                        sb.Append('(');
                    }
                    string nm = BinderName(l.Name, names);
                    sb.Append("let ").Append(nm).Append(" := ");
                    Go(l.Value, sb, names, 0);
                    sb.Append("; ");
                    names.Add(nm);
                    Go(l.Body, sb, names, 0);
                    names.RemoveAt(names.Count - 1);
                    if (prec > 0)
                    {
                        sb.Append(')');
                    }
                    break;
                }
            default:
                sb.Append('?');
                break;
        }
    }

    /// <summary><c>Prop</c>, <c>Type</c>, <c>Type u</c> or <c>Sort u</c>: Lean's spellings for a universe.</summary>
    private static string SortText(Level l, int prec)
    {
        if (l.Kind == LevelKind.Zero)
        {
            return "Prop";
        }
        if (l.Equals(Level.One))
        {
            return "Type";
        }
        (Level b, int off) = l.ToOffset();
        if (off >= 1)
        {
            Level inner = Level.MkSucc(b, off - 1);
            string t = inner.Kind == LevelKind.Zero ? "Type" : "Type " + LevelText(inner);
            return prec > 1023 ? "(" + t + ")" : t;
        }
        string s = "Sort " + LevelText(l);
        return prec > 1023 ? "(" + s + ")" : s;
    }

    /// <summary>A universe level, parenthesized when it is compound.</summary>
    private static string LevelText(Level l)
    {
        string s = l.ToString();
        return s.Contains(' ') || s.Contains('+') ? "(" + s + ")" : s;
    }

    /// <summary>A string literal with the escapes Lean uses.</summary>
    private static string Quote(string s) => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\n", "\\n") + "\"";

    /// <summary>What to call a bound variable. An empty or invented name still needs something printable.</summary>
    private static string BinderName(Name n, List<string> names)
    {
        string s = IsHygienic(n) ? Display(n) : Display(n);
        return s.Length == 0 ? "x✝" : s;
    }

    /// <summary>
    /// A dependent function type: <c>A → B</c> when nothing depends on the binder, a bounded <c>∀ x ∈ s, p</c> when
    /// the body is an implication from a membership or comparison on the bound variable, otherwise grouped binders
    /// (<c>∀ {α β : Type} [Monoid α] (n m : ℕ), …</c>), consecutive binders of the same kind and domain sharing one
    /// group the way Lean prints them.
    /// </summary>
    private void Pi(PiExpr first, StringBuilder sb, List<string> names, int prec)
    {
        // A → B when nothing depends on the binder and it is explicit
        if (first.Info == BinderInfo.Default && !ExprOps.HasLooseBVar(first.Body, 0))
        {
            string left = Sub(first.Domain, names, 26);
            names.Add("_");
            string right = Sub(first.Body, names, IsLeading(first.Body) ? 0 : 25);
            names.RemoveAt(names.Count - 1);
            sb.Append(Wrap(left + " → " + right, 25, prec));
            return;
        }
        // ∀ x ∈ s, p  for  ∀ x, x ∈ s → p  (and <, ≤, >, ≥, ≠, ⊆ on the bound variable)
        if (first.Info == BinderInfo.Default && first.Body is PiExpr hyp && !ExprOps.HasLooseBVar(hyp.Body, 0)
            && BoundedOn(hyp.Domain) is (string bop, Expr brhs))
        {
            string x = BinderName(first.BinderName, names);
            names.Add(x);
            string rhsText = Sub(brhs, names, 51);
            string rest = Sub(ExprOps.LowerLooseBVars(hyp.Body, 1, 1), names, 0);
            names.RemoveAt(names.Count - 1);
            sb.Append(Wrap("∀ " + x + " " + bop + " " + rhsText + ", " + rest, 0, prec));
            return;
        }
        var groups = new List<string>();
        Expr body = first;
        int pushed = 0;
        while (body is PiExpr p && (ReferenceEquals(body, first) || p.Info != BinderInfo.Default || ExprOps.HasLooseBVar(p.Body, 0)))
        {
            // group binders with the same kind and the same closed domain: (n m : Nat)
            var run = new List<string>();
            Expr domain = p.Domain;
            BinderInfo info = p.Info;
            string domainText = Sub(domain, names, 0);
            while (body is PiExpr q && q.Info == info
                   && (run.Count == 0 || q.Domain.Equals(run.Count == 0 ? domain : ExprOps.LiftLooseBVars(domain, run.Count))))
            {
                if (run.Count > 0 && !(q.Info != BinderInfo.Default || ExprOps.HasLooseBVar(q.Body, 0)))
                {
                    break; // the next one is an arrow, not a binder
                }
                string nm = BinderName(q.BinderName, names);
                bool anonymousInst = info == BinderInfo.InstImplicit && (IsHygienic(q.BinderName) || !ExprOps.HasLooseBVar(q.Body, 0));
                run.Add(anonymousInst ? "" : nm);
                names.Add(nm);
                pushed++;
                body = q.Body;
                if (anonymousInst)
                {
                    break;
                }
            }
            var (open, close) = info switch
            {
                BinderInfo.Implicit => ("{", "}"),
                BinderInfo.StrictImplicit => ("⦃", "⦄"),
                BinderInfo.InstImplicit => ("[", "]"),
                _ => ("(", ")"),
            };
            groups.Add(run.Count == 1 && run[0].Length == 0
                ? open + domainText + close
                : open + string.Join(' ', run) + " : " + domainText + close);
        }
        string bodyText = Sub(body, names, 0);
        names.RemoveRange(names.Count - pushed, pushed);
        sb.Append(Wrap("∀ " + string.Join(' ', groups) + ", " + bodyText, 0, prec));
    }

    /// <summary>Whether a term mentions no variable bound outside it, so it can be compared across binders.</summary>
    private static bool LooseFree(Expr e) => e.LooseBVarRange == 0;

    /// <summary>A form whose body runs to the end of the line, so as a last operand it needs no parentheses: `p → ∀ x, q`.</summary>
    private static bool IsLeading(Expr e) =>
        e is PiExpr or LamExpr or LetExpr
        || (e.GetAppArgs(out _) is ConstExpr c && c.Name.ToString() is "Exists" or "ite" or "dite" or "MeasureTheory.integral" or "MeasureTheory.lintegral");

    /// <summary>Print a subterm to its own string, at the given precedence.</summary>
    private string Sub(Expr e, List<string> names, int prec)
    {
        var sb = new StringBuilder();
        Go(e, sb, names, prec);
        return sb.ToString();
    }

    /// <summary>
    /// An application, which is where nearly all the notation lives. The head's binders say which arguments are
    /// implicit or instance and so invisible; what is left is matched against the tables and the special cases,
    /// then generalized field notation, and finally printed as a plain application.
    /// </summary>
    private void App(Expr e, StringBuilder sb, List<string> names, int prec)
    {
        Expr head = e.GetAppArgs(out Expr[] args);
        if (head is ConstExpr c)
        {
            string name = c.Name.ToString();
            Binder[] infos = BindersOf(c.Name);
            var visible = new List<Expr>();
            for (int i = 0; i < args.Length; i++)
            {
                if (i >= infos.Length || infos[i].Info == BinderInfo.Default)
                {
                    visible.Add(args[i]);
                }
            }
            switch (name)
            {
                case "OfNat.ofNat" when args.Length >= 2:
                    Go(args[1], sb, names, prec);
                    return;
                case "DFunLike.coe" or "FunLike.coe" when visible.Count >= 2:
                    {
                        var parts = visible.Select(a => Sub(a, names, 1024)).ToList();
                        sb.Append(Wrap(string.Join(' ', parts), 1023, prec));
                        return;
                    }
                case "DFunLike.coe" or "FunLike.coe" when visible.Count == 1:
                    sb.Append('⇑').Append(Sub(visible[0], names, 1024));
                    return;
                case "Subtype" when visible.Count == 1 && visible[0] is LamExpr { Body: AppExpr } sl
                                  && sl.Body.GetAppArgs(out Expr[] memArgs) is ConstExpr { } memHead
                                  && memHead.Name.ToString() == "Membership.mem" && memArgs.Length >= 2
                                  && ((memArgs[^1] is BVarExpr { Idx: 0 } && !ExprOps.HasLooseBVar(memArgs[^2], 0))
                                      || (memArgs[^2] is BVarExpr { Idx: 0 } && !ExprOps.HasLooseBVar(memArgs[^1], 0))):
                    {
                        // { x // x ∈ S } is how a subobject is coerced to a type; Mathlib writes it ↥S
                        Expr set = memArgs[^1] is BVarExpr { Idx: 0 } ? memArgs[^2] : memArgs[^1];
                        sb.Append('↥').Append(Sub(ExprOps.LowerLooseBVars(set, 1, 1), names, 1024));
                        return;
                    }
                case "Exists" when visible.Count == 1 && visible[0] is LamExpr:
                    {
                        // ∃ x y, p  and  ∃ x ∈ s, p
                        var bound = new List<string>();
                        Expr at = e;
                        string? bounded = null;
                        while (bounded is null && at.GetAppArgs(out Expr[] ea) is ConstExpr { } eh && eh.Name.ToString() == "Exists"
                               && ea.Length == 2 && ea[1] is LamExpr el)
                        {
                            string nm = BinderName(el.BinderName, names);
                            names.Add(nm);
                            bound.Add(nm);
                            at = el.Body;
                            if (at.GetAppArgs(out Expr[] aa) is ConstExpr { } ah && ah.Name.ToString() == "And" && aa.Length == 2
                                && BoundedOn(aa[0]) is (string bop, Expr brhs))
                            {
                                bounded = " " + bop + " " + Sub(brhs, names, 51);
                                at = aa[1];
                            }
                        }
                        string body = Sub(at, names, 0);
                        names.RemoveRange(names.Count - bound.Count, bound.Count);
                        sb.Append(Wrap("∃ " + string.Join(' ', bound) + (bounded ?? "") + ", " + body, 0, prec));
                        return;
                    }
                case "Subtype" or "setOf" when visible.Count == 1 && visible[0] is LamExpr lam:
                    {
                        string nm = BinderName(lam.BinderName, names);
                        names.Add(nm);
                        string body = Sub(lam.Body, names, 0);
                        names.RemoveAt(names.Count - 1);
                        sb.Append(name == "Subtype" ? "{ " + nm + " // " + body + " }" : "{" + nm + " | " + body + "}");
                        return;
                    }
                case "Option.some" when visible.Count == 1:
                    sb.Append(Wrap("some " + Sub(visible[0], names, 1024), 1023, prec));
                    return;
                case "CategoryTheory.CategoryStruct.id" when visible.Count == 1:
                    sb.Append(Wrap("𝟙 " + Sub(visible[0], names, 1024), 1023, prec));
                    return;
                case "MeasureTheory.lintegral" when visible.Count == 2 && visible[1] is LamExpr ll:
                    {
                        string nm = BinderName(ll.BinderName, names);
                        names.Add(nm);
                        string body = Sub(ll.Body, names, 0);
                        names.RemoveAt(names.Count - 1);
                        sb.Append(Wrap("∫⁻ " + nm + ", " + body + " ∂" + Sub(visible[0], names, 1024), 0, prec));
                        return;
                    }
                case "dite" when visible.Count == 3 && visible[1] is LamExpr dt && visible[2] is LamExpr de:
                    {
                        string h = BinderName(dt.BinderName, names);
                        names.Add(h);
                        string thenText = Sub(dt.Body, names, 0);
                        names[^1] = BinderName(de.BinderName, names);
                        string elseText = Sub(de.Body, names, 0);
                        names.RemoveAt(names.Count - 1);
                        sb.Append(Wrap("if " + h + " : " + Sub(visible[0], names, 0) + " then " + thenText + " else " + elseText, 0, prec));
                        return;
                    }
                // M →ₗ[R] N and friends: the semilinear map over the identity ring hom is the linear map
                case "LinearMap" or "ContinuousLinearMap" when visible.Count == 3:
                    {
                        string? ring = IdentityRing(visible[0], names);
                        string arrow = name == "LinearMap" ? (ring is null ? "→ₛₗ[" : "→ₗ[") : (ring is null ? "→SL[" : "→L[");
                        string inside = ring ?? Sub(visible[0], names, 0);
                        sb.Append(Wrap(Sub(visible[1], names, 26) + " " + arrow + inside + "] " + Sub(visible[2], names, 25), 25, prec));
                        return;
                    }
                case "LinearEquiv" or "ContinuousLinearEquiv" when visible.Count == 3:
                    {
                        // (σ : R →+* S) {σ' : S →+* R} ... (M) (N): the inverse hom is implicit, so three are visible
                        string? ring = IdentityRing(visible[0], names);
                        string arrow = name == "LinearEquiv" ? (ring is null ? "≃ₛₗ[" : "≃ₗ[") : (ring is null ? "≃SL[" : "≃L[");
                        string inside = ring ?? Sub(visible[0], names, 0);
                        sb.Append(Wrap(Sub(visible[1], names, 26) + " " + arrow + inside + "] " + Sub(visible[2], names, 26), 25, prec));
                        return;
                    }
                case "CategoryTheory.Functor.id" when visible.Count == 1:
                    sb.Append(Wrap("𝟭 " + Sub(visible[0], names, 1024), 1023, prec));
                    return;
                case "AlgHom" or "AlgEquiv" or "LinearIsometry" or "LinearIsometryEquiv" or "AffineMap" or "AffineEquiv" when visible.Count == 3 && name is "AlgHom" or "AlgEquiv":
                    {
                        string arrow = name == "AlgHom" ? "→ₐ[" : "≃ₐ[";
                        sb.Append(Wrap(Sub(visible[1], names, 26) + " " + arrow + Sub(visible[0], names, 0) + "] " + Sub(visible[2], names, 26), 25, prec));
                        return;
                    }
                case "GetElem.getElem" or "GetElem?.getElem?" or "GetElem?.getElem!" when visible.Count >= 2:
                    sb.Append(Sub(visible[0], names, 1024)).Append('[').Append(Sub(visible[1], names, 0)).Append(']')
                      .Append(name.EndsWith('?') ? "?" : name.EndsWith('!') ? "!" : "");
                    return;
                case "MeasureTheory.integral" when visible.Count == 2 && visible[1] is LamExpr il:
                    {
                        // ∫ x, f x ∂μ
                        string nm = BinderName(il.BinderName, names);
                        names.Add(nm);
                        string body = Sub(il.Body, names, 0);
                        names.RemoveAt(names.Count - 1);
                        sb.Append(Wrap("∫ " + nm + ", " + body + " ∂" + Sub(visible[0], names, 1024), 0, prec));
                        return;
                    }
                case "ite" when visible.Count == 3:
                    sb.Append(Wrap("if " + Sub(visible[0], names, 0) + " then " + Sub(visible[1], names, 0) + " else " + Sub(visible[2], names, 0), 0, prec));
                    return;
                case "Prod.mk" when visible.Count == 2:
                    sb.Append('(').Append(Sub(visible[0], names, 0)).Append(", ").Append(Sub(visible[1], names, 0)).Append(')');
                    return;
                case "Membership.mem" when visible.Count == 2:
                    {
                        // Lean since late 2024: mem (collection) (element); before: mem (element) (collection)
                        bool collectionFirst = FirstExplicitDomainIsSecondImplicit(c.Name);
                        Expr elem = collectionFirst ? visible[1] : visible[0];
                        Expr coll = collectionFirst ? visible[0] : visible[1];
                        sb.Append(Wrap(Sub(elem, names, 51) + " ∈ " + Sub(coll, names, 51), 50, prec));
                        return;
                    }
            }
            if (Anonymous.Contains(name) && visible.Count == 2)
            {
                sb.Append('⟨').Append(Sub(visible[0], names, 0)).Append(", ").Append(Sub(visible[1], names, 0)).Append('⟩');
                return;
            }
            if (FieldsOf(c.Name) is (string[] fields, int numParams) && args.Length == numParams + fields.Length)
            {
                // a structure built from all its fields: { re := a, im := b }
                var parts = new List<string>();
                for (int i = 0; i < fields.Length; i++)
                {
                    parts.Add(fields[i] + " := " + Sub(args[numParams + i], names, 0));
                }
                sb.Append("{ ").Append(string.Join(", ", parts)).Append(" }");
                return;
            }
            if (Binary.TryGetValue(name, out Op? op) && visible.Count == 2)
            {
                int lp = op.Assoc == 'l' ? op.Prec : op.Prec + 1;
                int rp = IsLeading(visible[1]) ? 0 : op.Assoc == 'r' ? op.Prec : op.Prec + 1;
                sb.Append(Wrap(Sub(visible[0], names, lp) + " " + op.Symbol + " " + Sub(visible[1], names, rp), op.Prec, prec));
                return;
            }
            if (Prefix.TryGetValue(name, out (string Symbol, int Prec) pre) && visible.Count == 1)
            {
                sb.Append(Wrap(pre.Symbol + Sub(visible[0], names, pre.Prec), pre.Prec, prec));
                return;
            }
            if (Around.TryGetValue(name, out (string Open, string Close) around) && visible.Count == 1)
            {
                sb.Append(around.Open).Append(Sub(visible[0], names, around.Close.Length == 0 ? 1024 : 0)).Append(around.Close);
                return;
            }
            if (Postfix.TryGetValue(name, out string? post) && visible.Count == 1)
            {
                sb.Append(Sub(visible[0], names, 1024)).Append(post);
                return;
            }
            if (BigOps.TryGetValue(name, out string? big) && visible.Count >= 1 && visible[^1] is LamExpr bl)
            {
                // ∑ x ∈ s, f x  /  ∑ x, f x  /  ⨆ i, f i  /  ∀ᶠ x in l, p x
                string nm = BinderName(bl.BinderName, names);
                names.Add(nm);
                string bodyText = Sub(bl.Body, names, 0);
                names.RemoveAt(names.Count - 1);
                string where = "";
                if (name is "Filter.Eventually" or "Filter.Frequently")
                {
                    // the filter is the last explicit argument after the predicate; visible is [p, l]
                    if (visible.Count == 2)
                    {
                        where = " in " + Sub(visible[1], names, 1024);
                    }
                }
                else if (visible.Count == 2 && !(visible[0].GetAppArgs(out _) is ConstExpr { } u && u.Name.ToString() == "Finset.univ"))
                {
                    where = " ∈ " + Sub(visible[0], names, 1024);
                }
                sb.Append(Wrap(big + " " + nm + where + ", " + bodyText, 0, prec));
                return;
            }
            if (visible.Count == 0)
            {
                sb.Append(Atoms.TryGetValue(name, out string? atom) ? atom : Display(c.Name));
                return;
            }
            // generalized field notation: S.f (x : S ...) rest  prints as  x.f rest
            int dot = name.LastIndexOf('.');
            if (dot > 0 && infos.Length > 0 && visible[0] is not LitExpr)
            {
                int firstExplicit = Array.FindIndex(infos, b => b.Info == BinderInfo.Default);
                if (firstExplicit >= 0 && infos[firstExplicit].DomainHead is Name ownerType && ownerType.ToString() == name[..dot]
                    && !name[(dot + 1)..].StartsWith('_'))
                {
                    var rest = new List<string> { Sub(visible[0], names, 1024) + "." + Escape(name[(dot + 1)..]) };
                    rest.AddRange(visible.Skip(1).Select(a => Sub(a, names, 1024)));
                    // x.f alone is as tight as a name; x.f y is an application
                    sb.Append(Wrap(string.Join(' ', rest), rest.Count == 1 ? 1024 : 1023, prec));
                    return;
                }
            }
            if (name == "Singleton.singleton" && visible.Count == 1)
            {
                sb.Append('{').Append(Sub(visible[0], names, 0)).Append('}');
                return;
            }
            var pieces = new List<string> { Aliases.TryGetValue(name, out string? alias) ? alias : Display(c.Name) };
            pieces.AddRange(visible.Select(a => Sub(a, names, 1024)));
            sb.Append(Wrap(string.Join(' ', pieces), 1023, prec));
            return;
        }
        var all = new List<string> { Sub(head, names, 1023) };
        all.AddRange(args.Select(a => Sub(a, names, 1024)));
        sb.Append(Wrap(string.Join(' ', all), 1023, prec));
    }

    /// <summary>`x ∈ s`, `x < b`, and the like with `x` the innermost bound variable: the symbol and the other side.</summary>
    private (string Op, Expr Rhs)? BoundedOn(Expr hyp)
    {
        if (hyp.GetAppArgs(out Expr[] a) is not ConstExpr h)
        {
            return null;
        }
        Binder[] infos = BindersOf(h.Name);
        var vis = new List<Expr>();
        for (int i = 0; i < a.Length; i++)
        {
            if (i >= infos.Length || infos[i].Info == BinderInfo.Default)
            {
                vis.Add(a[i]);
            }
        }
        if (vis.Count != 2)
        {
            return null;
        }
        string n = h.Name.ToString();
        if (n == "Membership.mem")
        {
            bool collectionFirst = FirstExplicitDomainIsSecondImplicit(h.Name);
            Expr elem = collectionFirst ? vis[1] : vis[0];
            Expr coll = collectionFirst ? vis[0] : vis[1];
            return elem is BVarExpr { Idx: 0 } && !ExprOps.HasLooseBVar(coll, 0) ? ("∈", coll) : null;
        }
        string? sym = n switch
        {
            "LT.lt" => "<", "LE.le" => "≤", "GT.gt" => ">", "GE.ge" => "≥", "Ne" => "≠", "HasSubset.Subset" => "⊆", _ => null,
        };
        return sym is not null && vis[0] is BVarExpr { Idx: 0 } && !ExprOps.HasLooseBVar(vis[1], 0) ? (sym, vis[1]) : null;
    }

    /// <summary>`RingHom.id R` prints as the ring inside the arrow: M →ₗ[R] N. Anything else is a semilinear map.</summary>
    private string? IdentityRing(Expr sigma, List<string> names) =>
        sigma.GetAppArgs(out Expr[] a) is ConstExpr { } h && h.Name.ToString() == "RingHom.id" && a.Length >= 1
            ? Sub(a[0], names, 0)
            : null;

    private readonly System.Collections.Concurrent.ConcurrentDictionary<Name, (string[] Fields, int NumParams)?> _fields = new();

    /// <summary>
    /// The field names of a structure's constructor, read off its binder names, or null when the constructor is not
    /// a structure's (several constructors, indices, recursion) or a field name is hygienic.
    /// </summary>
    private (string[] Fields, int NumParams)? FieldsOf(Name ctor) => _fields.GetOrAdd(ctor, k =>
    {
        if (_find(k) is not ConstructorInfo ci || ci.NumFields == 0 || _find(ci.Induct) is not InductiveInfo ii
            || ii.Ctors.Length != 1 || ii.NumIndices != 0 || ii.IsRec || Anonymous.Contains(k.ToString()) || k.ToString() is "Prod.mk" or "PProd.mk")
        {
            return null;
        }
        var fields = new List<string>();
        int i = 0;
        for (Expr t = ci.Type; t is PiExpr p; t = p.Body, i++)
        {
            if (i >= ci.NumParams)
            {
                if (IsHygienic(p.BinderName))
                {
                    return null;
                }
                fields.Add(Display(p.BinderName));
            }
        }
        return fields.Count == ci.NumFields ? (fields.ToArray(), ci.NumParams) : null;
    });

    private readonly System.Collections.Concurrent.ConcurrentDictionary<Name, bool> _memOrder = new();

    /// <summary>For Membership.mem: whether the first explicit binder's type is the second implicit (the collection type).</summary>
    private bool FirstExplicitDomainIsSecondImplicit(Name n) => _memOrder.GetOrAdd(n, k =>
    {
        ConstantInfo? c = _find(k);
        int depth = 0;
        for (Expr t = c?.Type ?? Expr.Sort(Level.Zero); t is PiExpr p; t = p.Body, depth++)
        {
            if (p.Info == BinderInfo.Default)
            {
                return p.Domain is BVarExpr b && depth - 1 - b.Idx == 1;
            }
        }
        return true;
    });
}
