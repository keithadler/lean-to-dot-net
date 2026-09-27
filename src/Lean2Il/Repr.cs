using System.Reflection;
using System.Reflection.Emit;
using Tenet.Kernel;

namespace LeanToDotNet;

/// <summary>How a Lean value is held at run time.</summary>
internal enum Kind
{
    /// <summary>A type or a proof. Nothing is computed from it, so it is not passed at all.</summary>
    Erased,
    /// <summary><c>Nat</c>, as a <c>BigInteger</c> that is never negative.</summary>
    Nat,
    /// <summary><c>Int</c>, as a <c>BigInteger</c>.</summary>
    Int,
    /// <summary><c>Bool</c>, and <c>Decidable p</c>, whose proof is erased and whose answer is kept.</summary>
    Bool,
    /// <summary>An inductive type whose constructors take no arguments, as a .NET enum.</summary>
    Enum,
    /// <summary>A structure, as a sealed .NET class with one read-only field per field that is not erased.</summary>
    Struct,
    /// <summary><c>String</c>, as <c>System.String</c>.</summary>
    String,
    /// <summary><c>List α</c>, as <c>LeanList&lt;T&gt;</c>.</summary>
    List,
    /// <summary><c>Option α</c>, as <c>LeanOption&lt;T&gt;</c>.</summary>
    Option,
    /// <summary>
    /// An inductive type with several constructors, some carrying data, or with itself as a field: an abstract class
    /// with a <c>Tag</c>, and a sealed nested class per constructor. Trees, expression syntax, results.
    /// </summary>
    Union,
    /// <summary>
    /// <c>UInt8</c> ... <c>UInt64</c> and <c>Int8</c> ... <c>Int64</c>, as <c>byte</c> ... <c>ulong</c> and
    /// <c>sbyte</c> ... <c>long</c>. Which one is in <see cref="Repr.Clr"/>; <see cref="FixedWidth"/> has the rest.
    /// </summary>
    Fixed,
    /// <summary><c>Array α</c>, as <c>LeanArray&lt;T&gt;</c>.</summary>
    Array,
    /// <summary>Something lean2il does not compile yet: a function value, a recursive type, a type with indices.</summary>
    Unsupported,
}

internal sealed record Repr(Kind Kind, Type? Clr = null, Layout? Layout = null, string? Why = null, Repr? Elem = null)
{
    /// <summary>
    /// A <c>Fin n</c> or a subtype: held as its value, with the proof about it erased. Anything passing one in from
    /// outside Lean has to keep the promise the proof made.
    /// </summary>
    public bool Constrained { get; init; }

    public static readonly Repr Erased = new(Kind.Erased);

    public bool IsData => Kind is Kind.Nat or Kind.Int or Kind.Bool or Kind.Enum or Kind.Struct or Kind.String or Kind.List or Kind.Option or Kind.Union or Kind.Fixed or Kind.Array;

    public Type ClrType => Clr ?? throw new CompileError(Why ?? $"no .NET type for a value of kind {Kind}");
}

/// <summary>
/// A Lean fixed-width integer and the .NET integer it is: same width, same signedness, so every value maps to
/// exactly one value and back. The operations whose meaning differs (division by zero, shift counts past the
/// width) go through <c>LeanFixed</c> in the runtime.
/// </summary>
internal sealed record FixedWidth(string Lean, string Clr, string CSharp, int Bits, bool Signed)
{
    public static readonly FixedWidth[] All =
    [
        new("UInt8", "System.Byte", "byte", 8, false),
        new("UInt16", "System.UInt16", "ushort", 16, false),
        new("UInt32", "System.UInt32", "uint", 32, false),
        new("UInt64", "System.UInt64", "ulong", 64, false),
        new("Int8", "System.SByte", "sbyte", 8, true),
        new("Int16", "System.Int16", "short", 16, true),
        new("Int32", "System.Int32", "int", 32, true),
        new("Int64", "System.Int64", "long", 64, true),
    ];

    public static FixedWidth? OfLean(string name) => All.FirstOrDefault(f => f.Lean == name);

    public static FixedWidth OfClr(Type t) => All.First(f => f.Clr == t.FullName);

    public System.Numerics.BigInteger Min => Signed ? -(System.Numerics.BigInteger.One << (Bits - 1)) : 0;

    public System.Numerics.BigInteger Max => (System.Numerics.BigInteger.One << (Signed ? Bits - 1 : Bits)) - 1;

    /// <summary>What Lean's <c>ofNat</c> and <c>ofInt</c> make of any integer: its low bits, read with this sign.</summary>
    public System.Numerics.BigInteger Wrap(System.Numerics.BigInteger n)
    {
        var low = n & ((System.Numerics.BigInteger.One << Bits) - 1);
        return low > Max ? low - (System.Numerics.BigInteger.One << Bits) : low;
    }

    /// <summary>A value in range as the boxed .NET integer, for reflection.</summary>
    public object Box(System.Numerics.BigInteger v) =>
        Convert.ChangeType(v > long.MaxValue ? (object)(ulong)v : (long)v, Type.GetType(Clr, true)!, System.Globalization.CultureInfo.InvariantCulture);
}

/// <summary>A structure field: its Lean name, how it is held, and the .NET field holding it (null when erased).</summary>
internal sealed record FieldSlot(Name Name, string ClrName, Repr Repr, FieldBuilder? Field);

/// <summary>One constructor of a union: its .NET class, fields, constructor, and how many fields are the type itself.</summary>
internal sealed record Variant(Name Ctor, string ClrName, TypeBuilder Type, List<FieldSlot> Fields, ConstructorBuilder Constructor, int SelfFields)
{
    public FieldSlot[] RuntimeFields => Fields.Where(f => f.Field is not null).ToArray();
}

/// <summary>An inductive type lean2il turned into a .NET type, at one instantiation of its parameters.</summary>
internal sealed class Layout
{
    /// <summary>The parameters this copy is for (<c>Int</c> in <c>Tree Int</c>); empty for a type without parameters.</summary>
    public Expr[] Params { get; init; } = [];
    public Level[] Levels { get; init; } = [];
    /// <summary>The Lean type this is, <c>Tree Int</c>, for printing.</summary>
    public Expr? LeanType { get; init; }
    public List<Variant> Variants { get; } = new();
    public FieldBuilder? TagField { get; set; }
    /// <summary>For a structure: how many of its fields are the structure itself.</summary>
    public int SelfFields { get; set; }

    public required Name Name { get; init; }
    public required InductiveInfo Info { get; init; }
    public required Kind Kind { get; init; }
    /// <summary>The <see cref="TypeBuilder"/> or <see cref="EnumBuilder"/>; either is a <see cref="Type"/>.</summary>
    public required Type Builder { get; init; }
    public required string ClrName { get; init; }
    public List<(Name Ctor, string ClrName, FieldBuilder Literal)> Cases { get; } = new();
    public List<FieldSlot> Fields { get; } = new();
    public ConstructorBuilder? Ctor { get; set; }

    /// <summary>
    /// Two fields at run time, an <c>Int</c> and then a <c>Nat</c>: a mantissa and a scale, which is what a
    /// <c>System.Decimal</c> is. Functions over such a structure get a second overload taking <c>decimal</c>.
    /// </summary>
    public bool DecimalShaped =>
        Kind == Kind.Struct && Fields.Count(f => f.Field is not null) == 2
        && Fields.Where(f => f.Field is not null).Select(f => f.Repr.Kind).SequenceEqual([LeanToDotNet.Kind.Int, LeanToDotNet.Kind.Nat]);

    public FieldSlot[] RuntimeFields => Fields.Where(f => f.Field is not null).ToArray();
}

/// <summary>A reason the input cannot be compiled, meant for the person who wrote the Lean.</summary>
internal sealed class CompileError(string message) : Exception(message);
