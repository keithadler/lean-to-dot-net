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
    /// <summary>Something lean2il does not compile yet: a function value, a recursive type, a type with indices.</summary>
    Unsupported,
}

internal sealed record Repr(Kind Kind, Type? Clr = null, Layout? Layout = null, string? Why = null)
{
    public static readonly Repr Erased = new(Kind.Erased);

    public bool IsData => Kind is Kind.Nat or Kind.Int or Kind.Bool or Kind.Enum or Kind.Struct;

    public Type ClrType => Clr ?? throw new CompileError(Why ?? $"no .NET type for a value of kind {Kind}");
}

/// <summary>A structure field: its Lean name, how it is held, and the .NET field holding it (null when erased).</summary>
internal sealed record FieldSlot(Name Name, string ClrName, Repr Repr, FieldBuilder? Field);

/// <summary>An inductive type lean2il turned into a .NET type.</summary>
internal sealed class Layout
{
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
