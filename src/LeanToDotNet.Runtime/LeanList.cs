using System.Collections;

namespace LeanToDotNet.Runtime;

/// <summary>
/// Lean's <c>List α</c>: immutable and singly linked, exactly the shape a Lean function pattern-matches on, so a
/// compiled <c>match l with | [] => … | x :: xs => …</c> is a null test and two field reads. It is also an ordinary
/// <see cref="IReadOnlyList{T}"/>, and C# can pass an array where one is expected:
/// <c>Proven.Total(new BigInteger[] { 1, 2, 3 })</c>.
/// </summary>
public sealed class LeanList<T> : IReadOnlyList<T>, IEquatable<LeanList<T>>, ILeanList
{
    private static readonly LeanList<T> s_nil = new(default!, null!, 0);

    /// <summary><c>[]</c>. A property rather than a field, so compiled code can refer to it on any <c>T</c>.</summary>
    public static LeanList<T> Nil => s_nil;

    private readonly T _head;
    private readonly LeanList<T>? _tail;

    private LeanList(T head, LeanList<T>? tail, int count)
    {
        _head = head;
        _tail = tail;
        Count = count;
    }

    /// <summary><c>x :: xs</c>.</summary>
    public static LeanList<T> Cons(T head, LeanList<T> tail) => new(head, tail, checked(tail.Count + 1));

    public bool IsNil => _tail is null;
    public T Head => IsNil ? throw new InvalidOperationException("the empty list has no head") : _head;
    public LeanList<T> Tail => _tail ?? throw new InvalidOperationException("the empty list has no tail");
    public int Count { get; }

    public T this[int index]
    {
        get
        {
            LeanList<T> l = this;
            for (int i = 0; i < index && !l.IsNil; i++)
            {
                l = l._tail!;
            }
            return l.IsNil || index < 0 ? throw new ArgumentOutOfRangeException(nameof(index)) : l._head;
        }
    }

    bool ILeanList.IsNil => IsNil;
    object? ILeanList.HeadObject => Head;
    ILeanList ILeanList.TailObject => Tail;
    ILeanList ILeanList.Prepend(object? head) => Cons((T)head!, this);

    public static LeanList<T> From(IEnumerable<T> items)
    {
        T[] a = items as T[] ?? items.ToArray();
        LeanList<T> l = Nil;
        for (int i = a.Length - 1; i >= 0; i--)
        {
            l = Cons(a[i], l);
        }
        return l;
    }

    public static implicit operator LeanList<T>(T[] items) => From(items);

    public IEnumerator<T> GetEnumerator()
    {
        for (LeanList<T> l = this; !l.IsNil; l = l._tail!)
        {
            yield return l._head;
        }
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public bool Equals(LeanList<T>? other) => other is not null && Count == other.Count && this.SequenceEqual(other);
    public override bool Equals(object? obj) => obj is LeanList<T> l && Equals(l);
    public override int GetHashCode() => this.Aggregate(Count, (h, x) => HashCode.Combine(h, x));
    public override string ToString() => "[" + string.Join(", ", this) + "]";
}

/// <summary>Helpers for building a <see cref="LeanList{T}"/> without naming its type.</summary>
public static class LeanList
{
    public static LeanList<T> Of<T>(params T[] items) => LeanList<T>.From(items);
}

/// <summary>Lean's <c>Option α</c>: <c>none</c> or <c>some x</c>.</summary>
public sealed class LeanOption<T> : IEquatable<LeanOption<T>>, ILeanOption
{
    private static readonly LeanOption<T> s_none = new(default!, false);

    /// <summary><c>none</c>.</summary>
    public static LeanOption<T> None => s_none;

    private readonly T _value;

    private LeanOption(T value, bool isSome)
    {
        _value = value;
        IsSome = isSome;
    }

    public static LeanOption<T> Some(T value) => new(value, true);

    public bool IsSome { get; }
    public T Value => IsSome ? _value : throw new InvalidOperationException("none has no value");

    object? ILeanOption.ValueObject => Value;
    ILeanOption ILeanOption.Some(object? value) => Some((T)value!);

    public bool Equals(LeanOption<T>? other) => other is not null && IsSome == other.IsSome && (!IsSome || EqualityComparer<T>.Default.Equals(_value, other._value));
    public override bool Equals(object? obj) => obj is LeanOption<T> o && Equals(o);
    public override int GetHashCode() => IsSome ? HashCode.Combine(1, _value) : 0;
    public override string ToString() => IsSome ? $"some {_value}" : "none";
}

/// <summary>Lean's <c>String</c> operations with Lean's meaning: lengths count Unicode code points, not UTF-16 units.</summary>
public static class LeanString
{
    public static System.Numerics.BigInteger Length(string s) => s.EnumerateRunes().Count();
    public static string Append(string a, string b) => a + b;
    public static bool DecEq(string a, string b) => string.Equals(a, b, StringComparison.Ordinal);
}

/// <summary>
/// What compiled code sees of a list: non-generic, because an assembly written by <c>PersistedAssemblyBuilder</c>
/// against reference assemblies cannot refer to a member of a generic runtime type. It casts back to the typed
/// <see cref="LeanList{T}"/> wherever a list leaves or enters a method, so callers only ever see the typed list.
/// </summary>
public interface ILeanList
{
    bool IsNil { get; }
    object? HeadObject { get; }
    ILeanList TailObject { get; }
    /// <summary><c>head :: this</c>.</summary>
    ILeanList Prepend(object? head);
}

/// <summary>What compiled code sees of an option; see <see cref="ILeanList"/>.</summary>
public interface ILeanOption
{
    bool IsSome { get; }
    object? ValueObject { get; }
    /// <summary><c>some value</c>, at this option's element type.</summary>
    ILeanOption Some(object? value);
}

/// <summary>The empty list and <c>none</c> at a type compiled code names with a type token.</summary>
public static class LeanOps
{
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<RuntimeTypeHandle, object> s_empty = new();

    public static object Nil(RuntimeTypeHandle listType) => Empty(listType, "Nil");

    public static object None(RuntimeTypeHandle optionType) => Empty(optionType, "None");

    private static object Empty(RuntimeTypeHandle h, string property) =>
        s_empty.GetOrAdd(h, x => Type.GetTypeFromHandle(x)!.GetProperty(property)!.GetValue(null)!);
}
