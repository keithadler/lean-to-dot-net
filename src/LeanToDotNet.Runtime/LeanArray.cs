using System.Collections;
using System.Numerics;

namespace LeanToDotNet.Runtime;

/// <summary>
/// Lean's <c>Array α</c>: immutable to its holder, backed by a .NET array, so indexing and <c>size</c> take constant
/// time. C# can pass a <c>T[]</c> where one is expected.
///
/// Lean updates an array in place when nothing else holds it. Compiled code cannot know that, so it does the next
/// best thing: arrays share a buffer, and <c>push</c> onto the newest array writes into the buffer's spare room
/// instead of copying, which makes building an array by pushing linear, as in Lean. <c>set</c> copies.
/// </summary>
public sealed class LeanArray<T> : IReadOnlyList<T>, IEquatable<LeanArray<T>>, ILeanArray
{
    private sealed class Buffer(T[] items, int used)
    {
        public T[] Items = items;
        public int Used = used;
    }

    private static readonly LeanArray<T> s_empty = new(new Buffer([], 0), 0);

    /// <summary><c>#[]</c>.</summary>
    public static LeanArray<T> Empty => s_empty;

    private readonly Buffer _buffer;

    private LeanArray(Buffer buffer, int count)
    {
        _buffer = buffer;
        Count = count;
    }

    public int Count { get; }

    public T this[int index] => (uint)index < (uint)Count ? _buffer.Items[index] : throw new ArgumentOutOfRangeException(nameof(index));

    public static LeanArray<T> From(IEnumerable<T> items)
    {
        T[] a = items.ToArray();
        return a.Length == 0 ? s_empty : new LeanArray<T>(new Buffer(a, a.Length), a.Length);
    }

    public static implicit operator LeanArray<T>(T[] items) => From(items);

    /// <summary><c>a.push x</c>.</summary>
    public LeanArray<T> Push(T item)
    {
        lock (_buffer)
        {
            if (Count == _buffer.Used && Count < _buffer.Items.Length)
            {
                _buffer.Items[Count] = item;
                _buffer.Used++;
                return new LeanArray<T>(_buffer, Count + 1);
            }
        }
        var grown = new T[Math.Max(4, checked(Count * 2))];
        Array.Copy(_buffer.Items, grown, Count);
        grown[Count] = item;
        return new LeanArray<T>(new Buffer(grown, Count + 1), Count + 1);
    }

    /// <summary><c>a.set i x</c>, for <c>i</c> in range.</summary>
    public LeanArray<T> Set(int index, T item)
    {
        if ((uint)index >= (uint)Count)
        {
            throw new ArgumentOutOfRangeException(nameof(index));
        }
        var copy = new T[Count];
        Array.Copy(_buffer.Items, copy, Count);
        copy[index] = item;
        return new LeanArray<T>(new Buffer(copy, Count), Count);
    }

    public LeanList<T> ToList()
    {
        LeanList<T> l = LeanList<T>.Nil;
        for (int i = Count - 1; i >= 0; i--)
        {
            l = LeanList<T>.Cons(_buffer.Items[i], l);
        }
        return l;
    }

    BigInteger ILeanArray.Size => Count;
    object? ILeanArray.Get(BigInteger index) => this[Index(index)];
    ILeanArray ILeanArray.Push(object? item) => Push((T)item!);
    ILeanArray ILeanArray.Set(BigInteger index, object? item) => Set(Index(index), (T)item!);
    ILeanArray ILeanArray.SetIfInBounds(BigInteger index, object? item) => index >= 0 && index < Count ? Set((int)index, (T)item!) : this;
    bool ILeanArray.InBounds(BigInteger index) => index >= 0 && index < Count;
    ILeanList ILeanArray.ToList() => ToList();

    ILeanArray ILeanArray.Append(ILeanList items)
    {
        LeanArray<T> a = this;
        for (ILeanList l = items; !l.IsNil; l = l.TailObject)
        {
            a = a.Push((T)l.HeadObject!);
        }
        return a;
    }

    private int Index(BigInteger i) => i >= 0 && i < Count ? (int)i : throw new ArgumentOutOfRangeException(nameof(i), $"index {i} is out of bounds for an array of size {Count}");

    public IEnumerator<T> GetEnumerator()
    {
        for (int i = 0; i < Count; i++)
        {
            yield return _buffer.Items[i];
        }
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public bool Equals(LeanArray<T>? other) => other is not null && Count == other.Count && this.SequenceEqual(other);
    public override bool Equals(object? obj) => obj is LeanArray<T> a && Equals(a);
    public override int GetHashCode() => this.Aggregate(Count, (h, x) => HashCode.Combine(h, x));
    public override string ToString() => "#[" + string.Join(", ", this) + "]";
}

/// <summary>What compiled code sees of an array; see <see cref="ILeanList"/> for why it is not generic.</summary>
public interface ILeanArray
{
    BigInteger Size { get; }
    object? Get(BigInteger index);
    bool InBounds(BigInteger index);
    ILeanArray Push(object? item);
    ILeanArray Set(BigInteger index, object? item);
    ILeanArray SetIfInBounds(BigInteger index, object? item);
    ILeanList ToList();
    /// <summary>This array followed by the list's items.</summary>
    ILeanArray Append(ILeanList items);
}
