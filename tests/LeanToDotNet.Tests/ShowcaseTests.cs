using System.Numerics;
using LeanToDotNet.Runtime;
using Showcase;
using Xunit;

namespace LeanToDotNet.Tests;

/// <summary>Recursion, lists, options, strings, lambdas, custom types and fixed-width integers, as a C# caller sees them.</summary>
public class ShowcaseTests
{
    [Fact]
    public void ArraysPassAsLists()
    {
        Assert.Equal(6, Proven.Total(new BigInteger[] { 1, 2, 3 }));
        Assert.Equal(0, Proven.Total(new BigInteger[0]));
        Assert.Equal(13, Proven.LibSum(LeanList.Of<BigInteger>(5, -2, 10)));
    }

    [Fact]
    public void ListsComeBackAsLists()
    {
        LeanList<BigInteger> r = Proven.RevDouble(new BigInteger[] { 1, 2, 3 });
        Assert.Equal(new BigInteger[] { 6, 4, 2 }, r);
        Assert.Equal("[6, 4, 2]", r.ToString());
        Assert.Equal(new BigInteger[] { 1, 2, 3 }, Proven.Join(new BigInteger[] { 1, 2 }, new BigInteger[] { 3 }));
    }

    [Fact]
    public void OptionsSayNone()
    {
        Assert.False(Proven.First(new BigInteger[0]).IsSome);
        Assert.Equal(9, Proven.First(new BigInteger[] { 9, 8 }).Value);
        Assert.Equal(7, Proven.MaxOf(new BigInteger[] { 3, 7, 2 }).Value);
        Assert.False(Proven.MaxOf(new BigInteger[0]).IsSome);
    }

    [Fact]
    public void StringsCountCharactersAsLeanDoes()
    {
        Assert.Equal("hello Grace, you are number 42", Proven.Greet("Grace", 42));
        Assert.Equal(3, Proven.Chars("a😀b"));   // .NET's "a😀b".Length is 4
    }

    [Fact]
    public void RecursionDeepAndLoopsLong()
    {
        BigInteger n = 200_000;
        Assert.Equal(n * (n + 1) / 2, Proven.SumTo(n));   // not tail recursive: rerun on a big stack
        Assert.Equal(21, Proven.GcdPrime(1071, 462));
        Assert.Equal(1800, Proven.DigitSum(BigInteger.Pow(10, 200) - 1, 0));   // tail recursive: a loop
    }

    [Fact]
    public void ANegativeNatIsStillRefused() =>
        Assert.Throws<ArgumentOutOfRangeException>(() => Proven.SumTo(-1));

    [Fact]
    public void LambdasKeepTheirLocals()
    {
        Assert.Equal(new BigInteger[] { 11, 12, 13 }, Proven.AddAll(10, new BigInteger[] { 1, 2, 3 }));
        Assert.Equal(new BigInteger[] { 3, 4 }, Proven.Between(2, 5, new BigInteger[] { 1, 2, 3, 4, 5, 6 }));
        Assert.Equal(1 + 5 + 5, Proven.CappedSum(5, new BigInteger[] { 1, 7, 9 }));
        Assert.Equal(new BigInteger[] { 1, -2 }, Proven.Scale(2, 3, new BigInteger[] { 2, -2 }));   // floor(-4/3) = -2
    }

    [Fact]
    public void ASyntaxTreeIsAClassHierarchy()
    {
        // 2 * (x + 3) with x = 4
        Arith e = new Arith.Mul(new Arith.Num(2), new Arith.Add(new Arith.Var(0), new Arith.Num(3)));
        Assert.Equal(14, Proven.Eval(new BigInteger[] { 4 }, e));
        Arith folded = Proven.Fold(new Arith.Add(new Arith.Num(2), new Arith.Num(3)));
        Assert.Equal(5, Assert.IsType<Arith.Num>(folded).N);
        Assert.IsType<Arith.Num>(Proven.Fold(new Arith.Mul(new Arith.Var(7), new Arith.Num(0))));
    }

    [Fact]
    public void TreesSortAndSearch()
    {
        Assert.Equal(new BigInteger[] { -4, 1, 2, 3, 9 }, Proven.TreeSort(new BigInteger[] { 3, 9, 1, -4, 2, 3 }));
        Tree t = Proven.OfList(new BigInteger[] { 5, 2, 8 });
        Assert.True(Proven.Contains(8, t));
        Assert.False(Proven.Contains(7, t));
        Assert.True(Proven.Contains(7, Proven.Insert(7, t)));
        Assert.Equal(Enumerable.Range(0, 2000).Select(i => (BigInteger)i), Proven.TreeSort(Enumerable.Range(0, 2000).Select(i => (BigInteger)i).ToArray()));
    }

    [Fact]
    public void ResultsCarryTheirCase()
    {
        Assert.Equal(3, Assert.IsType<Result.Ok>(Proven.SafeDiv(7, 2)).Value);
        Assert.Equal("cannot divide 7 by zero", Assert.IsType<Result.Error>(Proven.SafeDiv(7, 0)).Message);
        PairOfIntInt mm = Proven.MinMax(new BigInteger[] { 3, -1, 8 }).Value;
        Assert.Equal((-1, 8), ((int)mm.First, (int)mm.Second));
        Assert.False(Proven.MinMax(new BigInteger[0]).IsSome);
    }

    [Fact]
    public void FixedWidthIntegersAreTheCSharpTypes()
    {
        byte[] hello = System.Text.Encoding.ASCII.GetBytes("hello");
        Assert.Equal(0xa430d84680aabd0bUL, Proven.Fnv1a(hello));   // the published FNV-1a 64 of "hello"
        Assert.Equal((byte)255, Proven.SaturatingAdd(200, 100));
        Assert.Equal((byte)44, unchecked((byte)(200 + 100)));
        Assert.Equal(3u, Proven.RotateLeft(0x80000001u, 1));
        Assert.Equal(0x80000001u, Proven.RotateLeft(0x80000001u, 32));   // Lean's shift count wraps; so does this
        Assert.Equal(int.MinValue, Proven.ClampToInt32(BigInteger.Pow(-10, 11)));
    }

    [Fact]
    public void TheMidpointBugAndItsFix()
    {
        int lo = 2_000_000_000, hi = 2_100_000_000;
        Assert.Equal(unchecked(lo + hi) / 2, Proven.NaiveMidpoint(lo, hi));   // wraps negative, as it does in C#
        Assert.True(Proven.NaiveMidpoint(lo, hi) < 0);
        Assert.Equal(2_050_000_000, Proven.Midpoint(lo, hi));
        Assert.Equal(int.MaxValue - 1, Proven.Midpoint(int.MaxValue - 2, int.MaxValue));
    }

    [Fact]
    public void ArraysAreArrays()
    {
        Assert.Equal(6, Proven.ArraySum(new BigInteger[] { 1, 2, 3 }));
        Assert.Equal(new BigInteger[] { 1, 3, 6 }, Proven.RunningTotals(new BigInteger[] { 1, 2, 3 }));
        Assert.Equal(new BigInteger[] { 1, 2, 0 }, Proven.Histogram(3, new BigInteger[] { 1, 3, 0, 1, 7 }));
        Assert.Equal(new BigInteger[] { -2, 0, 4 }, Proven.Evens(new BigInteger[] { -2, -1, 0, 3, 4 }));
        Assert.Equal((byte)44, Proven.Checksum(new byte[] { 200, 100 }));
    }

    [Fact]
    public void BinarySearchOnALargeArray()
    {
        BigInteger[] sorted = Enumerable.Range(0, 100_000).Select(i => (BigInteger)(2 * i)).ToArray();
        LeanArray<BigInteger> a = sorted;
        Assert.Equal(31_415, Proven.BinarySearch(a, 62_830).Value);
        Assert.False(Proven.BinarySearch(a, 62_831).IsSome);
        Assert.Equal(99_999, Proven.BinarySearch(a, 199_998).Value);
        LeanArray<BigInteger> totals = Proven.RunningTotals(Enumerable.Repeat((BigInteger)1, 200_000).ToArray());
        Assert.Equal(200_000, totals[^1]);   // 200,000 pushes: linear, not quadratic
    }

    [Fact]
    public void LeansArrayLibraryCompiles()
    {
        Assert.Equal(new BigInteger[] { 3, -6 }, Proven.ScaleAll(3, new BigInteger[] { 1, -2 }));
        Assert.Equal(new BigInteger[] { 3, 2, 1 }, Proven.Reversed(new BigInteger[] { 1, 2, 3 }));
        Assert.Empty(Proven.Reversed(new BigInteger[0]));
        Assert.Equal(new BigInteger[] { 0, 1, 4, 9, 16 }, Proven.Squares(5));
        LeanArray<ProdOfIntInt> pairs = Proven.PairUp(new BigInteger[] { 1, 2, 3 }, new BigInteger[] { 10, 20 });
        Assert.Equal(2, pairs.Count);
        Assert.Equal((2, 20), ((int)pairs[1].Fst, (int)pairs[1].Snd));
        Assert.True(Proven.AnyOver(10, new BigInteger[] { 3, 11 }));
        Assert.False(Proven.AnyOver(10, new BigInteger[] { 3, 10 }));
        Assert.Equal(20, Proven.ItemAt(new BigInteger[] { 10, 20 }, 1).Value);
        Assert.False(Proven.ItemAt(new BigInteger[] { 10, 20 }, 2).IsSome);
    }

    [Fact]
    public void GeneratedTypesPrintAndCompareLikeRecords()
    {
        Tree t = Proven.OfList(new BigInteger[] { 2, 1 });
        Assert.Equal("Node { Left = Node { Left = Leaf, Key = 1, Right = Leaf }, Key = 2, Right = Leaf }", t.ToString());
        Assert.Equal(t, Proven.OfList(new BigInteger[] { 2, 1 }));
        Assert.NotEqual(t, Proven.OfList(new BigInteger[] { 1, 2 }));
        Assert.Equal(t.GetHashCode(), Proven.OfList(new BigInteger[] { 2, 1 }).GetHashCode());
        Assert.Equal("Error { Message = \"cannot divide 7 by zero\" }", Proven.SafeDiv(7, 0).ToString());
        Assert.Equal(new Arith.Num(5), Proven.Fold(new Arith.Add(new Arith.Num(2), new Arith.Num(3))));
        Assert.Equal("PairOfIntInt { First = -1, Second = 8 }", Proven.MinMax(new BigInteger[] { 3, -1, 8 }).Value.ToString());
    }

    [Fact]
    public void ParametersHaveNamesACallerCanUse()
    {
        string Names(string method) => string.Join(",", typeof(Proven).GetMethod(method)!.GetParameters().Select(p => p.Name));
        Assert.Equal("k,tree", Names(nameof(Proven.Contains)));
        Assert.Equal("env,arith", Names(nameof(Proven.Eval)));
        Assert.Equal("items", Names(nameof(Proven.Total)));
        Assert.Equal("n", Names(nameof(Proven.SumTo)));
        Assert.True(Proven.Contains(k: 1, tree: Proven.OfList(new BigInteger[] { 1 })));
    }
}
