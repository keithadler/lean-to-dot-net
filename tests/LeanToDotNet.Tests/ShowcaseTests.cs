using System.Numerics;
using LeanToDotNet.Runtime;
using Showcase;
using Xunit;

namespace LeanToDotNet.Tests;

/// <summary>Recursion, lists, options and strings, as a C# caller sees them.</summary>
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
}
