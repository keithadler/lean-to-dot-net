using System.Numerics;
using Finance;
using Xunit;
using Xunit.Abstractions;

namespace LeanToDotNet.Tests;

/// <summary>
/// The split, from C#. The theorems already say the shares add up and differ by at most a cent; these check that
/// the compiled code says so too, on inputs nobody wrote a theorem about, including a hundred thousand shares.
/// </summary>
public class SplitTests(ITestOutputHelper output)
{
    [Fact]
    public void TheProvedExamples()
    {
        Assert.Equal(new BigInteger[] { 3334, 3333, 3333 }, Proven.SplitEven(10000, 3));
        Assert.Equal(new BigInteger[] { -3333, -3333, -3334 }, Proven.SplitEven(-10000, 3));
        Assert.Empty(Proven.SplitEven(500, 0));
    }

    [Fact]
    public void SharesAlwaysAddUpAndDifferByAtMostACent()
    {
        var rng = new Random(7);
        int cases = 0;
        for (int i = 0; i < 20_000; i++)
        {
            BigInteger total = new BigInteger(rng.NextInt64(-10_000_000_000, 10_000_000_000));
            int n = rng.Next(1, 60);
            var shares = Proven.SplitEven(total, n);
            Assert.Equal(n, shares.Count);
            Assert.Equal(total, shares.Aggregate(BigInteger.Zero, (a, b) => a + b));
            Assert.True(shares.Max() - shares.Min() <= 1);
            cases++;
        }
        output.WriteLine($"{cases:N0} random bills split; every one added up to its total");
    }

    [Fact]
    public void AHundredThousandSharesDoNotOverflowTheStack()
    {
        // splitAux is not tail recursive: this needs the rerun on a big stack.
        var shares = Proven.SplitEven(10_000_000, 100_000);
        Assert.Equal(100_000, shares.Count);
        Assert.All(shares, s => Assert.Equal(100, s));
    }
}
