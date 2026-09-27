using System.Numerics;
using LeanToDotNet.Runtime;
using Xunit;

namespace LeanToDotNet.Tests;

/// <summary>
/// The runtime against Lean itself. Every expected value below is Lean 4.33.1's own <c>#eval</c> output, pasted
/// in (the snippet that produced it is in the comment), so the claim tested is "same answer as Lean", not "same
/// answer as I think Lean gives".
/// </summary>
public class RuntimeTests
{
    // #eval for a in [7,-7,6,-6,0,1,-1], b in [2,-2,3,-3,0]: [a, b, a / b, a % b, a.tdiv b, a.tmod b, a.fdiv b, a.fmod b]
    private const string LeanTable = "[7,2,3,1,3,1,3,1],[7,-2,-3,1,-3,1,-4,-1],[7,3,2,1,2,1,2,1],[7,-3,-2,1,-2,1,-3,-2],[7,0,0,7,0,7,0,7],[-7,2,-4,1,-3,-1,-4,1],[-7,-2,4,1,3,-1,3,-1],[-7,3,-3,2,-2,-1,-3,2],[-7,-3,3,2,2,-1,2,-1],[-7,0,0,-7,0,-7,0,-7],[6,2,3,0,3,0,3,0],[6,-2,-3,0,-3,0,-3,0],[6,3,2,0,2,0,2,0],[6,-3,-2,0,-2,0,-2,0],[6,0,0,6,0,6,0,6],[-6,2,-3,0,-3,0,-3,0],[-6,-2,3,0,3,0,3,0],[-6,3,-2,0,-2,0,-2,0],[-6,-3,2,0,2,0,2,0],[-6,0,0,-6,0,-6,0,-6],[0,2,0,0,0,0,0,0],[0,-2,0,0,0,0,0,0],[0,3,0,0,0,0,0,0],[0,-3,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[1,2,0,1,0,1,0,1],[1,-2,0,1,0,1,-1,-1],[1,3,0,1,0,1,0,1],[1,-3,0,1,0,1,-1,-2],[1,0,0,1,0,1,0,1],[-1,2,-1,1,0,-1,-1,1],[-1,-2,1,1,0,-1,0,-1],[-1,3,-1,2,0,-1,-1,2],[-1,-3,1,2,0,-1,0,-1],[-1,0,0,-1,0,-1,0,-1]";

    public static IEnumerable<object[]> Rows() =>
        LeanTable.Trim('[', ']').Split("],[").Select(r => r.Split(',').Select(x => (object)BigInteger.Parse(x)).ToArray());

    [Theory]
    [MemberData(nameof(Rows))]
    public void IntDivisionMatchesLean(BigInteger a, BigInteger b, BigInteger ediv, BigInteger emod, BigInteger tdiv, BigInteger tmod, BigInteger fdiv, BigInteger fmod)
    {
        Assert.Equal(ediv, LeanInt.EDiv(a, b));
        Assert.Equal(emod, LeanInt.EMod(a, b));
        Assert.Equal(tdiv, LeanInt.TDiv(a, b));
        Assert.Equal(tmod, LeanInt.TMod(a, b));
        Assert.Equal(fdiv, LeanInt.FDiv(a, b));
        Assert.Equal(fmod, LeanInt.FMod(a, b));
    }

    // #eval s!"{(3:Nat) - 5} {(7:Nat)/0} {(7:Nat)%0} {(2:Int)^10} {(-2:Int)^3} {Int.toNat (-5)} {Int.natAbs (-5)} {Nat.log2 1000} {Nat.gcd 12 18}"
    //   => "0 0 7 1024 -8 0 5 9 6"
    [Fact]
    public void NatAndIntEdgesMatchLean()
    {
        Assert.Equal(0, LeanNat.Sub(3, 5));
        Assert.Equal(0, LeanNat.Div(7, 0));
        Assert.Equal(7, LeanNat.Mod(7, 0));
        Assert.Equal(1024, LeanInt.Pow(2, 10));
        Assert.Equal(-8, LeanInt.Pow(-2, 3));
        Assert.Equal(0, LeanInt.ToNat(-5));
        Assert.Equal(5, LeanInt.NatAbs(-5));
        Assert.Equal(9, LeanNat.Log2(1000));
        Assert.Equal(6, LeanNat.Gcd(12, 18));
    }

    [Fact]
    public void NegativeNatIsRefused() =>
        Assert.Throws<ArgumentOutOfRangeException>(() => LeanNat.Check(-1, "digits"));

    [Fact]
    public void EveryDecimalSplitsAndJoinsBackToItself()
    {
        var rng = new Random(1);
        foreach (decimal d in Samples.Decimals(rng, 200_000))
        {
            decimal back = DecimalBridge.FromParts(DecimalBridge.Mantissa(d), DecimalBridge.Scale(d));
            Assert.Equal(d, back);
            Assert.Equal(d.Scale, back.Scale);
        }
    }

    [Fact]
    public void AValueWithNoDecimalFormIsRefusedNotRounded()
    {
        Assert.Throws<OverflowException>(() => DecimalBridge.FromParts(BigInteger.One << 96, 0));
        Assert.Throws<OverflowException>(() => DecimalBridge.FromParts(1, 29));
    }
}
