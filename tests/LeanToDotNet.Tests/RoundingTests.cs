using Finance;
using Xunit;
using Xunit.Abstractions;

namespace LeanToDotNet.Tests;

/// <summary>
/// The compiled Lean against .NET's own decimal rounding. The Lean <c>RoundingMode</c> lists .NET's five
/// <c>MidpointRounding</c> cases in the same order, and the proofs pin down what each one does, so wherever the two
/// agree .NET's decimal rounding has been shown to satisfy those theorems on that input. They should agree on every
/// input: .NET's <c>decimal</c> rounding is correct. The bugs this project is about come from defaults and from
/// <c>double</c>, not from <c>decimal.Round</c>.
/// </summary>
public class RoundingTests(ITestOutputHelper output)
{
    [Fact]
    public void ProvenRoundAgreesWithDecimalRoundEverywhere()
    {
        var rng = new Random(20260926);
        int cases = 0;
        foreach (decimal x in Samples.Decimals(rng, 60_000))
        {
            for (int mode = 0; mode < 5; mode++)
            {
                int digits = rng.Next(0, 29);
                decimal ours = Proven.Round(x, digits, (RoundingMode)mode);
                decimal theirs = Math.Round(x, digits, (MidpointRounding)mode);
                Assert.True(ours == theirs, $"Round({x}, {digits}, {(RoundingMode)mode}): Lean gives {ours}, .NET gives {theirs}");
                cases++;
            }
        }
        output.WriteLine($"{cases:N0} roundings, every one equal to Math.Round(decimal, int, MidpointRounding)");
    }

    [Fact]
    public void TheDefaultIsBankersRounding()
    {
        // The surprise: no mode given means ToEven.
        Assert.Equal(0.12m, Math.Round(0.125m, 2));
        Assert.Equal(0.13m, Proven.Round(0.125m, 2, RoundingMode.AwayFromZero));
        Assert.Equal(0.12m, Proven.Round(0.125m, 2, RoundingMode.ToEven));
    }

    [Fact]
    public void DoubleCannotHoldTheMidpoint()
    {
        // 1.005 as a double is 1.00499999999999989341858963598497211933135986328125.
        Assert.Equal(1.0, Math.Round(1.005, 2, MidpointRounding.AwayFromZero));
        Assert.Equal(1.01m, Proven.Round(1.005m, 2, RoundingMode.AwayFromZero));
    }

    [Fact]
    public void HowOftenDoubleGetsAHalfCentWrong()
    {
        // Every price from 0.005 to 99.995 that ends in a half cent, rounded to cents away from zero.
        int wrong = 0, total = 0;
        for (int halfCents = 1; halfCents < 20_000; halfCents += 2)
        {
            decimal price = halfCents * 0.005m;
            total++;
            decimal right = Proven.Round(price, 2, RoundingMode.AwayFromZero);
            if ((decimal)Math.Round((double)price, 2, MidpointRounding.AwayFromZero) != right)
            {
                wrong++;
            }
        }
        output.WriteLine($"{wrong} of {total} half-cent prices round the wrong way as double on .NET {System.Environment.Version}");
        Assert.Equal(10_000, total);
        Assert.True(wrong > 0);
    }

    [Fact]
    public void TheHandRolledFixBreaksRefunds()
    {
        static decimal FloorHalfUp(decimal x) => Math.Floor(x * 100 + 0.5m) / 100;
        Assert.Equal(2.68m, FloorHalfUp(2.675m));
        Assert.Equal(-2.67m, FloorHalfUp(-2.675m));   // the refund is a cent short
        Assert.Equal(-2.68m, Proven.Round(-2.675m, 2, RoundingMode.AwayFromZero));
    }

    [Fact]
    public void RoundCentsIsInvoiceRounding()
    {
        Assert.Equal(20.00m, Proven.RoundCents(19.995m));
        Assert.Equal(-20.00m, Proven.RoundCents(-19.995m));
    }

    [Fact]
    public void TheExactOverloadHasNoNinetySixBitLimit()
    {
        var huge = new Dec(System.Numerics.BigInteger.Parse("123456789012345678901234567890123456789125"), 3);
        Dec r = Proven.Round(huge, 2, RoundingMode.AwayFromZero);
        Assert.Equal(System.Numerics.BigInteger.Parse("12345678901234567890123456789012345678913"), r.Mantissa);
        Assert.Equal(2, r.Scale);
    }

    [Fact]
    public void ANegativeDigitCountIsRefused() =>
        Assert.Throws<ArgumentOutOfRangeException>(() => Proven.Round(1.5m, -1, RoundingMode.ToEven));

    [Fact]
    public void ProvenInfoCarriesTheVerdict()
    {
        Assert.Contains("Tenet", ProvenInfo.Verdict);
        Assert.Contains("Finance.round_neg", ProvenInfo.Theorems());
    }
}
