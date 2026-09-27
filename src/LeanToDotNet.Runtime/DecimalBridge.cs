using System.Numerics;

namespace LeanToDotNet.Runtime;

/// <summary>
/// Moves a <see cref="decimal"/> in and out of a Lean structure shaped like one: an <c>Int</c> mantissa and a
/// <c>Nat</c> scale, the value being <c>mantissa × 10^-scale</c>. This is the one piece of the path from a caller
/// to a proved function that the proofs do not cover, so it is kept small and tested on its own: every
/// <c>decimal</c> splits and joins back to itself, scale included.
/// </summary>
public static class DecimalBridge
{
    private static readonly BigInteger MaxMantissa = (BigInteger.One << 96) - 1;

    /// <summary>The mantissa of <paramref name="value"/>, sign included: <c>2.675m</c> gives <c>2675</c>.</summary>
    public static BigInteger Mantissa(decimal value)
    {
        Span<int> bits = stackalloc int[4];
        decimal.GetBits(value, bits);
        BigInteger m = ((BigInteger)(uint)bits[2] << 64) | ((BigInteger)(uint)bits[1] << 32) | (uint)bits[0];
        return bits[3] < 0 ? -m : m;
    }

    /// <summary>The scale of <paramref name="value"/>, the digits after its point: <c>2.675m</c> gives <c>3</c>.</summary>
    public static BigInteger Scale(decimal value) => value.Scale;

    /// <summary>
    /// The <see cref="decimal"/> with this mantissa and scale. Throws <see cref="OverflowException"/> when the value
    /// has no exact <c>decimal</c> form, a mantissa past 96 bits or a scale past 28, rather than rounding it: a
    /// proved result is never changed on the way out.
    /// </summary>
    public static decimal FromParts(BigInteger mantissa, BigInteger scale)
    {
        if (scale.Sign < 0 || scale > 28)
        {
            throw new OverflowException($"scale {scale} is outside System.Decimal's 0 to 28");
        }
        BigInteger abs = BigInteger.Abs(mantissa);
        if (abs > MaxMantissa)
        {
            throw new OverflowException($"mantissa {mantissa} does not fit in System.Decimal's 96 bits");
        }
        int lo = (int)(uint)(abs & uint.MaxValue);
        int mid = (int)(uint)((abs >> 32) & uint.MaxValue);
        int hi = (int)(uint)((abs >> 64) & uint.MaxValue);
        return new decimal(lo, mid, hi, mantissa.Sign < 0, (byte)(int)scale);
    }
}
