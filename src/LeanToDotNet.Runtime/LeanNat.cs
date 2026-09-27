using System.Numerics;

namespace LeanToDotNet.Runtime;

/// <summary>
/// Lean's <c>Nat</c> operations on <see cref="BigInteger"/>, with Lean's meaning rather than C#'s: subtraction stops
/// at zero, and dividing by zero gives zero. A compiled assembly calls these in place of the kernel's definitions;
/// the table in lean2il's <c>Primitives.cs</c> says which Lean constant each one stands for.
/// </summary>
public static class LeanNat
{
    /// <summary><c>Nat.sub</c>: truncated, so <c>3 - 5 = 0</c>.</summary>
    public static BigInteger Sub(BigInteger a, BigInteger b) => a >= b ? a - b : BigInteger.Zero;

    /// <summary><c>Nat.div</c>: <c>n / 0 = 0</c>.</summary>
    public static BigInteger Div(BigInteger a, BigInteger b) => b.IsZero ? BigInteger.Zero : a / b;

    /// <summary><c>Nat.mod</c>: <c>n % 0 = n</c>.</summary>
    public static BigInteger Mod(BigInteger a, BigInteger b) => b.IsZero ? a : a % b;

    /// <summary><c>Nat.pow</c>.</summary>
    public static BigInteger Pow(BigInteger a, BigInteger b) =>
        b > int.MaxValue ? throw new OverflowException($"exponent {b} is too large to compute") : BigInteger.Pow(a, (int)b);

    /// <summary><c>Nat.pred</c>: <c>pred 0 = 0</c>.</summary>
    public static BigInteger Pred(BigInteger a) => a.IsZero ? BigInteger.Zero : a - 1;

    /// <summary><c>Nat.gcd</c>.</summary>
    public static BigInteger Gcd(BigInteger a, BigInteger b) => BigInteger.GreatestCommonDivisor(a, b);

    /// <summary><c>Nat.log2</c>: <c>log2 0 = 0</c>.</summary>
    public static BigInteger Log2(BigInteger a) => a <= 1 ? BigInteger.Zero : (BigInteger)(long)BigInteger.Log2(a);

    /// <summary><c>Nat.shiftLeft</c>.</summary>
    public static BigInteger ShiftLeft(BigInteger a, BigInteger b) => a << checked((int)b);

    /// <summary><c>Nat.shiftRight</c>.</summary>
    public static BigInteger ShiftRight(BigInteger a, BigInteger b) => b > int.MaxValue ? BigInteger.Zero : a >> (int)b;

    /// <summary><c>Nat.repr</c>: decimal digits, no separators, whatever the culture.</summary>
    public static string Repr(BigInteger n) => n.ToString(System.Globalization.CultureInfo.InvariantCulture);

    /// <summary>
    /// The guard every public entry point puts on a <c>Nat</c> argument: .NET has no unsigned big integer, so a
    /// negative value is refused here rather than given a meaning Lean never proved anything about.
    /// </summary>
    public static BigInteger Check(BigInteger value, string parameter) =>
        value.Sign < 0 ? throw new ArgumentOutOfRangeException(parameter, value, "A Lean Nat cannot be negative.") : value;
}

/// <summary>
/// Lean's <c>Int</c> operations on <see cref="BigInteger"/>. Lean's <c>/</c> and <c>%</c> on <c>Int</c> are Euclidean
/// (the remainder is never negative), where C#'s truncate toward zero, so these are not the operators.
/// </summary>
public static class LeanInt
{
    /// <summary><c>Int.ediv</c>, which is Lean's <c>/</c>: <c>-7 / 2 = -4</c>, and <c>x / 0 = 0</c>.</summary>
    public static BigInteger EDiv(BigInteger a, BigInteger b)
    {
        if (b.IsZero)
        {
            return BigInteger.Zero;
        }
        BigInteger q = BigInteger.DivRem(a, b, out BigInteger r);
        if (r.Sign < 0)
        {
            q = b.Sign > 0 ? q - 1 : q + 1;
        }
        return q;
    }

    /// <summary><c>Int.emod</c>, which is Lean's <c>%</c>: never negative, and <c>x % 0 = x</c>.</summary>
    public static BigInteger EMod(BigInteger a, BigInteger b)
    {
        if (b.IsZero)
        {
            return a;
        }
        BigInteger r = BigInteger.Remainder(a, b);
        return r.Sign < 0 ? r + BigInteger.Abs(b) : r;
    }

    /// <summary><c>Int.tdiv</c>: truncating, as C# does; <c>x / 0 = 0</c>.</summary>
    public static BigInteger TDiv(BigInteger a, BigInteger b) => b.IsZero ? BigInteger.Zero : BigInteger.Divide(a, b);

    /// <summary><c>Int.tmod</c>: the sign of the dividend, as C# does; <c>x % 0 = x</c>.</summary>
    public static BigInteger TMod(BigInteger a, BigInteger b) => b.IsZero ? a : BigInteger.Remainder(a, b);

    /// <summary><c>Int.fdiv</c>: rounding toward negative infinity; <c>x / 0 = 0</c>.</summary>
    public static BigInteger FDiv(BigInteger a, BigInteger b)
    {
        if (b.IsZero)
        {
            return BigInteger.Zero;
        }
        BigInteger q = BigInteger.DivRem(a, b, out BigInteger r);
        return !r.IsZero && (r.Sign < 0) != (b.Sign < 0) ? q - 1 : q;
    }

    /// <summary><c>Int.fmod</c>: the sign of the divisor; <c>x % 0 = x</c>.</summary>
    public static BigInteger FMod(BigInteger a, BigInteger b) => b.IsZero ? a : a - b * FDiv(a, b);

    /// <summary><c>Int.natAbs</c>.</summary>
    public static BigInteger NatAbs(BigInteger a) => BigInteger.Abs(a);

    /// <summary><c>Int.toNat</c>: negative values become zero.</summary>
    public static BigInteger ToNat(BigInteger a) => a.Sign < 0 ? BigInteger.Zero : a;

    /// <summary><c>Int.negSucc n</c>, which is <c>-(n + 1)</c>.</summary>
    public static BigInteger NegSucc(BigInteger n) => -(n + 1);

    /// <summary><c>Int.repr</c>: <c>-5</c>, <c>0</c>, <c>12</c>.</summary>
    public static string Repr(BigInteger n) => n.ToString(System.Globalization.CultureInfo.InvariantCulture);

    /// <summary><c>Int.pow</c>: an <c>Int</c> to a <c>Nat</c> power.</summary>
    public static BigInteger Pow(BigInteger a, BigInteger b) => (b > int.MaxValue
        ? throw new OverflowException($"exponent {b} is too large to compute") : BigInteger.Pow(a, (int)b));
}
