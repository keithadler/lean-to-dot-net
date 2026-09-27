namespace LeanToDotNet.Tests;

internal static class Samples
{
    /// <summary>
    /// Decimals spread over every scale and size, with midpoints heavily over-represented: a value ending in 5 is
    /// where rounding modes disagree, and a uniform sample would almost never land on one.
    /// </summary>
    public static IEnumerable<decimal> Decimals(Random rng, int count)
    {
        for (int i = 0; i < count; i++)
        {
            byte scale = (byte)rng.Next(0, 29);
            int kind = rng.Next(4);
            int lo = rng.Next(int.MinValue, int.MaxValue);
            int mid = kind >= 2 ? rng.Next(int.MinValue, int.MaxValue) : 0;
            int hi = kind == 3 ? rng.Next(int.MinValue, int.MaxValue) : 0;
            decimal d = new(lo, mid, hi, rng.Next(2) == 0, scale);
            if (rng.Next(3) == 0 && scale > 0)
            {
                // force a midpoint at a random precision: ...d5 followed by zeros
                int keep = rng.Next(0, scale);
                d = Math.Truncate(d * Pow10(keep)) / Pow10(keep) + Math.Sign(d) * 5m / Pow10(keep + 1);
            }
            yield return d;
        }
    }

    private static decimal Pow10(int k)
    {
        decimal p = 1m;
        for (int i = 0; i < k; i++)
        {
            p *= 10m;
        }
        return p;
    }
}
