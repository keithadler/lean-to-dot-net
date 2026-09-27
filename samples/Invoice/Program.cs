using Finance;

// Three ways finance code rounds money wrong in .NET, and the same lines through a function proved in Lean.

Console.WriteLine("Three rounding bugs, and the proved fix");
Console.WriteLine();
Row("what the code does", "input", "bug", "proved", "why");
Console.WriteLine(new string('-', 104));

// 1. Math.Round with no mode is banker's rounding.
Row("Math.Round(x, 2)", "0.125", Math.Round(0.125m, 2), Proven.Round(0.125m, 2, RoundingMode.AwayFromZero),
    "the default mode is ToEven");

// 2. double cannot hold the midpoint.
Row("Math.Round((double)x, 2, AwayFromZero)", "1.005", (decimal)Math.Round(1.005, 2, MidpointRounding.AwayFromZero),
    Proven.Round(1.005m, 2, RoundingMode.AwayFromZero), "1.005 is 1.00499999... as a double");

// 3. The hand-rolled fix is not symmetric.
Row("Math.Floor(x * 100 + 0.5m) / 100", "-2.675", Math.Floor(-2.675m * 100 + 0.5m) / 100,
    Proven.Round(-2.675m, 2, RoundingMode.AwayFromZero), "a refund comes out a cent short");

Console.WriteLine();
Console.WriteLine("An invoice, rounded per line with Proven.RoundCents:");
decimal[] lines = [19.995m, 4.125m, 0.005m, -2.675m];
foreach (decimal l in lines)
{
    Console.WriteLine($"  {l,10} -> {Proven.RoundCents(l),8}");
}
Console.WriteLine();
Console.WriteLine("Splitting a $100.00 bill three ways:");
Console.WriteLine($"  total / 3 each:        {3 * Math.Round(100.00m / 3, 2),8}   a cent short");
var shares = Proven.SplitEven(10000, 3);
Console.WriteLine($"  Proven.SplitEven:      {string.Join(" + ", shares.Select(c => (decimal)c / 100m))} = {shares.Aggregate(System.Numerics.BigInteger.Zero, (a, b) => a + b) / 100}.00, proved to add up");
Console.WriteLine();
Console.WriteLine(ProvenInfo.Verdict);
Console.WriteLine($"{ProvenInfo.Theorems().Length} theorems stand behind this assembly, among them:");
foreach (string t in ProvenInfo.Theorems().Where(t => t.Contains("round_")).Take(5))
{
    Console.WriteLine("  " + t);
}

static void Row(string code, string input, object bug, object proved, string why) =>
    Console.WriteLine($"{code,-40} {input,7} {bug,8} {proved,8}   {why}");
