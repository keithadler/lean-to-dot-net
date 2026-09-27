# Changelog

## 0.3.0 (2026-09-27)

What the review of 0.1 asked for: a bigger fragment and a stronger check on the compiler.

- **Recursion**, structural and well-founded, your own and Lean's library's, compiled from the equation lemmas
  Lean proves (`f.eq_def`), which Tenet re-checks with the project. Tail calls become jumps; deeper recursion is
  rerun on a 1 GB stack instead of crashing the process.
- **Lists, options and strings**: `List α` as `LeanList<T>`, `Option α` as `LeanOption<T>`, `String` as
  `string` with Lean's character counts. Library functions like `List.map`, `foldr`, `sum`, `reverse` and `++`
  compile, specialized to closed function arguments.
- **Differential testing on every build**: each export runs on random inputs through Lean's own compiler and
  through the IL, and the build fails on the first disagreement, naming the input (`--fuzz`, default 100).
- **A harder demo**: `Finance/Split.lean` splits a bill into shares proved to add up to exactly the total,
  refunds included, and to differ by at most a cent.
- `examples/showcase`, compiled and differential-tested on every build; 57 C# tests.
- Fixes: Lean's `'`, `?` and `!` in names become valid .NET names; Lean-internal `_unary` exports are skipped.

## 0.2.0 (2026-09-27)

- The VS Code extension (0.3.0) works out of the box: it bundles lean2il, Tenet and the two .NET reference
  assemblies they need, checks for the .NET 10 runtime and Lean and offers to install what is missing, says when
  it is out of date, and keeps its lenses on the right line while you edit. Unit and integration tests, in CI.
- lean2il needs only the .NET runtime, not the SDK: `System.Runtime` and `System.Runtime.Numerics` reference
  assemblies ship beside it.
- lean2il skips a compiled module whose source file was deleted, instead of compiling code that no longer exists.
- lean2il names recursion as the reason it refuses a recursive definition.

## 0.1.0 (2026-09-26)

First release.

- `lean2il`: re-checks a Lake project with Tenet, compiles `@[export]` definitions from their kernel terms to
  an IL assembly, and writes IntelliSense XML, Markdown and a `.proof.json` from the Lean docstrings and
  theorems. Proved examples are replayed against the IL on every build.
- `LeanToDotNet.Runtime`: Lean's `Nat` and `Int` on `BigInteger`, and exact `System.Decimal` conversion.
- `lean/Finance/Rounding.lean`: rounding on exact decimals for all five `MidpointRounding` modes, with proofs
  of half-unit error, nearest, tie behavior, symmetry and idempotence.
- The Invoice sample, the test suite (300,000 comparisons with `Math.Round(decimal)`), and the VS Code
  extension (`vscode/`, packaged as a VSIX).
