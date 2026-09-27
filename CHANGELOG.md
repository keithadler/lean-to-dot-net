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
- **Lambdas that use local variables**: `xs.map (fun x => x + k)` compiles to a copy of `List.map` taking `k`.
- **Your own data types**: inductives with data, recursive ones (trees, expression syntax, results), and types
  with parameters, one .NET class per use. `Arith` with a constant folder proved correct, a search tree, a
  `Result`, in the showcase.
- **Fixed-width integers**: `UInt8` ... `UInt64`, `Int8` ... `Int64` as `byte` ... `long`, wrapping, with Lean's
  meaning where C#'s differs (division by zero is zero, shift counts wrap, `MinValue / -1` does not throw).
  The showcase has FNV-1a, a saturating add, and the binary-search midpoint bug with the fix proved in range.
- **Arrays**: `Array α` as `LeanArray<T>` over a .NET array, with constant-time `size`, `a[i]`, `push` and `set`;
  `foldl`, `filter`, `reverse` and the rest compiled from Lean's own definitions over them. `Array.map` and
  `range`, whose definitions go through private helpers, are compiled from restatements Lean proves in the
  equations module and Tenet re-checks.
- `Fin n` and subtypes are held as their value, as in Lean's compiler.
- **A harder demo**: `Finance/Split.lean` splits a bill into shares proved to add up to exactly the total,
  refunds included, and to differ by at most a cent.
- `examples/showcase`, 43 functions compiled and differential-tested on every build; 68 C# tests.
- The differential test turns off Lean's panic backtraces (`LEAN_BACKTRACE=0`); an input that makes Lean's code
  panic now costs microseconds instead of a second.
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
