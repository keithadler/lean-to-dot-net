# Changelog

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
