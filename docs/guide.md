# The lean2il guide

Everything about using lean2il: what the pieces are, every option, how Lean maps to .NET, how the docs are
chosen, what compiles, and what each error means. New here? Start with the [tutorial](tutorial.md).

## The pieces

**Lean 4** is a programming language and a proof assistant: you write functions, and you write theorems about
them, and Lean checks the proofs. The part that checks is the *kernel*, a small program that everything else
in Lean rests on. Lean compiles each file to an `.olean`, which holds every definition and theorem as a
*kernel term*, the exact form the kernel checked.

**Tenet** ([github.com/keithadler/tenet](https://github.com/keithadler/tenet)) is a second implementation of
Lean's kernel, written independently in C# on .NET from the type theory, sharing no code with Lean. It reads
`.olean` files and re-checks every declaration from scratch. It checks all of Mathlib, and it rejects a
committed corpus of deliberately broken files, which is how you know it is checking rather than agreeing. The
value of a second kernel is simple: a bug in one checker is unlikely to be the same bug in an independent one,
so a proof both accept is one you can trust a little more. Tenet's own README is candid about the limit: the
*algorithm* follows Lean's on purpose, so a flaw in the kernel's design, rather than its code, is one it
would share.

**lean2il** is this repository's compiler. It uses Tenet twice: as the checker that must accept the project
before anything is emitted, and as the reader that decodes the `.olean` files into kernel terms, which it then
compiles to .NET IL.

**LeanToDotNet.Runtime** is the small library the emitted assembly calls: Lean's `Nat` and `Int` arithmetic on
`BigInteger`, with Lean's meaning, and the exact conversion between a Lean decimal structure and
`System.Decimal`.

**LeanViz** ([github.com/keithadler/leanviz](https://github.com/keithadler/leanviz)) is a browsable site of a
Lean project's declarations, also built on Tenet. The generated docs can link each theorem to its LeanViz page.

## Getting the dependencies

| What | How | Notes |
|---|---|---|
| Lean 4 | `./setup.sh` installs [elan](https://github.com/leanprover/elan) | Each project's `lean-toolchain` picks the version; elan downloads it on first use. |
| .NET 10 SDK | `./setup.sh` runs Microsoft's `dotnet-install.sh` into `~/.dotnet` | Or install it from [dot.net](https://dot.net). |
| Tenet (the library) | nothing | `lean2il` references `Tenet.Olean` 0.11.1 from nuget.org; `dotnet` restores it. |
| Tenet (the `tenet` command) | `dotnet tool restore` | Pinned in [`dotnet-tools.json`](../dotnet-tools.json). Use it to re-check or audit a project on its own: `dotnet tenet check lean --all`. |
| lean2il (the command) | `./setup.sh`, or `dotnet tool update -g lean2il --add-source ./artifacts` after `./build.sh` | A .NET global tool in `~/.dotnet/tools`. |
| The VS Code extension | the [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=keithadler.lean-to-dot-net), or `code --install-extension keithadler.lean-to-dot-net` | It bundles lean2il and Tenet: with it, you need only the .NET 10 runtime and Lean. |

On Windows, `setup.ps1` does the same as `setup.sh`.

## Command line

```
lean2il <lake-project> [options]
```

| Option | Default | |
|---|---|---|
| `--out <dir>` | `<project>/.lake/dotnet` | Where the assembly and its docs go. |
| `--assembly <name>` | `<Namespace>.Proven` | The assembly name. |
| `--namespace <ns>` | the namespace every export shares | The Lean namespace to strip from method names, and the .NET namespace. |
| `--class <name>` | `Proven` | The static class holding the exported functions. |
| `--trust-imports` | off | Re-check only the project's own modules, not Lean's library under them. Seconds instead of a minute or two. |
| `--no-check` | off | Skip Tenet. The docs and `ProvenInfo.Verdict` then say the proofs were not re-checked. |
| `--leanviz <url>` | none | A LeanViz site for the project; theorem names in the docs link there. |
| `--source <url>` | none | Base URL of the Lean sources; each theorem links to its lines. |

The project must be built (`lake build`) first. lean2il reads `.lake/build/lib/lean`, and the `.olean` files of
any Lake dependencies under `.lake/packages`.

## What you get

| File | |
|---|---|
| `<Assembly>.dll` | The compiled functions, the types they use, and `ProvenInfo`. |
| `LeanToDotNet.Runtime.dll` | The runtime it calls. Reference both. |
| `<Assembly>.xml` | IntelliSense: summaries, parameters, remarks listing the theorems, examples. |
| `<Assembly>.md` | The same as a page to read: how to reference it, each method, its examples and theorems, the types. |
| `<Assembly>.proof.json` | Machine-readable: functions, signatures, theorems with statements and axioms, examples, the verdict. |

## From Lean to .NET

| Lean | .NET |
|---|---|
| `Nat` | `BigInteger`, never negative; a negative argument throws `ArgumentOutOfRangeException` |
| `Int` | `BigInteger` |
| `Bool`, `Decidable p` | `bool` (a `Decidable` keeps its answer and drops its proof) |
| an inductive whose constructors take no arguments | a .NET `enum`, cases in the same order |
| a structure | a sealed class with a constructor and one public read-only field per field |
| a structure of an `Int` and then a `Nat` | also accepted and returned as `decimal`, through an overload |
| types, type-class instances, proofs | erased: they are not parameters at all |

Names: `Finance.RoundingMode` becomes the type `Finance.RoundingMode`; its constructor `toEven` becomes
`ToEven`. An exported `Finance.roundCents` becomes the method `Finance.Proven.RoundCents`: the namespace is
stripped and the rest is PascalCased.

### The decimal overload

When an export takes or returns a structure shaped like a decimal (two fields at run time, an `Int` and then a
`Nat`, read as mantissa and scale), lean2il emits a second overload with `decimal` in its place and `int` in
place of each `Nat`, so

```lean
def round (x : Dec) (digits : Nat) (mode : RoundingMode) : Dec
```

is callable both as `Dec Round(Dec x, BigInteger digits, RoundingMode mode)`, exact and unbounded, and as
`decimal Round(decimal x, int digits, RoundingMode mode)`. The conversion is exact both ways; a result with no
`decimal` form (a mantissa past 96 bits, a scale past 28) throws `OverflowException` rather than being rounded.

## How the docs are chosen

Everything comes from the `.olean`, the file the proofs are in:

- **A definition's docstring** is its method's summary.
- **Theorems with docstrings** that mention a definition are listed in its remarks, with the statement
  (printed by LeanViz's printer), the axioms under it, and links. A theorem without a docstring is left out.
- **Proved examples**: a documented theorem of the form `f a b = c` whose arguments and result are literals
  becomes a C# example. Before the docs are written, lean2il calls `f` on the new assembly, through both
  overloads if there are two, and fails the build if the answer is not `c`.
- **Field and constructor docstrings** document the .NET fields and enum members.
- **The module docstring** (`/-! ... -/`) introduces the Markdown page.

## What compiles

Non-recursive definitions over the types in the table above; `if`, `match`, `let`, and anything built from
them; instances, numerals and coercions (unfolded at compile time); calls between exports; `Nat` and `Int`
arithmetic including Lean's division, modulo, power, gcd, shifts and bitwise operations.

Not yet, and refused with a message rather than compiled wrong:

| Refused | Message |
|---|---|
| recursion | `it is defined by structural recursion (Nat.brecOn)` or `well-founded recursion` |
| a function as a value | `a function value would be needed at run time` |
| `String`, `Float`, `Array`, `List` | `no run-time form for the type ...` |
| inductives with parameters, indices or recursive fields | `the type X is not compiled: it is recursive` (or has parameters, or indices) |
| types from outside the project | `only types declared in the compiled project become .NET types` |
| `partial` and `unsafe` definitions | `is partial or unsafe; lean2il compiles only what the kernel checked` |
| `opaque` and axioms | `is opaque; its value cannot be compiled` |

## Errors

| Message | Meaning |
|---|---|
| `... does not exist; run lake build` | The project has not been built. |
| `cannot find module 'X'` | The `.olean` files are stale; `lake build` again. |
| `Tenet rejected the project; nothing was emitted` | A declaration failed the independent check. Each rejected one is listed with Tenet's reason. Take it seriously. |
| `nothing is marked @[export]` | Mark at least one definition. |
| `the IL disagrees with <theorem>` | A proved example returned something else on the compiled assembly. This is a lean2il bug: please open an issue with the Lean. |

In VS Code, all of these land in the Problems panel on the line they are about.

## What this rests on

The proofs rest on Lean's kernel and, independently, Tenet's, and on the axioms listed next to each theorem.
The IL rests on lean2il's translation, which is not proved; it is tested, on every build by the replayed
examples, and in the test suite by comparing the runtime with Lean's own `#eval` output and the compiled
rounding with `Math.Round(decimal)` on 300,000 inputs. The `decimal` bridge is the one piece between a caller
and a proved function that the proofs cannot see, so it is small, exact, and tested to round-trip every
`decimal` it is given.
