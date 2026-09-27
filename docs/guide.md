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
| The VS Code extension | the [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=keithadler.lean-to-dot-net) or, for Cursor, Windsurf and VSCodium, [Open VSX](https://open-vsx.org/extension/keithadler/lean-to-dot-net); or `code --install-extension keithadler.lean-to-dot-net` | It bundles lean2il and Tenet: with it, you need only the .NET 10 runtime and Lean. |

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
| `--fuzz <n>` | `100` | Random inputs per export, run by Lean's own compiler and by the IL, which must agree. `0` skips it. |
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
| `String` | `string`; `String.length` counts characters (code points), as Lean does, not UTF-16 units |
| `List α` | `LeanList<T>`: immutable, singly linked, an `IReadOnlyList<T>`; an array converts to one implicitly |
| `Option α` | `LeanOption<T>`: `IsSome`, `Value`, `None`, `Some(x)` |
| `Array α` | `LeanArray<T>`: an `IReadOnlyList<T>` over a .NET array; a `T[]` converts to one implicitly |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | `byte`, `ushort`, `uint`, `ulong` |
| `Int8`, `Int16`, `Int32`, `Int64` | `sbyte`, `short`, `int`, `long` |
| an inductive whose constructors take no arguments | a .NET `enum`, cases in the same order |
| a structure | a sealed class with a constructor and one public read-only field per field |
| any other inductive: several constructors with data, or recursive | an abstract class with an `int Tag`, and a sealed nested class per constructor: `new Arith.Add(new Arith.Num(2), new Arith.Var(0))` |
| a type with parameters | one class per instantiation: `Pair Int String` is `PairOfIntString`, `Int × Int` is `ProdOfIntInt` |
| `Fin n`, a subtype `{x // p x}` | the value alone, as Lean's compiler does: `BigInteger`, or the type of `x`. A caller passing one in keeps the promise the proof made; the differential test skips such functions |
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

## Recursion

Lean elaborates a recursive definition into a term built on `brecOn` (structural recursion) or `WellFounded.fix`
(well-founded recursion). Neither is something to run. But Lean proves, for every recursive `f`, an equation
lemma `f.eq_def : ∀ xs, f xs = rhs`, where `rhs` is the body as you wrote it, calling `f` directly.

lean2il finds every recursive definition the exports reach (Lean marks them by also emitting `f._unsafe_rec`),
writes a small module, `.lake/lean2il/Lean2IlEqns.lean`, that asks Lean for each `eq_def`, and has Lean compile
it. Tenet re-checks that module with the rest of the project, and each recursive method is compiled from its
equation's right-hand side, where a recursive call is an ordinary call. So the IL computes something both kernels
agree equals `f`. The same goes for Lean's library: `List.map`, `List.foldr`, `List.length`, `List.reverse`,
`List.append`.

At run time:

- A call to itself in **tail position** becomes a jump: `gcd`, loops and accumulators run in constant stack.
- Any other recursion checks, before each call, that the stack has room. When it does not, the call throws, the
  exception unwinds, and the public method runs the whole call again on a thread with a 1 GB stack. Rerunning is
  safe because a compiled Lean function has no side effects. `sumTo 200000`, which is not tail recursive, returns
  in about 20 ms.
- A helper used at two different types, or with two different function arguments, is two methods.

## What compiles

Definitions over the types in the table above, with `if`, `match`, `let`, and anything built from them;
instances, numerals and coercions (unfolded at compile time); recursion, as above; calls between exports; `Nat`
and `Int` arithmetic including Lean's division, modulo, power, gcd, shifts and bitwise operations; string
concatenation, length, equality, and `toString` of numbers.

A **function argument** compiles by specializing the function it is passed to, as a C++ template would be.
When the lambda uses local variables, they become extra parameters of the copy: `xs.map (fun x => x + k)`
calls a `List.map` that takes `k`. So `xs.sum`, `xs.filter (fun x => lo < x && x < hi)` and
`xs.foldl (fun acc x => acc + min x cap) 0` all compile to direct calls, with no delegate.

### Fixed-width integers

`UInt8` ... `UInt64` and `Int8` ... `Int64` are the .NET integers of the same width and sign, so a C# caller
passes and gets ordinary `byte`, `int`, `ulong`. Arithmetic wraps, as C#'s unchecked arithmetic does. Where Lean
and C# disagree, the compiled code does what Lean does:

| | Lean, and the compiled code | C# |
|---|---|---|
| `x / 0` | `0` | throws `DivideByZeroException` |
| `x % 0` | `x` | throws |
| `Int32.MinValue / -1` | `Int32.MinValue` | throws `OverflowException` |
| `(1 : UInt8) <<< 9` | `2`: the count wraps around the width | `0` |
| `Int8` shift by `-1` | a shift by `7` | a shift by `31` after promotion |

Conversions between widths (`x.toUInt32`, `x.toInt64`) wrap or sign-extend like C#'s casts, `toNat` and `toInt`
give a `BigInteger`, and `ofNat`/`ofInt` keep the low bits. Numerals are folded at compile time.

### Arrays

`Array α` is a `LeanArray<T>`, backed by a .NET array. `a.size`, `a[i]`, `a[i]!`, `a.push x`, `a.set i x` and
`a.set! i x` are the array's own constant-time operations; the rest of the library (`foldl`, `filter`, `append`,
`reverse`, `contains`, `any`, `zip`) is compiled from Lean's own recursive definitions over them.

`Array.map`, `mapIdx` and `range` are defined through `private` helpers, whose equation lemmas cannot be named from
outside Lean's library. For those, the equations module states a restatement over lists, such as
`Array.map = fun f xs => (xs.toList.map f).toArray`, Lean proves it, Tenet re-checks the proof, and lean2il
compiles the right-hand side. The table of restatements is `Equations.Replacements`; nothing is replaced without
a proof. Lean updates an array
in place when nothing else holds it; compiled code cannot know that, so arrays share a buffer and `push` onto
the newest array writes into its spare room. Building an array by pushing is linear, as in Lean. `set` copies,
so a loop that sets every element is quadratic; build with `push` where you can.

Not yet, and refused with a message rather than compiled wrong:

| Refused | Message |
|---|---|
| a function stored or returned as a value | `a function value would be needed at run time` |
| `Float`, `Char` and other types without a mapping | `no run-time form for the type ...` |
| inductives with indices, mutual inductives, a type nested in itself (`children : List Tree`) | `the type X is not compiled: it has indices` (or is mutually inductive, or contains itself inside another type) |
| types from outside the project, other than the built-in ones above | `only types declared in the compiled project become .NET types` |
| a recursive definition Lean gives no equation lemma for | `is recursive and Lean gave no equation lemma for it` |
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
| `the IL disagrees with Lean's own compiler on <function> <input>` | The differential test found an input where Lean and the IL give different answers. Also a lean2il bug, with the input to reproduce it. |
| `Lean gave no equation lemma for X` | Lean could not state `X.eq_def`; anything that needs `X` is refused. |

In VS Code, all of these land in the Problems panel on the line they are about.

## What this rests on

The proofs rest on Lean's kernel and, independently, Tenet's, and on the axioms listed next to each theorem;
recursive functions also rest on their equation lemmas, which both kernels check. The IL rests on lean2il's
translation, which is not proved; it is tested on every build by the replayed examples and by the differential
test against Lean's own compiler, and in the test suite by comparing the runtime with Lean's own `#eval` output
and the compiled rounding with `Math.Round(decimal)` on 300,000 inputs. The `decimal` bridge is the one piece between a caller
and a proved function that the proofs cannot see, so it is small, exact, and tested to round-trip every
`decimal` it is given.
