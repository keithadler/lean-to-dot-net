# Contributing

Issues and pull requests are welcome.

## Build and test

```bash
./setup.sh        # once: installs elan and the .NET 10 SDK if they are missing, then builds
./build.sh        # proofs, lean2il, the assembly, tests, sample, VSIX
./build.sh --full # the same, with Tenet re-checking Lean's own library too
```

## Ground rules

- **Nothing is emitted from a project Tenet rejects.** Keep it that way.
- **A new primitive needs Lean's own answer.** Every entry in `src/Lean2Il/Primitives.cs` claims a Lean
  constant means a .NET operation. Add its expected values to `tests/LeanToDotNet.Tests/RuntimeTests.cs`
  from Lean's `#eval`, pasted in with the snippet that produced them.
- **Refuse rather than guess.** When the compiler meets something it does not handle, it throws a
  `CompileError` that says what and why. A wrong assembly is worse than none.
- **The docs come from the Lean.** Improve a doc by improving the docstring or the theorem, not the generator's
  output.
- US English in code, comments and docs.
