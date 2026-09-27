## Install Lean and .NET

The extension brings its own compiler, **lean2il**, and **Tenet**, the independent Lean kernel it uses. Two
things have to be on the machine:

- **The .NET 10 runtime** (the SDK includes it). To call the result from C#, F# or VB.NET you want the SDK anyway.
- **Lean 4**, through [elan](https://github.com/leanprover/elan), Lean's version manager. Each project's
  `lean-toolchain` file picks the exact Lean version.

The first time you build, the extension checks for both. If one is missing it says which, and offers a
terminal with the official installer's command typed in: press Enter to run it.

It runs on macOS, Linux and Windows.
