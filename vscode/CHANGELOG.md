# Changelog

## 0.4.0

- Bundles lean2il 0.3.0: recursive definitions (compiled from the equation lemmas Lean proves for them), lists,
  options, strings and arrays, lambdas that use local variables, your own data types, fixed-width integers, deep
  recursion without stack overflows, and a differential test of every build against Lean's own compiler.
- A refusal that names a parameter ("Finance.half, parameter x: ...") lands on its function's line in the Problems
  panel, like any other.
- The dashboard and the status bar report the differential test; a disagreement lands in the Problems panel on
  the function it names.

## 0.3.0

- **Works out of the box.** lean2il, Tenet and the two .NET reference assemblies they need ship inside the
  extension (1.7 MB), so there is nothing to clone or build, and only the .NET 10 runtime is required, not the SDK.
- **Checks what is missing.** Before a build, it looks for the .NET 10 runtime and Lean, and for either one offers
  a terminal with the official installer's command typed in, or the download page.
- **Says when it is out of date.** After an edit or a failed build, the status bar, the Proofs view, the lenses and
  the dashboard say they show the last successful build.
- **Lenses follow the code.** They are placed by finding the declaration in the current text, so they stay on
  the right line while you edit.
- Unit tests for the parsing and matching (`npm test`); C# calls in line comments are no longer matched.
- The view is titled **Proofs**; marked as a preview while the compiler is 0.x.

## 0.2.0

- The Proofs view in the Activity Bar: assemblies, functions, proved examples and theorems.
- The Proof Dashboard: the verdict, signatures, examples replayed on the IL, theorems with their axioms.
- Builds run in their own terminal; Lean errors, lean2il refusals and Tenet rejections go to the Problems panel.
- `lean2dotnet.buildOnSave`; C# completion after `Proven.`; Lean snippets; a getting-started walkthrough.
- Lenses over proved examples show the call and the value it returned.
- Finds Lean and .NET under `~/.elan` and `~/.dotnet` when VS Code is started from the Dock.

## 0.1.0

First release: CodeLens and hovers in Lean and C#, the Tenet verdict in the status bar, and a build command.
