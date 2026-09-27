## Build the assembly

**Build .NET Assembly** runs `lake build` and then `lean2il`, which:

1. re-checks every declaration with **Tenet**, an independent Lean kernel, and stops if it rejects anything;
2. compiles each `@[export]` definition to IL;
3. writes IntelliSense XML, Markdown docs and a `.proof.json`, and runs every proved example against the new DLL.

Lean errors and lean2il's refusals appear in the Problems panel.
