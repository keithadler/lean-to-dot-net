# Lean to .NET for VS Code

The editor side of [lean2il](https://github.com/keithadler/lean-to-dot-net), which compiles Lean 4 definitions
to a .NET assembly after re-checking every proof with [Tenet](https://github.com/keithadler/tenet), an
independent Lean kernel.

- **In Lean**, a CodeLens over each `@[export]` definition gives the C# signature it became, how many theorems
  are proved about it, and how many proved examples were replayed against the IL. A lens over each documented
  theorem names the .NET methods whose docs it appears in.
- **In C#**, every call to a compiled function gets a lens, *proved in Lean, re-checked by Tenet*, that opens the
  Lean definition beside it, and a hover with the signatures, the proved examples and the theorems, each one
  a link to its line.
- **The status bar** shows the assembly and Tenet's verdict. Click it for the generated API docs.
- **Lean to .NET: Build .NET Assembly** runs `lake build` and `lean2il` in a terminal and reloads everything.

Everything shown comes from the `.proof.json` lean2il writes next to the assembly, so it reflects exactly what the
last build proved.

## Requirements

`lean2il` on the PATH, or a clone of lean-to-dot-net built in the workspace (the extension finds
`src/Lean2Il/bin/Release/net10.0/lean2il.dll`). `./setup.sh` in the repository installs everything, Tenet
included. For Lean syntax, install the official Lean 4 extension too.

## Settings

| Setting | Default | |
|---|---|---|
| `lean2dotnet.lean2ilCommand` | empty | How to run lean2il, when it is not on the PATH. |
| `lean2dotnet.checkImports` | `false` | Also re-check Lean's own library under the project. Slower, strongest. |
| `lean2dotnet.leanvizUrl` | empty | A LeanViz site for the project, for links in the docs. |
