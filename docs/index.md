# Lean to .NET

**Prove a function in Lean 4, call it from C#.** `lean2il` re-checks every proof with
[Tenet](https://github.com/keithadler/tenet), an independent Lean kernel, compiles the definitions you mark to
.NET IL, and writes their documentation from the Lean.

![A C# call to Proven.Round, with the proofs behind it](images/vscode-csharp-hover.png)

- **[Tutorial](tutorial.md)**: from nothing to a proved Lean function called from C#, in about fifteen minutes.
- **[Guide](guide.md)**: what Lean and Tenet are, every option, what compiles, how types map, what each error means.
- **[Finance.Proven API docs](Finance.Proven.md)**: the demo assembly's docs, generated entirely from the Lean.
- **[The proofs in LeanViz](leanviz/?p=finance#/d/Finance.round_neg)**: every declaration, browsable, re-checked by Tenet.
- **[Source on GitHub](https://github.com/keithadler/lean-to-dot-net)**, MIT.
