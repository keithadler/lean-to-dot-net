#!/usr/bin/env bash
# Everything, in order: the Lean proofs, lean2il, the assembly it emits, the tests, the sample, the VSIX.
# Run ./setup.sh once first if elan or the .NET 10 SDK is missing.
set -euo pipefail
cd "$(dirname "$0")"

step() { printf '\n\033[1m== %s\033[0m\n' "$*"; }

step "Lean: build the proofs (lake build)"
(cd lean && lake build)

step "Tools: restore Tenet (pinned in dotnet-tools.json)"
dotnet tool restore

step "lean2il: build the compiler; pack it, the runtime and the MSBuild package into artifacts/"
dotnet build src/Lean2Il -c Release -v quiet -nologo
for p in src/Lean2Il src/LeanToDotNet.Runtime src/LeanToDotNet.Build; do
  dotnet pack "$p" -c Release -o artifacts -v quiet -nologo
done

CHECK="--trust-imports"
if [[ "${1:-}" == "--full" ]]; then CHECK=""; fi   # --full: Tenet re-checks Lean's own library too
step "lean2il: re-check with Tenet, emit Finance.Proven.dll and its docs"
dotnet src/Lean2Il/bin/Release/net10.0/lean2il.dll lean $CHECK \
  --leanviz "https://keithadler.github.io/lean-to-dot-net/leanviz/?p=finance" \
  --source "https://github.com/keithadler/lean-to-dot-net/blob/main/lean"
cp lean/.lake/dotnet/Finance.Proven.md docs/Finance.Proven.md

step "Showcase: recursion, lists, options and strings (examples/showcase)"
(cd examples/showcase && lake build)
dotnet src/Lean2Il/bin/Release/net10.0/lean2il.dll examples/showcase $CHECK

step "Tests: runtime against Lean's own answers, Proven.Round against Math.Round(decimal), the split, the showcase"
dotnet test tests/LeanToDotNet.Tests -c Release -nologo -v quiet

step "Sample: samples/Invoice"
dotnet run --project samples/Invoice -c Release

step "Packages: a new project using LeanToDotNet.Build from artifacts/ (tests/package-smoke.sh)"
tests/package-smoke.sh

if command -v npm >/dev/null; then
  step "VS Code extension: unit tests, then vscode/lean-to-dot-net-*.vsix with lean2il bundled"
  (cd vscode && npm ci --no-fund --no-audit >/dev/null && npm test 2>&1 | grep -E '^ℹ (pass|fail)' && npm run package >/dev/null && ls -1 *.vsix)
fi
