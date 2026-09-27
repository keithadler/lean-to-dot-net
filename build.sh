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

step "lean2il: build the compiler, and pack it as a .NET tool into artifacts/"
dotnet build src/Lean2Il -c Release -v quiet -nologo
dotnet pack src/Lean2Il -c Release -o artifacts -v quiet -nologo

CHECK="--trust-imports"
if [[ "${1:-}" == "--full" ]]; then CHECK=""; fi   # --full: Tenet re-checks Lean's own library too
step "lean2il: re-check with Tenet, emit Finance.Proven.dll and its docs"
dotnet src/Lean2Il/bin/Release/net10.0/lean2il.dll lean $CHECK \
  --leanviz "https://keithadler.github.io/lean-to-dot-net/leanviz/?p=finance" \
  --source "https://github.com/keithadler/lean-to-dot-net/blob/main/lean"
cp lean/.lake/dotnet/Finance.Proven.md docs/Finance.Proven.md

step "Tests: runtime against Lean's own answers, and Proven.Round against Math.Round(decimal)"
dotnet test tests/LeanToDotNet.Tests -c Release -nologo -v quiet

step "Sample: samples/Invoice"
dotnet run --project samples/Invoice -c Release

if command -v npx >/dev/null; then
  step "VS Code extension: vscode/lean-to-dot-net-*.vsix"
  (cd vscode && npx --yes @vscode/vsce@3 package --no-dependencies >/dev/null && ls -1 *.vsix)
fi
