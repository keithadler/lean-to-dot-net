#!/usr/bin/env bash
# Install what lean-to-dot-net needs, if it is missing, then build everything.
#
#   elan and Lean     from the official installer (https://github.com/leanprover/elan); the project's
#                     lean-toolchain file then picks the exact Lean version on first use
#   .NET 10 SDK       from Microsoft's official dotnet-install script, into ~/.dotnet
#   Tenet             nothing to do: it is a NuGet package (Tenet.Olean) and a pinned local tool
#                     (dotnet-tools.json), both fetched by `dotnet` on first build
#
# Nothing is installed system-wide and nothing is installed without saying so first.
set -euo pipefail
cd "$(dirname "$0")"

say() { printf '\033[1m%s\033[0m\n' "$*"; }

if ! command -v lake >/dev/null && [[ ! -x "$HOME/.elan/bin/lake" ]]; then
  say "Lean is missing: installing elan (the Lean version manager) into ~/.elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

need_dotnet=1
if command -v dotnet >/dev/null && dotnet --list-sdks | grep -q '^10\.'; then need_dotnet=0; fi
if [[ -x "$HOME/.dotnet/dotnet" ]] && "$HOME/.dotnet/dotnet" --list-sdks | grep -q '^10\.'; then
  export DOTNET_ROOT="$HOME/.dotnet" PATH="$HOME/.dotnet:$PATH"; need_dotnet=0
fi
if [[ $need_dotnet == 1 ]]; then
  say "The .NET 10 SDK is missing: installing it into ~/.dotnet with Microsoft's dotnet-install.sh"
  curl -sSfL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh
  bash /tmp/dotnet-install.sh --channel 10.0 --install-dir "$HOME/.dotnet"
  export DOTNET_ROOT="$HOME/.dotnet" PATH="$HOME/.dotnet:$PATH"
  say "Add this to your shell profile to keep it:  export DOTNET_ROOT=\$HOME/.dotnet PATH=\$HOME/.dotnet:\$PATH"
fi

say "Lean:   $(cd lean && lean --version)"
say ".NET:   $(dotnet --version)"
./build.sh "$@"

say "Installing the lean2il command (a .NET global tool, in ~/.dotnet/tools)"
# Reinstall rather than update: a rebuilt package keeps its version number, and NuGet would reuse its cached copy.
dotnet tool uninstall --global lean2il >/dev/null 2>&1 || true
rm -rf "${NUGET_PACKAGES:-$HOME/.nuget/packages}/lean2il"
dotnet tool install --global lean2il --add-source ./artifacts >/dev/null
case ":$PATH:" in *":$HOME/.dotnet/tools:"*) ;; *) say "Add ~/.dotnet/tools to your PATH to run lean2il from anywhere.";; esac

if command -v code >/dev/null; then
  say "Installing the VS Code extension"
  code --install-extension vscode/lean-to-dot-net-*.vsix --force >/dev/null 2>&1 || true
fi
say "Done. Try: lean2il lean   (or open this folder in VS Code and run 'Lean to .NET: Build .NET Assembly')"
