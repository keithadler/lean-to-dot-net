#!/usr/bin/env bash
# The NuGet packages as a user gets them. In a scratch folder: a copy of lean/ with nothing built, and a new console
# project that references LeanToDotNet.Build from artifacts/ (with an empty package cache, so nothing stale is
# used), lists ../lean as a LeanProject, and calls the proven code. `dotnet build` has to run lake, lean2il and
# the C# compiler in that order, and the program has to print the proved answers. Run after the packages are packed.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
native() { if command -v cygpath >/dev/null; then cygpath -m "$1"; else printf '%s' "$1"; fi; }

cp -R "$root/lean" "$work/lean"
rm -rf "$work/lean/.lake"
mkdir "$work/app"
cd "$work/app"
cat > nuget.config <<XML
<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <config><add key="globalPackagesFolder" value="$(native "$work/packages")" /></config>
  <packageSources>
    <clear />
    <add key="local" value="$(native "$root/artifacts")" />
    <add key="nuget.org" value="https://api.nuget.org/v3/index.json" />
  </packageSources>
</configuration>
XML
version=$(sed -n 's:.*<Version>\(.*\)</Version>.*:\1:p' "$root/Directory.Build.props")
cat > app.csproj <<XML
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
  </PropertyGroup>
  <ItemGroup>
    <PackageReference Include="LeanToDotNet.Build" Version="$version" />
    <LeanProject Include="../lean" />
  </ItemGroup>
</Project>
XML
cat > Program.cs <<'CS'
using Finance;

Console.WriteLine(Proven.RoundCents(1.005m));
Console.WriteLine(Proven.Round(-2.675m, 2, RoundingMode.AwayFromZero));
Console.WriteLine(string.Join(", ", Proven.SplitEven(10000, 3)));
CS
dotnet build -nologo -v quiet
got=$(dotnet run --no-build | tr -d '\r')
want=$'1.01\n-2.68\n3334, 3333, 3333'
if [[ "$got" != "$want" ]]; then
  printf 'package smoke test: expected\n%s\ngot\n%s\n' "$want" "$got" >&2
  exit 1
fi
echo "package smoke test: a new project built the Lean with LeanToDotNet.Build and got the proved answers"

# A broken proof has to fail the .NET build with Lean's message at its place in the source, in the form IDEs link.
sed -i.bak 's/splitEven 1 4 = \[1, 0, 0, 0\]/splitEven 1 4 = [0, 1, 0, 0]/' ../lean/Finance/Split.lean
if out=$(dotnet build -nologo 2>&1); then
  echo "package smoke test: the build passed with a broken proof" >&2
  exit 1
fi
if ! grep -qE 'Split\.lean\([0-9]+,[0-9]+\): error LEAN: Tactic `decide` proved that the proposition' <<<"$out"; then
  printf 'package smoke test: no clickable Lean error in the build output:\n%s\n' "$out" >&2
  exit 1
fi
echo "package smoke test: a broken proof fails dotnet build with a clickable Lean error"
