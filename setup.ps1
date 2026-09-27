# Install what lean-to-dot-net needs on Windows, if it is missing, then build everything.
# elan from its official installer, the .NET 10 SDK from Microsoft's dotnet-install.ps1 into
# $HOME\.dotnet. Tenet comes from NuGet on first build; there is nothing to install for it.
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot

if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
  Write-Host 'Lean is missing: installing elan (the Lean version manager)'
  $elan = Join-Path $env:TEMP 'elan-init.ps1'
  Invoke-WebRequest https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile $elan
  & $elan -NoPrompt $true -DefaultToolchain none
  $env:PATH = "$HOME\.elan\bin;$env:PATH"
}
$sdks = (Get-Command dotnet -ErrorAction SilentlyContinue) ? (dotnet --list-sdks) : @()
if (-not ($sdks -match '^10\.')) {
  Write-Host 'The .NET 10 SDK is missing: installing it into ~\.dotnet'
  $di = Join-Path $env:TEMP 'dotnet-install.ps1'
  Invoke-WebRequest https://dot.net/v1/dotnet-install.ps1 -OutFile $di
  & $di -Channel 10.0 -InstallDir "$HOME\.dotnet"
  $env:DOTNET_ROOT = "$HOME\.dotnet"; $env:PATH = "$HOME\.dotnet;$env:PATH"
}

Push-Location lean; lake build; Pop-Location
dotnet tool restore
dotnet build src/Lean2Il -c Release -nologo
dotnet pack src/Lean2Il -c Release -o artifacts -nologo
dotnet tool uninstall --global lean2il 2>$null
Remove-Item -Recurse -Force "$HOME\.nuget\packages\lean2il" -ErrorAction SilentlyContinue
dotnet tool install --global lean2il --add-source ./artifacts
dotnet src/Lean2Il/bin/Release/net10.0/lean2il.dll lean --trust-imports
dotnet test tests/LeanToDotNet.Tests -c Release -nologo
dotnet run --project samples/Invoice -c Release
$vsix = Get-ChildItem vscode/*.vsix -ErrorAction SilentlyContinue | Select-Object -First 1
if ($vsix -and (Get-Command code -ErrorAction SilentlyContinue)) { code --install-extension $vsix.FullName --force }
