# LeanToDotNet.Build

Compile Lean 4 definitions into your .NET project on every build.

```xml
<ItemGroup>
  <PackageReference Include="LeanToDotNet.Build" Version="0.3.0" />
  <LeanProject Include="../lean" />
</ItemGroup>
```

`dotnet build` then runs `lake build` in `../lean` and lean2il on it: every proof is re-checked by Tenet, the
`@[export]` definitions become `<Namespace>.Proven.dll` with IntelliSense docs, the proved examples are replayed
against it, and random inputs are run through Lean's compiler and the IL, which must agree. The assembly is
referenced and copied to the output. Nothing runs again until a `.lean` file, the lakefile or the toolchain
changes.

You need Lean (`elan`) and the .NET 10 SDK. lean2il and Tenet come inside this package.

| Property | Default | |
|---|---|---|
| `LeanLakeBuild` | `true` | run `lake build` first |
| `LeanCheckImports` | `false` | also re-check Lean's library under the project (slower) |
| `LeanFuzz` | `100` | random inputs per function for the differential test; `0` skips it |

Metadata on a `LeanProject`: `Assembly`, `Namespace`, `Class`, as lean2il's options of the same names.

More: https://github.com/keithadler/lean-to-dot-net
