## Call it from C#

Reference the two assemblies from `.lake/dotnet/`:

```xml
<ItemGroup>
  <Reference Include="Finance.Proven" HintPath="path/to/Finance.Proven.dll" />
  <Reference Include="LeanToDotNet.Runtime" HintPath="path/to/LeanToDotNet.Runtime.dll" />
</ItemGroup>
```

```csharp
using Finance;
Proven.Round(0.125m, 2, RoundingMode.AwayFromZero); // 0.13
```

Every call gets a lens, **proved in Lean**, that opens the definition, and a hover with its theorems.
