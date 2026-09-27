# Tutorial: your first proved function in C#

In about fifteen minutes: a Lean function with a docstring, two theorems and a worked example, compiled to a
.NET assembly and called from a C# console app. Every command below was run to write this page.

## 0. Install

> **Only want the editor?** Install **Lean to .NET** from the
> [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=keithadler.lean-to-dot-net), or run
> `code --install-extension keithadler.lean-to-dot-net`. It brings lean2il and Tenet with it; where this page
> says `lean2il .`, run **Lean to .NET: Build .NET Assembly** instead. Everything else is the same.

```bash
git clone https://github.com/keithadler/lean-to-dot-net
cd lean-to-dot-net
./setup.sh
```

This installs what is missing: Lean (through [elan](https://github.com/leanprover/elan), Lean's version
manager) and the .NET 10 SDK. It builds everything, installs the `lean2il` command as a .NET global tool, and
installs the VS Code extension if VS Code is present. You do not install Tenet: it is a NuGet package the
compiler references, and `dotnet` fetches it.

Check that it worked:

```bash
lean2il --version
```

If the command is not found, add `~/.dotnet/tools` to your `PATH`.

## 1. Make a Lean project

```bash
lake +leanprover/lean4:v4.33.1 new shop lib
cd shop
```

The `+leanprover/lean4:v4.33.1` pins the Lean version, so this works even before you have picked a default
toolchain. The project has a library called `Shop`, with its code in `Shop/Basic.lean`.

## 2. Write the function, and say what it does

Replace `Shop/Basic.lean` with:

```lean
namespace Shop

/-- The total of an order line in cents: `qty` items at `unitCents` each, less a discount of `pct`
percent, rounded down to the cent. -/
@[export shop_line_total]
def lineTotal (unitCents qty pct : Nat) : Nat :=
  unitCents * qty * (100 - pct) / 100

end Shop
```

Two things matter here:

- **`@[export shop_line_total]`** marks the definition for lean2il. The symbol name is Lean's (it is the C
  name Lean's own compiler would use); lean2il names the .NET method after the Lean name, `LineTotal`.
- **The docstring** (`/-- ... -/`) becomes the method's summary in IntelliSense.

## 3. Prove things about it

Add these before `end Shop`:

```lean
/-- **A discount never raises the price.** The total is at most the undiscounted price. -/
theorem lineTotal_le (unitCents qty pct : Nat) : lineTotal unitCents qty pct ≤ unitCents * qty := by
  unfold lineTotal
  apply Nat.div_le_of_le_mul
  have : 100 - pct ≤ 100 := Nat.sub_le 100 pct
  calc unitCents * qty * (100 - pct) ≤ unitCents * qty * 100 := Nat.mul_le_mul_left _ this
    _ = 100 * (unitCents * qty) := Nat.mul_comm _ _

/-- **No discount, no change.** -/
theorem lineTotal_zero (unitCents qty : Nat) : lineTotal unitCents qty 0 = unitCents * qty := by
  unfold lineTotal; simp

/-- Four items at $2.50 with 10% off come to $9.00. -/
theorem lineTotal_example : lineTotal 250 4 10 = 900 := by decide
```

Each theorem has a docstring, and that is what puts it in the .NET docs: **a theorem with a docstring is
documentation; one without is a private helper.** The last one is an equation with literal arguments, which
lean2il turns into a C# example and runs against the compiled code.

## 4. Build

```bash
lake build
lean2il .
```

```
lean2il: 2 modules in .../shop (Lean 4.33.1)
tenet: 64,660 declarations in 633 modules re-checked (with everything they import), 0 failed, 107.7s
emitted .../shop/.lake/dotnet/Shop.Proven.dll: 1 function in Shop.Proven, for net10.0
  Shop.Proven.LineTotal  <-  Shop.lineTotal
docs: Shop.Proven.xml (IntelliSense), Shop.Proven.md (how to call it), Shop.Proven.proof.json; 3 theorems, 1 proved example replayed against the IL, all equal
```

What happened, line by line:

1. **Tenet re-checked everything.** Not just your three theorems: every declaration in Lean's own library
   that they rest on, 64,660 of them, through a second, independent kernel. If Tenet had rejected anything,
   lean2il would have stopped here and emitted nothing. For a quicker loop while you work, `--trust-imports`
   re-checks only your own modules (a few seconds).
2. **`lineTotal` became `Shop.Proven.LineTotal`**, compiled from the term Tenet just checked.
3. **The docs were written, and the example was run.** `lineTotal 250 4 10 = 900` was called on the new DLL
   and returned 900. Had it not, lean2il would have failed rather than document a call that does not work.

Everything lands in `.lake/dotnet/`: the assembly, lean2il's small runtime (`LeanToDotNet.Runtime.dll`), the
IntelliSense XML, a Markdown page on how to call it, and `Shop.Proven.proof.json` for tools such as the VS
Code extension.

## 5. Call it from C#

```bash
cd ..
dotnet new console -n ShopApp
```

Reference the two assemblies in `ShopApp/ShopApp.csproj`:

```xml
<ItemGroup>
  <Reference Include="Shop.Proven" HintPath="../shop/.lake/dotnet/Shop.Proven.dll" />
  <Reference Include="LeanToDotNet.Runtime" HintPath="../shop/.lake/dotnet/LeanToDotNet.Runtime.dll" />
</ItemGroup>
```

and call it in `ShopApp/Program.cs`:

```csharp
using Shop;

Console.WriteLine(Proven.LineTotal(250, 4, 10));   // 900
Console.WriteLine(ProvenInfo.Verdict);
```

```bash
dotnet run --project ShopApp
```

```
900
Every proof was re-checked by Tenet, an independent Lean kernel: 64,660 declarations in 633 modules, Lean's own library under the project included, none rejected (Lean 4.33.1).
```

A Lean `Nat` is a `BigInteger` in .NET (it has no size limit in Lean either), so `LineTotal` takes
`BigInteger` arguments; C# converts `250` for you. A negative argument is refused with
`ArgumentOutOfRangeException`, since a `Nat` cannot be negative. `ProvenInfo` is generated into every
assembly: the verdict, the Lean version, and `ProvenInfo.Theorems()`, the list of theorems behind it.

## 6. In VS Code

Open the folder in VS Code with the extension installed. Over `def lineTotal` you get a lens with the C#
signature and the theorem count; in `Program.cs`, one over the call that opens the Lean; the **Proofs** view in
the Activity Bar lists the function, its theorems and the replayed example; and **Lean to .NET: Open Proof
Dashboard** shows everything on one page. **Build .NET Assembly** reruns steps 4 for you, and puts any error on
the line it is about.

## Where to go next

- [The guide](guide.md): every option, what compiles and what does not, how names and types map, how the
  docs are chosen, and what each error means.
- [`lean/Finance/Rounding.lean`](../lean/Finance/Rounding.lean): a larger example, rounding money with a
  `decimal` overload, and the proofs behind it.
