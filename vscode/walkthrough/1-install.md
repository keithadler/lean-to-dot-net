## Install the toolchain

lean-to-dot-net needs two things, and `./setup.sh` in the repository installs whichever is missing:

- **Lean 4**, through [elan](https://github.com/leanprover/elan), Lean's version manager. Each project's
  `lean-toolchain` file picks the exact Lean version.
- **The .NET 10 SDK**.

**Tenet** needs no installing. It comes from nuget.org the first time `dotnet` builds the compiler, and its
command-line checker is pinned in `dotnet-tools.json`, so `dotnet tool restore` fetches it.

```bash
git clone https://github.com/keithadler/lean-to-dot-net
cd lean-to-dot-net && ./setup.sh
```
