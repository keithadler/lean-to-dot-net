using System.Numerics;
using System.Reflection;

namespace LeanToDotNet;

/// <summary>
/// The .NET types and methods a compiled assembly refers to, loaded from the reference assemblies of the target
/// framework through a <see cref="MetadataLoadContext"/> rather than from the running process.
///
/// That distinction is the difference between an assembly a C# project can reference and one it cannot. Types
/// taken from the running process live in <c>System.Private.CoreLib</c>, which works when the assembly is loaded
/// by reflection and fails the moment the C# compiler sees it, because no project references that implementation
/// assembly. Types taken from the reference pack live in <c>System.Runtime</c> and <c>System.Runtime.Numerics</c>,
/// which every project already references.
/// </summary>
internal sealed class Clr : IDisposable
{
    private readonly MetadataLoadContext _mlc;

    public Assembly CoreAssembly => _mlc.CoreAssembly!;
    public string ReferenceDirectory { get; }
    public string TargetFramework { get; }

    public Type Object { get; }
    public Type Void { get; }
    public Type Bool { get; }
    public Type Int32 { get; }
    public Type Int64 { get; }
    public Type String { get; }
    public Type Decimal { get; }
    public Type BigInteger { get; }
    public Type ValueType { get; }
    public Type Enum { get; }
    public Type LeanNat { get; }
    public Type LeanInt { get; }
    public Type DecimalBridge { get; }
    public Type LeanList { get; }
    public Type LeanOption { get; }
    public Type LeanString { get; }
    public Type LeanOps { get; }
    public Type ILeanList { get; }
    public Type ILeanOption { get; }
    public Type RuntimeTypeHandle { get; }
    public Type RuntimeMethodHandle { get; }
    public Type LeanStack { get; }
    public Type LeanStackOverflow { get; }
    public MethodInfo Getter(Type t, string property) => t.GetProperty(property)!.GetGetMethod()!;

    public Clr(string runtimeAssemblyPath)
    {
        (ReferenceDirectory, TargetFramework) = FindReferencePack();
        var paths = Directory.GetFiles(ReferenceDirectory, "*.dll").ToList();
        paths.Add(runtimeAssemblyPath);
        _mlc = new MetadataLoadContext(new PathAssemblyResolver(paths), "System.Runtime");
        Object = Core("System.Object");
        Void = Core("System.Void");
        Bool = Core("System.Boolean");
        Int32 = Core("System.Int32");
        Int64 = Core("System.Int64");
        String = Core("System.String");
        Decimal = Core("System.Decimal");
        ValueType = Core("System.ValueType");
        Enum = Core("System.Enum");
        BigInteger = _mlc.LoadFromAssemblyName("System.Runtime.Numerics").GetType("System.Numerics.BigInteger", throwOnError: true)!;
        Assembly runtime = _mlc.LoadFromAssemblyPath(runtimeAssemblyPath);
        LeanNat = runtime.GetType("LeanToDotNet.Runtime.LeanNat", throwOnError: true)!;
        LeanInt = runtime.GetType("LeanToDotNet.Runtime.LeanInt", throwOnError: true)!;
        DecimalBridge = runtime.GetType("LeanToDotNet.Runtime.DecimalBridge", throwOnError: true)!;
        LeanList = runtime.GetType("LeanToDotNet.Runtime.LeanList`1", throwOnError: true)!;
        LeanOption = runtime.GetType("LeanToDotNet.Runtime.LeanOption`1", throwOnError: true)!;
        LeanString = runtime.GetType("LeanToDotNet.Runtime.LeanString", throwOnError: true)!;
        LeanOps = runtime.GetType("LeanToDotNet.Runtime.LeanOps", throwOnError: true)!;
        ILeanList = runtime.GetType("LeanToDotNet.Runtime.ILeanList", throwOnError: true)!;
        ILeanOption = runtime.GetType("LeanToDotNet.Runtime.ILeanOption", throwOnError: true)!;
        RuntimeTypeHandle = Core("System.RuntimeTypeHandle");
        RuntimeMethodHandle = Core("System.RuntimeMethodHandle");
        LeanStack = runtime.GetType("LeanToDotNet.Runtime.LeanStack", throwOnError: true)!;
        LeanStackOverflow = runtime.GetType("LeanToDotNet.Runtime.LeanStackOverflowException", throwOnError: true)!;
    }

    private Type Core(string name) => CoreAssembly.GetType(name, throwOnError: true)!;

    /// <summary>A public static method of <paramref name="t"/> taking exactly these parameter types.</summary>
    public MethodInfo Static(Type t, string name, params Type[] ps) =>
        t.GetMethod(name, BindingFlags.Public | BindingFlags.Static, null, ps, null)
        ?? throw new MissingMethodException(t.FullName, name);

    /// <summary>A BigInteger operator or method on two BigIntegers.</summary>
    public MethodInfo Big2(string name) => Static(BigInteger, name, BigInteger, BigInteger);

    public MethodInfo Big1(string name) => Static(BigInteger, name, BigInteger);

    public MethodInfo Nat2(string name) => Static(LeanNat, name, BigInteger, BigInteger);

    public MethodInfo Int2(string name) => Static(LeanInt, name, BigInteger, BigInteger);

    public MethodInfo Int1(string name) => Static(LeanInt, name, BigInteger);

    /// <summary>
    /// The newest reference pack for the major version of the runtime lean2il is running on: first the SDK's own
    /// <c>packs</c> folder, then the NuGet cache, where the SDK puts a targeting pack it had to download.
    /// </summary>
    private static (string Dir, string Tfm) FindReferencePack()
    {
        int major = System.Environment.Version.Major;
        string tfm = $"net{major}.0";
        // The two reference assemblies an emitted assembly refers to ship beside lean2il (see Lean2Il.csproj), so it
        // runs with the .NET runtime alone; the SDK's packs are only a fallback for a build that lacks them.
        string bundled = Path.Combine(AppContext.BaseDirectory, "ref");
        if (File.Exists(Path.Combine(bundled, "System.Runtime.dll")) && File.Exists(Path.Combine(bundled, "System.Runtime.Numerics.dll")))
        {
            return (bundled, tfm);
        }
        var candidates = new List<string>();
        string shared = Path.GetDirectoryName(typeof(object).Assembly.Location)!; // <root>/shared/Microsoft.NETCore.App/<ver>
        string root = Path.GetFullPath(Path.Combine(shared, "..", "..", ".."));
        candidates.Add(Path.Combine(root, "packs", "Microsoft.NETCore.App.Ref"));
        string? home = System.Environment.GetEnvironmentVariable("NUGET_PACKAGES")
            ?? Path.Combine(System.Environment.GetFolderPath(System.Environment.SpecialFolder.UserProfile), ".nuget", "packages");
        candidates.Add(Path.Combine(home, "microsoft.netcore.app.ref"));
        foreach (string c in candidates.Where(Directory.Exists))
        {
            string? best = Directory.GetDirectories(c)
                .Where(d => Path.GetFileName(d).StartsWith($"{major}.", StringComparison.Ordinal))
                .OrderByDescending(d => Version.TryParse(Path.GetFileName(d).Split('-')[0], out var v) ? v : new Version())
                .Select(d => Path.Combine(d, "ref", tfm))
                .FirstOrDefault(Directory.Exists);
            if (best is not null)
            {
                return (best, tfm);
            }
        }
        throw new DirectoryNotFoundException(
            $"No .NET {major} reference pack found (looked in {string.Join(", ", candidates)}). Install the .NET {major} SDK; ./setup.sh does it.");
    }

    public void Dispose() => _mlc.Dispose();
}
