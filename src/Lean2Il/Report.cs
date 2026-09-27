using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using Tenet.Kernel;
using Tenet.Olean;

namespace LeanToDotNet;

/// <summary>
/// Errors, as a person at a terminal or an IDE wants them. By default: <c>lean2il: message</c>. With
/// <c>--msbuild</c>: MSBuild's canonical form, <c>File.lean(12,5): error L2IL001: message</c>, which Visual Studio,
/// Rider and VS Code's C# tools list with the others and open at the line when clicked.
/// </summary>
internal static class Report
{
    public static bool MsBuild { get; set; }

    /// <summary>How many errors have been reported with a place in the source.</summary>
    public static int Located { get; set; }

    /// <summary>Where a declaration is in the project's sources, once the modules are loaded.</summary>
    public static Func<Name, (string File, int Line, int Column)?>? Locate { get; set; }

    public static void Error(string message, Name? at = null, string code = "L2IL001")
    {
        if (!MsBuild)
        {
            Console.Error.WriteLine("lean2il: " + message);
            return;
        }
        var where = at is not null ? Locate?.Invoke(at) : null;
        Located += where is null ? 0 : 1;
        Console.WriteLine(Canonical(where, "error", code, message));
    }

    /// <summary>
    /// The closing "it failed" line. In an IDE's error list it only repeats the located errors above it, so there it
    /// appears only when nothing else did.
    /// </summary>
    public static void Summary(string message)
    {
        if (!MsBuild || Located == 0)
        {
            Error(message);
        }
    }

    public static void Rejected(string module, Name name, string message)
    {
        if (!MsBuild)
        {
            Console.Error.WriteLine($"  REJECTED {module}: {name}: {message}");
            return;
        }
        Console.WriteLine(Canonical(Locate?.Invoke(name), "error", "TENET", $"Tenet rejected {name}: {message}"));
    }

    public static string Canonical((string File, int Line, int Column)? at, string severity, string code, string message)
    {
        string text = Regex.Replace(message, @"\s*\n\s*", " ").Trim();
        return at is { } a ? $"{a.File}({a.Line},{a.Column}): {severity} {code}: {text}" : $"lean2il : {severity} {code}: {text}";
    }

    /// <summary>
    /// The line of a declaration's name: Lean records where the whole declaration starts, docstring and attributes
    /// included, so look inside that range for the line that introduces the name.
    /// </summary>
    public static (string File, int Line, int Column)? Find(Name n, IEnumerable<Name> modules, Func<Name, SourceRange?> rangeIn, string project)
    {
        foreach (Name m in modules)
        {
            if (rangeIn(m) is not SourceRange r)
            {
                continue;
            }
            string file = Path.Combine(project, Path.Combine(m.ToString().Split('.')) + ".lean");
            if (!File.Exists(file))
            {
                continue;
            }
            string[] lines = File.ReadAllLines(file);
            string last = Regex.Escape(n.LastString ?? n.ToString());
            var intro = new Regex($@"\b(def|abbrev|theorem|instance|structure|inductive)\s+(\S+\.)?{last}\b");
            for (int i = r.Line - 1; i < Math.Min(r.EndLine, lines.Length); i++)
            {
                Match mt = intro.Match(lines[i]);
                if (mt.Success)
                {
                    return (file, i + 1, mt.Index + 1);
                }
            }
            return (file, r.Line, r.Column + 1);
        }
        return null;
    }
}

/// <summary>
/// <c>lake build</c>, with Lean's messages passed through, or with <c>--msbuild</c> rewritten in MSBuild's form:
/// <c>error: Finance/Split.lean:78:69: Tactic ... is false</c> becomes
/// <c>/…/Finance/Split.lean(78,70): error LEAN: Tactic ... is false</c>, its following lines joined on.
/// </summary>
internal static partial class LakeBuild
{
    public static int Run(string project)
    {
        var psi = new ProcessStartInfo("lake") { WorkingDirectory = project, RedirectStandardOutput = true, RedirectStandardError = true };
        psi.ArgumentList.Add("build");
        // An IDE started from the Dock may not have elan's folder on PATH.
        string elan = Path.Combine(System.Environment.GetFolderPath(System.Environment.SpecialFolder.UserProfile), ".elan", "bin");
        psi.Environment["PATH"] = elan + Path.PathSeparator + (System.Environment.GetEnvironmentVariable("PATH") ?? "");
        Process p;
        try
        {
            p = Process.Start(psi)!;
        }
        catch (System.ComponentModel.Win32Exception)
        {
            throw new CompileError("lake was not found; install Lean with elan (https://github.com/leanprover/elan) or put lake on PATH");
        }
        var lines = new List<string>();
        var gate = new object();
        void Add(string? line)
        {
            if (line is not null)
            {
                lock (gate)
                {
                    lines.Add(line);
                }
            }
        }
        p.OutputDataReceived += (_, e) => Add(e.Data);
        p.ErrorDataReceived += (_, e) => Add(e.Data);
        p.BeginOutputReadLine();
        p.BeginErrorReadLine();
        p.WaitForExit();
        foreach (string line in Rewrite(lines, project))
        {
            Console.WriteLine(line);
        }
        return p.ExitCode;
    }

    public static IEnumerable<string> Rewrite(IReadOnlyList<string> lines, string project)
    {
        for (int i = 0; i < lines.Count; i++)
        {
            Match m = LeanMessage().Match(lines[i]);
            if (Report.MsBuild && !m.Success && lines[i].StartsWith("error: ", StringComparison.Ordinal))
            {
                // Lake's summary ("error: build failed"): the errors themselves are reported with their places, and
                // lean2il reports the failure once more; as an error of its own this would only be a duplicate.
                yield return "lake says: " + lines[i]["error: ".Length..];
                continue;
            }
            if (!Report.MsBuild || !m.Success)
            {
                yield return lines[i];
                continue;
            }
            var text = new StringBuilder(m.Groups["msg"].Value);
            int j = i + 1;
            for (; j < lines.Count && j < i + 12 && !NotContinuation().IsMatch(lines[j]); j++)
            {
                text.Append(' ').Append(lines[j].Trim());
            }
            string file = Path.GetFullPath(Path.Combine(project, m.Groups["file"].Value));
            var at = (file, int.Parse(m.Groups["line"].Value), int.Parse(m.Groups["col"].Value) + 1);
            Report.Located += m.Groups["sev"].Value == "error" ? 1 : 0;
            yield return Report.Canonical(at, m.Groups["sev"].Value, "LEAN", text.ToString());
            i = j - 1;
        }
    }

    [GeneratedRegex(@"^(?<sev>error|warning): (?<file>.+?\.lean):(?<line>\d+):(?<col>\d+): (?<msg>.*)$")]
    private static partial Regex LeanMessage();

    [GeneratedRegex(@"^(error|warning|info|trace|✖|⚠|✔|Some required|Build completed|- |\s*$)")]
    private static partial Regex NotContinuation();
}
