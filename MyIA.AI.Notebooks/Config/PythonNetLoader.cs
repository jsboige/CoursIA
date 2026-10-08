// PythonNetLoader.cs -- choisit et charge le CPython de pythonnet, sous Windows, Linux et macOS.
//
// Un notebook C# le charge par un chemin relatif a son dossier, puis lui passe l'assembly
// pythonnet qu'il reference deja et le module Python dont il a besoin :
//
//     #r "nuget: pythonnet,3.1.0"
//     #load "../../Config/PythonNetLoader.cs"
//     using Python.Runtime;
//     PythonNetLoader.Initialize(typeof(PythonEngine).Assembly, "mealpy");
//
// Ordre de recherche :
//   1. PYTHONNET_PYDLL, s'il designe un fichier : cette bibliotheque, telle quelle ;
//   2. le premier interpreteur qui importe le module demande, dans une version de CPython
//      que la version chargee de pythonnet prend en charge. Les candidats sont les
//      installations standard de Windows (C:\Python3xx puis %LOCALAPPDATA%\Programs\Python,
//      la plus recente d'abord, puis conda), puis python3 et python du PATH. L'interpreteur
//      retenu donne sa bibliotheque partagee (libpython .so sous Linux, .dylib sous macOS,
//      python3xx.dll sous Windows), son prefixe et son sys.path, environnement virtuel compris.
//
// Le fichier ne reference pas pythonnet : il passe par reflexion sur l'assembly recue.
// MyIA.AI.Notebooks.csproj, qui compile ce dossier, n'en depend donc pas.

#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text.Json;

public static class PythonNetLoader
{
    // Ce que l'interpreteur retenu transmet a pythonnet. Home et SysPath sont nuls quand la
    // bibliotheque vient de PYTHONNET_PYDLL : pythonnet les deduit alors lui-meme.
    public sealed record PythonRuntimeInfo(string Dll, string? Home, IReadOnlyList<string>? SysPath, string Source);

    // Execute par l'interpreteur candidat : importe le module, puis decrit sa version, sa
    // bibliotheque partagee, son prefixe et son sys.path.
    const string ProbeScript =
        "import importlib, json, os, sys, sysconfig\n" +
        "importlib.import_module(sys.argv[1])\n" +
        "v = sysconfig.get_config_var; lib = v('LIBDIR') or ''; mm = sys.version_info[:2]\n" +
        "c = [os.path.join(lib, n) for n in (v('INSTSONAME'), v('LDLIBRARY')) if n]\n" +
        "c += [os.path.join(d, 'libpython%d.%d.dylib' % mm) for d in (lib, os.path.join(sys.base_prefix, 'lib'))]\n" +
        "c.append(os.path.join(sys.base_prefix, 'python%d%d.dll' % mm))\n" +
        "dll = next((p for p in c if os.path.isfile(p)), '')\n" +
        "print(json.dumps({'version': list(sys.version_info[:3]), 'dll': dll,\n" +
        "                  'home': sys.base_prefix, 'path': [p for p in sys.path if p]}))\n";

    // Trouve le CPython a charger pour un notebook qui a besoin de `module`.
    public static PythonRuntimeInfo Resolve(Assembly pythonnet, string module)
    {
        var configured = Environment.GetEnvironmentVariable("PYTHONNET_PYDLL");
        if (!string.IsNullOrWhiteSpace(configured) && File.Exists(configured))
            return new PythonRuntimeInfo(configured, null, null, "PYTHONNET_PYDLL");

        var engine = pythonnet.GetType("Python.Runtime.PythonEngine", throwOnError: true)!;
        var isSupported = engine.GetMethod("IsSupportedVersion", new[] { typeof(Version) })!;
        var rejected = new List<string>();
        foreach (var interpreter in CandidateInterpreters())
        {
            var probe = ProbeInterpreter(interpreter, module);
            if (probe == null) continue;
            var (info, version) = probe.Value;
            if ((bool)isSupported.Invoke(null, new object[] { version })!) return info;
            rejected.Add($"{interpreter} ({version})");
        }

        var min = (Version)engine.GetProperty("MinSupportedVersion")!.GetValue(null)!;
        var max = (Version)engine.GetProperty("MaxSupportedVersion")!.GetValue(null)!;
        var range = $"{min.ToString(2)} a {max.ToString(2)}";
        var detail = rejected.Count == 0 ? "" : $" Versions hors de cette plage : {string.Join(", ", rejected)}.";
        throw new FileNotFoundException(
            $"Aucun CPython {range} n'importe {module} : l'installer (pip install), ou definir PYTHONNET_PYDLL.{detail}");
    }

    // Charge le CPython retenu dans pythonnet. Sans effet si le moteur tourne deja
    // (cellule re-executee) : renvoie alors null.
    public static PythonRuntimeInfo? Initialize(Assembly pythonnet, string module)
    {
        var engine = pythonnet.GetType("Python.Runtime.PythonEngine", throwOnError: true)!;
        if ((bool)engine.GetProperty("IsInitialized")!.GetValue(null)!) return null;

        var info = Resolve(pythonnet, module);
        if (OperatingSystem.IsWindows()) AddDependencyDirectoriesToPath(info.Dll);
        pythonnet.GetType("Python.Runtime.Runtime", throwOnError: true)!
            .GetProperty("PythonDLL")!.SetValue(null, info.Dll);
        if (info.Home != null) engine.GetProperty("PythonHome")!.SetValue(null, info.Home);
        engine.GetMethod("Initialize", Type.EmptyTypes)!.Invoke(null, null);

        if (info.SysPath != null)
        {
            // Le sys.path de l'interpreteur sonde, environnement virtuel compris.
            var gil = (IDisposable)pythonnet.GetType("Python.Runtime.Py", throwOnError: true)!
                .GetMethod("GIL", Type.EmptyTypes)!.Invoke(null, null)!;
            using (gil)
            {
                var code = "import sys\nsys.path[:] = " + JsonSerializer.Serialize(info.SysPath) + "\n";
                engine.GetMethod("RunSimpleString", new[] { typeof(string) })!.Invoke(null, new object[] { code });
            }
        }
        return info;
    }

    // Installations standard de Windows d'abord, puis python3 et python du PATH.
    static IEnumerable<string> CandidateInterpreters()
    {
        if (OperatingSystem.IsWindows())
        {
            var roots = new List<string>();
            roots.AddRange(PythonDirectories(@"C:\"));
            var localAppData = Environment.GetEnvironmentVariable("LOCALAPPDATA");
            if (!string.IsNullOrWhiteSpace(localAppData))
                roots.AddRange(PythonDirectories(Path.Combine(localAppData, "Programs", "Python")));
            var home = Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
            roots.AddRange(new[] {
                Path.Combine(home, "miniconda3"), Path.Combine(home, "anaconda3"),
                @"C:\ProgramData\miniconda3", @"C:\ProgramData\anaconda3" });
            foreach (var root in roots)
            {
                var exe = Path.Combine(root, "python.exe");
                if (File.Exists(exe)) yield return exe;
            }
        }
        yield return "python3";
        yield return "python";
    }

    // Dossiers Python3xx de `root`, la version la plus recente d'abord (Python313 avant Python39).
    static IEnumerable<string> PythonDirectories(string root)
    {
        try
        {
            return Directory.Exists(root)
                ? Directory.GetDirectories(root, "Python3*").OrderByDescending(p => MinorVersion(Path.GetFileName(p))).ToArray()
                : Array.Empty<string>();
        }
        catch (Exception e) when (e is UnauthorizedAccessException || e is IOException)
        {
            return Array.Empty<string>();
        }
    }

    static int MinorVersion(string directoryName)
    {
        var digits = new string(directoryName.Skip("Python3".Length).TakeWhile(char.IsDigit).ToArray());
        return int.TryParse(digits, out var minor) ? minor : -1;
    }

    static (PythonRuntimeInfo Info, Version Version)? ProbeInterpreter(string interpreter, string module)
    {
        try
        {
            var psi = new ProcessStartInfo(interpreter)
            { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
            foreach (var arg in new[] { "-c", ProbeScript, module }) psi.ArgumentList.Add(arg);
            using var process = Process.Start(psi);
            if (process == null) return null;
            // Lectures asynchrones : un interpreteur bloque ne doit pas bloquer la cellule.
            var stdout = process.StandardOutput.ReadToEndAsync();
            _ = process.StandardError.ReadToEndAsync();   // draine stderr sans le lire
            if (!process.WaitForExit(120_000)) { process.Kill(entireProcessTree: true); return null; }
            if (process.ExitCode != 0) return null;

            var json = JsonDocument.Parse(stdout.Result).RootElement;
            var dll = json.GetProperty("dll").GetString();
            if (string.IsNullOrEmpty(dll)) return null;
            var v = json.GetProperty("version").EnumerateArray().Select(e => e.GetInt32()).ToArray();
            var sysPath = json.GetProperty("path").EnumerateArray().Select(e => e.GetString() ?? "").ToArray();
            var info = new PythonRuntimeInfo(dll, json.GetProperty("home").GetString(), sysPath, interpreter);
            return (info, new Version(v[0], v[1], v[2]));
        }
        catch (System.ComponentModel.Win32Exception) { return null; }   // interpreteur absent
        catch (JsonException) { return null; }                          // sortie inattendue
    }

    // Windows : les DLL dont depend python3xx.dll (ssl, ffi, zlib sous conda) doivent etre
    // trouvables avant le chargement. Memes dossiers que `conda activate`, plus DLLs.
    static void AddDependencyDirectoriesToPath(string dll)
    {
        var root = Path.GetDirectoryName(dll);
        if (string.IsNullOrEmpty(root)) return;
        var directories = new[] {
                root,
                Path.Combine(root, "Library", "mingw-w64", "bin"),
                Path.Combine(root, "Library", "usr", "bin"),
                Path.Combine(root, "Library", "bin"),
                Path.Combine(root, "Scripts"),
                Path.Combine(root, "bin"),
                Path.Combine(root, "DLLs") }
            .Where(Directory.Exists);
        var current = Environment.GetEnvironmentVariable("PATH") ?? "";
        Environment.SetEnvironmentVariable("PATH", string.Join(Path.PathSeparator, directories.Append(current)));
    }
}
