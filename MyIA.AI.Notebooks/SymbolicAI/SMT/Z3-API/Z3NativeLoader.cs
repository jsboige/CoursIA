// Z3NativeLoader.cs - Bibliotheque native de Z3 pour les notebooks C# qui chargent Microsoft.Z3 depuis NuGet
// Usage dans un notebook, avant le premier appel a Z3 :
//     #r "nuget: Microsoft.Z3"
//     #load "Z3NativeLoader.cs"
//     Z3NativeLoader.Register(typeof(Microsoft.Z3.Context).Assembly);
//
// Le paquet NuGet Microsoft.Z3 (4.12.2, derniere version publiee) ne livre la bibliotheque
// native que pour Windows x64 et macOS Intel (runtimes/win-x64, runtimes/osx-x64). Ailleurs
// (Linux, macOS Apple Silicon), le premier appel a Z3 leve DllNotFoundException 'libz3'.
// Ce chargeur indique alors a .NET ou trouver libz3, dans cet ordre :
//   1. le dossier designe par Z3_LIBRARY_PATH (la variable que z3-py consulte aussi) ;
//   2. le dossier lib/ du paquet Python z3-solver, celui des notebooks Python de la serie
//      (le premier interpreteur, python3 puis python, qui importe z3) ;
//   3. les dossiers systeme (paquet libz3-dev, Homebrew).
// Meme moteur que z3-solver. Pour retrouver exactement les sorties committees, prendre
// la version du paquet NuGet : pip install z3-solver==4.12.2.0.
// Sous Windows et macOS Intel, rien ne change : la bibliotheque du paquet NuGet est utilisee.

using System;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;

public static class Z3NativeLoader
{
    static string _path;

    /// <summary>Chemin de la bibliotheque chargee, ou null si celle du paquet NuGet suffit.</summary>
    public static string LoadedFrom => _path;

    public static void Register(Assembly z3Assembly)
    {
        bool nugetHasNative = OperatingSystem.IsWindows()
            || (OperatingSystem.IsMacOS() && RuntimeInformation.ProcessArchitecture == Architecture.X64);
        if (nugetHasNative || _path != null) return;
        string path = Find();
        try
        {
            NativeLibrary.SetDllImportResolver(z3Assembly, (name, assembly, searchPath) =>
                name == "libz3" ? NativeLibrary.Load(path) : IntPtr.Zero);
        }
        catch (InvalidOperationException)
        {
            // cellule re-executee : un resolveur est deja installe sur cet assembly
        }
        _path = path;
    }

    static string Find()
    {
        string file = OperatingSystem.IsMacOS() ? "libz3.dylib" : "libz3.so";
        var candidates = new System.Collections.Generic.List<string>();
        var env = Environment.GetEnvironmentVariable("Z3_LIBRARY_PATH");
        if (!string.IsNullOrEmpty(env))
            foreach (var dir in env.Split(Path.PathSeparator)) candidates.Add(Path.Combine(dir, file));
        foreach (var exe in new[] { "python3", "python" })
        {
            var dir = Z3SolverLibDir(exe);
            if (dir != null) { candidates.Add(Path.Combine(dir, file)); break; }
        }
        foreach (var dir in new[] { "/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
                                    "/usr/lib64", "/usr/lib", "/usr/local/lib", "/opt/homebrew/lib" })
            candidates.Add(Path.Combine(dir, file));
        foreach (var c in candidates)
            if (File.Exists(c)) return c;
        throw new FileNotFoundException(
            $"{file} introuvable : le paquet NuGet Microsoft.Z3 ne la livre pas pour cette plateforme. " +
            "Installer le paquet Python z3-solver (pip install z3-solver==4.12.2.0), " +
            "ou definir Z3_LIBRARY_PATH vers le dossier qui contient " + file + ".");
    }

    // Dossier lib/ du paquet z3-solver vu par cet interpreteur, ou null.
    static string Z3SolverLibDir(string exe)
    {
        try
        {
            var psi = new ProcessStartInfo(exe)
            { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
            psi.ArgumentList.Add("-c");
            psi.ArgumentList.Add("import os, z3; print(os.path.join(os.path.dirname(z3.__file__), 'lib'))");
            using var p = Process.Start(psi);
            var stderr = p.StandardError.ReadToEndAsync();
            string dir = p.StandardOutput.ReadToEnd().Trim();
            p.WaitForExit();
            return p.ExitCode == 0 && Directory.Exists(dir) ? dir : null;
        }
        catch (System.ComponentModel.Win32Exception)
        {
            return null;   // interpreteur absent du PATH
        }
    }
}
