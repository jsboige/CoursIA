using System;
using System.IO;
using System.Linq;
using System.Reflection;
using Microsoft.ML.Probabilistic.Models;
using Microsoft.ML.Probabilistic.Models.Attributes;
using Microsoft.ML.Probabilistic.Algorithms;
using Microsoft.ML.Probabilistic.Distributions;
using Microsoft.ML.Probabilistic.Compiler;
using Microsoft.ML.Probabilistic;
using Range = Microsoft.ML.Probabilistic.Models.Range;

/// <summary>
/// Helper partagé pour le cache des modèles Infer.NET compilés.
/// Inspiré de PrecompiledRobustSudokuModel du notebook Sudoku-15-Infer-Csharp.
/// </summary>
public static class InferNETCacheHelper
{
    private const string CompiledModelsDir = "CompiledInferNETModels";

    /// <summary>
    /// Tente de charger un modèle précompilé depuis le dossier de cache.
    /// </summary>
    public static bool TryLoadPrecompiledModel<T>(
        string modelName,
        out T compiledModel
    ) where T : class
    {
        compiledModel = null;
        string compiledModelPath = Path.Combine(CompiledModelsDir, $"{modelName}.dll");

        if (!File.Exists(compiledModelPath))
        {
            return false;
        }

        try
        {
            Assembly assembly = Assembly.LoadFrom(compiledModelPath);
            Type modelType = assembly.GetTypes()
                .FirstOrDefault(t => typeof(T).IsAssignableFrom(t));

            if (modelType != null)
            {
                compiledModel = (T)Activator.CreateInstance(modelType);
                return true;
            }
        }
        catch (Exception)
        {
            // Le fichier existe mais ne peut pas être chargé
            return false;
        }

        return false;
    }

    /// <summary>
    /// Sauvegarde le code source généré par Infer.NET pour compilation future.
    /// </summary>
    public static void SaveGeneratedSource(string modelName)
    {
        string generatedSourcePath = Path.Combine(Environment.CurrentDirectory, "GeneratedSource");

        if (!Directory.Exists(generatedSourcePath))
        {
            Console.WriteLine($"Aucun code source généré trouvé dans {generatedSourcePath}");
            return;
        }

        Directory.CreateDirectory(CompiledModelsDir);

        var modelSourceFile = Directory.GetFiles(generatedSourcePath, "*.cs")
            .OrderByDescending(File.GetLastWriteTime)
            .FirstOrDefault();

        if (modelSourceFile != null)
        {
            string targetPath = Path.Combine(CompiledModelsDir, $"{modelName}.cs");
            File.Copy(modelSourceFile, targetPath, true);
            Console.WriteLine($"Code source sauvegardé : {targetPath}");
        }
    }

    /// <summary>
    /// Affiche un message d'information sur le cache.
    /// </summary>
    public static void LogCacheInfo(string modelName)
    {
        Console.WriteLine($"=== Cache Infer.NET pour {modelName} ===");
        Console.WriteLine($"Dossier cache : {CompiledModelsDir}");
        Console.WriteLine($"Modèle DLL : {Path.Combine(CompiledModelsDir, modelName + ".dll")}");
        Console.WriteLine($"Code source  : {Path.Combine(CompiledModelsDir, modelName + ".cs")}");
        Console.WriteLine();
    }

    /// <summary>
    /// Crée le dossier de cache s'il n'existe pas.
    /// </summary>
    public static void EnsureCacheDirectoryExists()
    {
        Directory.CreateDirectory(CompiledModelsDir);
    }

    /// <summary>
    /// Nettoie le cache pour un modèle spécifique.
    /// </summary>
    public static void ClearCache(string modelName)
    {
        string dllPath = Path.Combine(CompiledModelsDir, $"{modelName}.dll");
        string csPath = Path.Combine(CompiledModelsDir, $"{modelName}.cs");

        if (File.Exists(dllPath))
        {
            File.Delete(dllPath);
            Console.WriteLine($"Cache supprimé : {dllPath}");
        }

        if (File.Exists(csPath))
        {
            File.Delete(csPath);
            Console.WriteLine($"Cache supprimé : {csPath}");
        }
    }
}
