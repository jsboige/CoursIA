# Scripts pour les notebooks Infer.NET

Ce répertoire contient les scripts de configuration et de test pour la série de notebooks de programmation probabiliste Infer.NET.

## Prérequis

- .NET SDK 6.0 ou supérieur
- Python 3.8 ou supérieur
- pip (gestionnaire de paquets Python)

## Installation rapide

### Windows (PowerShell)

```powershell
# Exécuter le script de configuration
.\setup_environment.ps1

# Ou avec des options
.\setup_environment.ps1 -Verbose
.\setup_environment.ps1 -SkipPapermill  # Si vous n'avez pas besoin de papermill
```

### Installation manuelle

1. **Installer l'outil .NET Interactive :**
   ```bash
   dotnet tool install -g Microsoft.dotnet-interactive
   dotnet interactive jupyter install
   ```

2. **Installer les dépendances Python :**
   ```bash
   pip install -r requirements.txt
   ```

3. **Vérifier les kernels :**
   ```bash
   jupyter kernelspec list
   ```
   Vous devriez voir `.net-csharp`, `.net-fsharp`, `.net-powershell`

## Tester les notebooks

### Lancer tous les tests

```bash
python test_notebooks.py
```

### Tester un notebook spécifique

```bash
python test_notebooks.py -n Infer-1-Setup.ipynb -v
```

### Options

| Option | Description |
|--------|-------------|
| `-n, --notebook` | Tester un notebook spécifique |
| `-t, --timeout` | Timeout par notebook (défaut : 600s) |
| `-v, --verbose` | Sortie verbeuse |
| `-l, --list` | Lister les notebooks disponibles |

### Sortie

- Les notebooks exécutés sont sauvegardés dans `MyIA.AI.Notebooks/Probas/Infer/test_outputs/`
- Le résumé des résultats de test est sauvegardé dans `test_outputs/test_results.json`

## Dépannage

### Kernel introuvable

Si le kernel `.net-csharp` est introuvable :

```bash
dotnet interactive jupyter install
```

### Problèmes de restauration NuGet

Les notebooks restaurent automatiquement les paquets NuGet. Si vous rencontrez des problèmes :

```bash
dotnet nuget locals all --clear
```

### Problèmes de timeout

Certains notebooks (en particulier ceux avec de nombreuses opérations d'inférence) peuvent prendre plus de temps. Augmentez le timeout :

```bash
python test_notebooks.py -t 1200  # 20 minutes
```

## Fichiers

| Fichier | Description |
|------|-------------|
| `setup_environment.ps1` | Script de configuration PowerShell |
| `test_notebooks.py` | Lanceur de tests Python |
| `requirements.txt` | Dépendances Python |
| `README.md` | Ce fichier |
