# ÉTAPE 2 : Variables Critiques pour Injection MCP

## 🎯 **DÉCOUVERTE MAJEURE : Cause Racine Identifiée**

L'audit environnemental a révélé que le problème **N'EST PAS** dans les variables .NET (déjà présentes) mais dans **l'environnement conda utilisé** :

- ✅ **Environnement fonctionnel :** `mcp-jupyter-py310` 
- ❌ **Environnement MCP actuel :** `mcp-jupyter`

## 📋 **LISTE COMPLÈTE DES VARIABLES À INJECTER**

### **1. Variables CONDA Manquantes Critiques**
```json
{
  "CONDA_EXE": "C:\\ProgramData\\miniconda3\\Scripts\\conda.exe",
  "CONDA_PREFIX_1": "C:\\ProgramData\\miniconda3",
  "CONDA_PROMPT_MODIFIER": "(mcp-jupyter-py310)",
  "CONDA_PYTHON_EXE": "C:\\ProgramData\\miniconda3\\python.exe",
  "CONDA_ROOT": "C:\\ProgramData\\miniconda3",
  "CONDA_SHLVL": "2",
  "_CONDA_EXE": "C:\\ProgramData\\miniconda3\\Scripts\\conda.exe",
  "_CONDA_OLD_CHCP": "65001",
  "_CONDA_ROOT": "C:\\ProgramData\\miniconda3",
  "__CONDA_OPENSLL_CERT_FILE_SET": "1"
}
```

### **2. PATH Critique Manquant (à préfixer)**
```json
{
  "PATH": "C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\mingw-w64\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\usr\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Scripts;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\bin;c:\\Program Files\\Git\\cmd;C:\\Users\\jsboi\\.elan\\bin;C:\\WINDOWS\\system32;C:\\WINDOWS;C:\\WINDOWS\\System32\\Wbem;C:\\WINDOWS\\System32\\WindowsPowerShell\\v1.0\\;C:\\WINDOWS\\System32\\OpenSSH\\;C:\\Program Files (x86)\\NVIDIA Corporation\\PhysX\\Common;C:\\ProgramData\\chocolatey\\bin;C:\\Program Files\\dotnet\\;C:\\Program Files\\Microsoft VS Code\\bin;C:\\Program Files\\Git\\cmd;C:\\Program Files\\NVIDIA Corporation\\NVIDIA App\\NvDLISR;C:\\Program Files\\Docker\\Docker\\resources\\bin;C:\\Program Files\\nodejs\\;C:\\JupyterLab;C:\\ProgramData\\miniconda3;C:\\ProgramData\\miniconda3\\Scripts;C:\\Strawberry\\c\\bin;C:\\Strawberry\\perl\\site\\bin;C:\\Strawberry\\perl\\bin;C:\\Users\\jsboi\\AppData\\Local\\Microsoft\\WindowsApps;C:\\Users\\jsboi\\.dotnet\\tools;C:\\Users\\jsboi\\AppData\\Roaming\\npm;C:\\Users\\jsboi\\AppData\\Local\\Programs\\MiKTeX\\miktex\\bin\\x64\\;C:\\Users\\jsboi\\AppData\\Local\\Pandoc\\"
}
```

### **3. Variables .NET Existantes (À Conserver)**
```json
{
  "DOTNET_ROOT": "C:\\Program Files\\dotnet",
  "NUGET_PACKAGES": "C:\\Users\\jsboi\\.nuget\\packages",
  "PACKAGEMANAGEMENT_HOME": "C:\\Users\\jsboi\\.packagemanagement",
  "MSBuildExtensionsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
  "MSBuildSDKsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305\\Sdks",
  "MSBuildToolsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
  "MSBuildUserExtensionsPath": "C:\\Users\\jsboi\\AppData\\Local\\Microsoft\\MSBuild"
}
```

## 🔧 **CONFIGURATION MCP_SETTINGS.JSON COMPLÈTE**

```json
{
  "jupyter-papermill-mcp-server": {
    "transportType": "stdio",
    "autoStart": true,
    "description": "Serveur MCP Python avec Papermill et environnement .NET complet",
    "disabled": false,
    "command": "conda",
    "args": ["run", "-n", "mcp-jupyter-py310", "python", "-m", "papermill_mcp.main"],
    "env": {
      "PYTHONPATH": "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server",
      "CONDA_EXE": "C:\\ProgramData\\miniconda3\\Scripts\\conda.exe",
      "CONDA_PREFIX_1": "C:\\ProgramData\\miniconda3",
      "CONDA_PROMPT_MODIFIER": "(mcp-jupyter-py310)",
      "CONDA_PYTHON_EXE": "C:\\ProgramData\\miniconda3\\python.exe",
      "CONDA_ROOT": "C:\\ProgramData\\miniconda3",
      "CONDA_SHLVL": "2",
      "_CONDA_EXE": "C:\\ProgramData\\miniconda3\\Scripts\\conda.exe",
      "_CONDA_OLD_CHCP": "65001",
      "_CONDA_ROOT": "C:\\ProgramData\\miniconda3",
      "__CONDA_OPENSLL_CERT_FILE_SET": "1",
      "PATH": "C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\mingw-w64\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\usr\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Library\\bin;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\Scripts;C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\bin;c:\\Program Files\\Git\\cmd;C:\\Users\\jsboi\\.elan\\bin;C:\\WINDOWS\\system32;C:\\WINDOWS;C:\\WINDOWS\\System32\\Wbem;C:\\WINDOWS\\System32\\WindowsPowerShell\\v1.0\\;C:\\WINDOWS\\System32\\OpenSSH\\;C:\\Program Files (x86)\\NVIDIA Corporation\\PhysX\\Common;C:\\ProgramData\\chocolatey\\bin;C:\\Program Files\\dotnet\\;C:\\Program Files\\Microsoft VS Code\\bin;C:\\Program Files\\Git\\cmd;C:\\Program Files\\NVIDIA Corporation\\NVIDIA App\\NvDLISR;C:\\Program Files\\Docker\\Docker\\resources\\bin;C:\\Program Files\\nodejs\\;C:\\JupyterLab;C:\\ProgramData\\miniconda3;C:\\ProgramData\\miniconda3\\Scripts;C:\\Strawberry\\c\\bin;C\\Strawberry\\perl\\site\\bin;C:\\Strawberry\\perl\\bin;C:\\Users\\jsboi\\AppData\\Local\\Microsoft\\WindowsApps;C:\\Users\\jsboi\\.dotnet\\tools;C:\\Users\\jsboi\\AppData\\Roaming\\npm;C:\\Users\\jsboi\\AppData\\Local\\Programs\\MiKTeX\\miktex\\bin\\x64\\;C:\\Users\\jsboi\\AppData\\Local\\Pandoc\\",
      "DOTNET_ROOT": "C:\\Program Files\\dotnet",
      "NUGET_PACKAGES": "C:\\Users\\jsboi\\.nuget\\packages",
      "PACKAGEMANAGEMENT_HOME": "C:\\Users\\jsboi\\.packagemanagement",
      "MSBuildExtensionsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
      "MSBuildSDKsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305\\Sdks",
      "MSBuildToolsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
      "MSBuildUserExtensionsPath": "C:\\Users\\jsboi\\AppData\\Local\\Microsoft\\MSBuild",
      "DOTNET_INTERACTIVE_CLI_TELEMETRY_OPTOUT": "1",
      "DOTNET_NOLOGO": "1"
    }
  }
}
```

## ⚠️ **MODIFICATIONS CRITIQUES NÉCESSAIRES**

1. **Changer l'environnement conda :** `mcp-jupyter` → `mcp-jupyter-py310`
2. **Ajouter les 10 variables CONDA manquantes**  
3. **Corriger le PATH** avec les chemins conda en tête
4. **Conserver les variables .NET existantes**

## 🎯 **RÉSULTAT ATTENDU**

Avec cette configuration complète, le subprocess isolation aura **exactement le même environnement** que la commande `conda run -n mcp-jupyter-py310` qui fonctionne parfaitement.

**Status :** ✅ **PRÊT POUR ÉTAPE 3 (Injection et Test)**