# Kernels & Runtime — Cluster CoursIA

Document de reference detaillant l'inventaire kernels obligatoire sur toute machine du cluster (cf CLAUDE.md regle H.2).

**Regle user 2026-05-07** : toute machine du cluster (ai-01, po-2023, po-2024, po-2025, po-2026) doit pouvoir executer n'importe quel notebook du depot.

## .NET Interactive (C# notebooks)

Notebooks dans `SymbolicAI/SemanticWeb/`, `SymbolicAI/SmartContract/`, `Search/`, `Sudoku/`, `ML/`, `Probas/`.

| Prerequis | Version | Verification |
|-----------|---------|-------------|
| .NET SDK | 8.0 + 9.0 (10.0 optionnel) | `dotnet --list-sdks` |
| dotnet-interactive | >= 1.0.700 (PIN 1.0.552801 sur ai-01) | `dotnet interactive --version` |
| Jupyter kernels `.net-csharp`, `.net-fsharp`, `.net-powershell` | auto-installes | `jupyter kernelspec list` |

Installation : `dotnet tool install --global Microsoft.dotnet-interactive` puis `dotnet interactive jupyter install`.

**Execution** : toujours cell-by-cell via MCP Jupyter (Papermill ne supporte pas .NET Interactive). Le kernel `.net-csharp` preserve l'etat entre cellules.

**Versions a EVITER** : 1.0.522904 (Roslyn bug), 1.0.712001 (#!import bug). PIN sur 1.0.552801 si possible.

## Python 3.10+ (notebooks Python)

Notebooks dans `GenAI/`, `QuantConnect/`, `GameTheory/`, `IIT/`, `SymbolicAI/SemanticWeb/` (Python).

| Prerequis | Usage |
|-----------|-------|
| Python 3.10+ | Kernel `python3` Jupyter |
| Conda env `epita_symbolic_ai` | `rdflib`, `owlready2`, `reasonable`, `pyshacl` (SemanticWeb Python) |
| Conda env `coursia-ml-training` | `torch`, `sklearn`, `scipy`, `hmmlearn` (ML training) |
| Conda env `mcp-jupyter` | MCP Jupyter server |
| GenAI `.env` | API keys services locaux |

Paths sur ai-01 :
- `C:\Users\MYIA\miniconda3\envs\coursia-ml-training`
- `C:\Users\MYIA\miniconda3\envs\mcp-jupyter`
- `C:\Users\MYIA\.conda\envs\epita_symbolic_ai`

## WSL kernels (Lean / GameTheory / OpenSpiel)

Notebooks dans `GameTheory/` et `SymbolicAI/Lean/` requierent un kernel WSL specifique :
- `Python (GameTheory WSL + OpenSpiel)` pour GameTheory
- `Python 3 (WSL)` ou `Lean 4 (WSL)` pour SymbolicAI/Lean

Pieges : backslashes consommes par WSL shell, paths sans separateurs, kernel timeout 60s cold start, heredoc variables interpolees. Wrapper bash obligatoire (Python wrapper ne marche PAS).

Detail diagnostic + workarounds : [.claude/rules/wsl-kernels.md](../.claude/rules/wsl-kernels.md) + [docs/wsl-kernels-detail.md](wsl-kernels-detail.md).

## Verification rapide (toute machine)

```bash
# .NET
dotnet --list-sdks
dotnet interactive --version
jupyter kernelspec list | findstr ".net"

# Python
python --version
conda env list

# WSL
wsl -l -v
```

## Si un kernel manque

Cf regle F (CLAUDE.md) : reparer plutot que contourner. Installer le kernel manquant, ne pas deleguer. Pour kernels privilegies (UAC), demander au user.
