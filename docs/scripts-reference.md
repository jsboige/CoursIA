# Scripts du dépôt — référence maintenance & alignement d'environnement

Référence des scripts réutilisables du dépôt CoursIA. **Règle générale (CLAUDE.md)** : ne jamais écrire un script ad-hoc d'exécution / validation / maintenance — il existe presque toujours un outil dédié ici. Si manquant, l'ajouter dans `scripts/notebook_tools/` (pas à la racine `scripts/`).

Les scripts `scripts/fix_*.py` / `scripts/recycle_*.py` à la racine sont des one-offs **historiques** (corrections ponctuelles déjà appliquées) — ne pas les réutiliser comme outils génériques.

## Outils notebooks canoniques — `scripts/notebook_tools/`

### CLI multi-famille
| Script | Usage |
|--------|-------|
| `notebook_tools.py` | CLI principal : `validate` / `execute` / `skeleton` / `analyze` (multi-famille) |
| `notebook_helpers.py` | Helpers partagés (import, pas d'exécution directe) |
| `extract_notebook_skeleton.py` | Extraire le squelette (structure cellules) d'un notebook |
| `notebook_lint.py` | Lint structurel notebooks (+ `test_notebook_lint.py`) |

### Exécution
| Script | Usage |
|--------|-------|
| `wsl_papermill.py` | **Papermill INSIDE WSL** pour kernels GameTheory/Lean Python (`execute` / `batch` / `check-env`) — cf [.claude/rules/wsl-kernels.md](../.claude/rules/wsl-kernels.md) |
| `batch_reexecute.py` | Re-exécution Papermill en lot |
| `dotnet_executor.py`, `exec_dotnet_persist.py`, `exec_single_cell.py` | Exécution .NET Interactive (cell-by-cell, kernel persistant) |
| `execute_qcpy_docker.py`, `qc_quantbook_execute.py` | Exécution QuantConnect (Quantbooks via Docker/QC Cloud) |
| `_exec_bdd_csharp.py` | Exécution C# BDD interne |

### Catalogue (anti-drift)
| Script | Usage |
|--------|-------|
| `generate_catalog.py` | Régénère `COURSE_CATALOG.generated.json` + `.md`. Flags : `--json-only`, `--series X`, `--status X`, `--check`. **Lancer la copie du worktree** pour cibler ce worktree |
| `catalog_coverage.py` | Couverture du catalogue |
| `expand_catalog_markers.py` | Expansion des marqueurs catalogue |
| `fix_catalog_drift.py` | Corriger le drift catalogue |
| `verify_catalog_readme.py` | Vérifier cohérence catalogue ↔ README |
| `count_notebooks_by_series.py`, `generate_parcours.py` | Comptage + génération de parcours |

### Qualité / conformité (règles C.1/C.2/C.3, anti-leak)
| Script | Usage |
|--------|-------|
| `audit_c1_c3.py` | Audit C.1 (pas d'erreur volontaire) + C.3 (scope re-exécution) |
| `check_c2_compliance.py` | Audit C.2 (outputs + execution_count présents) |
| `detect_solution_leaks.py`, `audit_solution_leaks.py` | Détection fuite de solutions (labeling Exemple/Exercice) |
| `validate_pr_notebooks.py` | Validation des notebooks d'une PR |
| `diagnose_broken.py`, `forensic_scan.py` | Diagnostic notebooks cassés / scan forensic |
| `fix_string_cells.py` | Normaliser cellules `source` en string vs array |

### Diagnostic / reporting / spécifiques
| Script | Usage |
|--------|-------|
| `qc_classify.py` | Classification stratégies QC (BROKEN/NEEDS_IMPROVEMENT/HEALTHY) |
| `epita_prcon_autograde.py` | Autograde EPITA Programmation par Contraintes |
| `weekly_digest.py` | Digest hebdomadaire d'activité |
| `auto_enrich_notebooks.py` | Enrichissement markdown pédagogique automatique |
| `fix_audio_dependencies.py`, `optimize_dvs.py` | Dépendances audio / optimisation |
| `_alpha_diag.py`, `generate_16e.py` | Diagnostics ponctuels |

## Maintenance & environnement — `scripts/`

| Chemin | Usage |
|--------|-------|
| `scripts/environment/setup_environment.ps1` | Setup environnement (alignement machine) |
| `scripts/environment/audit_environment.ps1` | Audit de l'environnement local |
| `scripts/environment/install-ffmpeg.{ps1,sh}` | Installer ffmpeg (audio/vidéo) |
| `scripts/kernels/lean4-wsl/` | Kernel Lean 4 WSL |
| `scripts/kernels/validate_lean11.py` | Validation Lean-11 |
| `scripts/mcp-maintenance/` | Maintenance MCP (config, docs, scripts) — cf `README_MCP_MAINTENANCE.md` |
| `scripts/validation/dispatch.py` + `matrix.yml` | Matrice de validation / dispatch |
| `scripts/genai-stack/genai.py` | GenAI Docker (ComfyUI + Qwen) + validation — cf [docs/genai-services.md](genai-services.md) |
| `scripts/repair_genai_notebooks.py`, `scripts/audit_genai_corruption.py` | Réparation / audit corruption GenAI |
| `scripts/fix_robust_dotenv.py` | Robustesse chargement `.env` |
| `scripts/scan_student_forks.py` | Scan des forks étudiants |
| `scripts/series_progress_manager.py` | Suivi de progression des séries |
| `scripts/validate_qc_projects.py` | Validation projets QuantConnect |
| `scripts/update_navigation.py` | Mise à jour navigation README |
| `scripts/extract_pptx_titles.py`, `scripts/extract_slidev_titles.py` | Extraction titres slides (PPTX / Slidev) |
| `scripts/execute_with_env.py`, `scripts/execute_dotnet_notebook.py`, `scripts/execute_sudoku_python.py` | Wrappers d'exécution avec env |
| `scripts/quantconnect/`, `scripts/smartcontracts/`, `scripts/sudoku/`, `scripts/datasets/`, `scripts/tests/` | Outils par domaine |

## Voir aussi

- [docs/common-commands.md](common-commands.md) — setup env, validation notebooks, slash commands
- [docs/kernels-runtime.md](kernels-runtime.md) — .NET / Python / WSL kernels, conda envs
- [docs/genai-services.md](genai-services.md) — scripts genai-stack, mappings notebooks
- [.claude/rules/wsl-kernels.md](../.claude/rules/wsl-kernels.md) — Papermill WSL
