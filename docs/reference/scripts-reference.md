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
| `wsl_papermill.py` | **Papermill INSIDE WSL** pour kernels GameTheory/Lean Python (`execute` / `batch` / `check-env`) — cf [.claude/rules/wsl-kernels.md](../../.claude/rules/wsl-kernels.md) |
| `batch_reexecute.py` | Re-exécution Papermill en lot |
| `dotnet_executor.py`, `exec_dotnet_persist.py`, `exec_single_cell.py` | Exécution .NET Interactive (cell-by-cell, kernel persistant) |
| `execute_qcpy_docker.py`, `qc_quantbook_execute.py` | Exécution QuantConnect (Quantbooks via Docker/QC Cloud) |
| `_exec_bdd_csharp.py` | Exécution C# BDD interne |

#### `notebook_tools.py execute` — Options avancées

```bash
python scripts/notebook_tools/notebook_tools.py execute <target> [options]
```

| Option | Description | Cas d'usage |
|--------|-------------|-------------|
| `--kernel <name>` | Force un kernel specifique (ex. `python3`, `.net-csharp`, `python3 (PyMC)`) | Cibler un env conda precis quand le kernel par defaut manque des deps |
| `--cwd <path>` | Execute depuis ce repertoire au lieu du dossier parent du notebook | Executer dans un worktree de curation, ou isoler `load_dotenv()` |
| `--env KEY=VAL` | Injecte une variable d'environnement (repeter pour plusieurs) | `--env BATCH_MODE=true`, overrides ponctuels |
| `--scrub-keys` | Retire les cles API LLM (`OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, etc.) du sous-processus | Force le chemin mock deterministe pour les notebooks LLM (SC-11, GenAI) sans appel API payant |
| `--batch-mode` | Active BATCH_MODE=true (env + param Papermill) | Notebooks interactifs en validation non-interactive |
| `--cell-by-cell` | Execution cellule par cellule (.NET/Lean) | Kernels persistants |
| `--timeout N` | Timeout par notebook en secondes (defaut: 300) | Notebooks longs |

**Cookbook — cas d'usage courants** :

```bash
# Re-exec validation standard (chemin mock, pas d'appel API)
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/SymbolicAI/SmartContracts/SC-11-LLM-Assisted.ipynb --scrub-keys

# Re-exec dans un worktree de curation
python scripts/notebook_tools/notebook_tools.py execute /tmp/worktree/SC-11.ipynb --cwd /tmp/worktree

# Forcer un kernel conda specifique
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Probas/PyMC/ --kernel "python3 (PyMC)"

# Re-exec avec variables d'env personnalisees
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/GenAI/ --env BATCH_MODE=true --env MOCK_RESPONSES=true

# Re-exec batch d'une famille complete, mode mock
python scripts/notebook_tools/notebook_tools.py execute SmartContracts --scrub-keys --batch-mode
```

#### Capture des outputs .NET post-`#r` (#5005)

Les notebooks .NET Interactive contenant une directive `#r "nuget: ..."` ou `#r "<dll>"` perdent leurs outputs stdout (`Console.WriteLine`) si exécutes via le chemin Papermill par defaut (drain iopub / timing `nbclient` 2.7.0).

**Recommandations** :

- **`--cell-by-cell`** (chemin `jupyter_client` direct) : OK depuis le fix du warmup post-`wait_for_ready` (cf PR `feature/5005-cell-by-cell-warmup`, fichier `scripts/notebook_tools/notebook_helpers.py`). Pas de régression Python/Lean (warmup conditionnel `.net-*`).
- **`dotnet_executor.py`** directement : chemin canonique pour les notebooks .NET, déjà fonctionnel avant le fix. À privilégier pour les re-exécutions de validation.

```bash
# Validation .NET canonique (chemin kc.execute() direct, sans Papermill)
python scripts/notebook_tools/dotnet_executor.py <notebook> --kernel .net-csharp --timeout 240

# Equivalent via le CLI multi-famille (depuis le fix warmup)
python scripts/notebook_tools/notebook_tools.py execute <notebook> --cell-by-cell --kernel .net-csharp --timeout 240
```

**Diagnostic** : le bug n'est PAS dans le kernel .NET Interactive ni dans le mode HTTP — un test `jupyter_client` direct (`kc.execute()` + `get_iopub_msg`) capture 9/9 outputs post-`#r`. Le défaut venait des wrappers client (Papermill + cell-by-cell sans warmup).

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
| `diagnose_broken.py`, `forensic_scan.py` | Diagnostic notebooks cassés / scan forensic (HEAD, erreurs *dures* uniquement) |
| `regression_scan.py` | Détecteur de régression **output-health** (axe-2) : marqueurs *doux* de dégradation env que `forensic_scan`/`diagnose_broken` ratent (token-starve, `Graphviz non disponible`, MiniZinc/Tweety manquant, `.env` mono-endpoint, `INFEASIBLE`/`Solution valide: False`). 3 modes : `--snapshot` (défaut, dégradés à HEAD), `--history` (git-walk `git log --follow` + `git show` par notebook → pointe le commit/date/auteur régressant + recoveries), `--guard --base <ref> --head <ref> --paths …` (CI, exit 1 si healthy→degraded). Allowlist `regression_allowlist.json` (dégradations *démontrées*/externes acquittées). Git **local-only**, stdlib pure. Ne juge PAS la fidélité prose↔sortie (axe-1 = humain/bot) |
| `fix_string_cells.py` | Normaliser cellules `source` en string vs array |
| `scan_md_hierarchy.py` | Audit **mise en forme** (EPIC #3966) : flague `HINT-AS-HEADING` (indice/objectif/etape en heading -> grande police), `H1-DEEP`, `MULTI-H1`. Render-agnostic (parse JSON). Verif visuelle finale via nbconvert+Playwright : cf [notebook-formatting.md](notebook-formatting.md) |
| `audit_pip_install_cells.py` | Audit cellules `!pip install` (leak vector + env anti-pattern, secrets-hygiene §6 triage C = source-leak). Classifier `UNCONDITIONAL_BASH` / `UNCONDITIONAL_SYS` / `CONDITIONAL_TRY` / `NON_BASH`. Modes `--scan` / `--scan-all` / `--scan-all --check` (exit 1 si HIGH) / `--json`. Compteur initial repo = 70 HIGH-severity sur 203 notebooks (c.460). 13/13 tests unitaires PASS |

### Diagnostic / reporting / spécifiques
| Script | Usage |
|--------|-------|
| `qc_classify.py` | Classification stratégies QC (BROKEN/NEEDS_IMPROVEMENT/HEALTHY) |
| `epita_prcon_autograde.py` | Autograde EPITA Programmation par Contraintes |
| `weekly_digest.py` | Digest hebdomadaire d'activité |
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
| `scripts/lean/setup_lean4_all.py` | **Point d'entrée unique** setup kernel Lean 4 : `--wsl-only` / `--register` / `--validate` / `--check-wrapper` (orchestre WSL install + registration Windows + validation) — cf [docs/wsl-kernels-detail.md](wsl-kernels-detail.md) |
| `scripts/lean/lean_kernel_check.py` | Détection canonique régression wrapper kernel.json (#1618) : `inspect_kernel_wrapper` (partagé par les 2 validateurs + l'orchestrateur) |
| `scripts/lean/smoke_test_epita_is.py` | Smoke-test kernels Lean EPITA-IS |
| `scripts/lean/setup_shared_mathlib.ps1` | Mutualisation checkouts Mathlib via junctions NTFS (#2611) : `-Mode Scan` (inventaire groupes), `Apply` (cache `.mathlib-cache/` + junctions, `-Build` vérifie, `-RemoveBackups` libère l'espace), `Rollback` (restaure les checkouts physiques). Précondition : lake-manifest.json identique sur TOUTES les deps transitives + même lean-toolchain. Ne jamais `lake update` un projet junctionné |
| `scripts/mcp-maintenance/` | Maintenance MCP (config, docs, scripts) — cf `README_MCP_MAINTENANCE.md` |
| `scripts/validation/dispatch.py` + `matrix.yml` | Matrice de validation / dispatch |
| `scripts/genai-stack/genai.py` | GenAI Docker (ComfyUI + Qwen) + validation — cf [docs/genai/genai-services.md](../genai/genai-services.md) |
| `scripts/repair_genai_notebooks.py`, `scripts/audit_genai_corruption.py` | Réparation / audit corruption GenAI |
| `scripts/fix_robust_dotenv.py` | Robustesse chargement `.env` |
| `scripts/scan_student_forks.py` | Scan des forks étudiants |
| `scripts/series_progress_manager.py` | Suivi de progression des séries |
| `scripts/validate_qc_projects.py` | Validation projets QuantConnect |
| `scripts/update_navigation.py` | Mise à jour navigation README |
| `scripts/extract_pptx_titles.py`, `scripts/extract_slidev_titles.py` | Extraction titres slides (PPTX / Slidev) |
| `scripts/execute_with_env.py`, `scripts/execute_dotnet_notebook.py`, `scripts/execute_sudoku_python.py` | Wrappers d'exécution avec env |
| `scripts/quantconnect/`, `scripts/smartcontracts/`, `scripts/sudoku/`, `scripts/datasets/`, `scripts/tests/` | Outils par domaine |

## Tests — `scripts/tests/` + `scripts/notebook_tools/tests/`

46 fichiers de test dans `scripts/tests/`, 1729 tests au total (pytest). Couverture par domaine :

| Domaine | Fichiers | Modules couverts |
| ------- | -------- | --------------- |
| **notebook_tools/** | 14 | CLI principal (notebook_tools.py pure fn), helpers, skeleton, lint, catalogue (generate/expand/verify/coverage), qualite C.1/C.2/C.3, leak detection, forensic, execution (exec_single_cell, wsl_papermill, batch_reexecute, execute_qcpy_docker), enrich, reporting |
| **genai-stack/** | 8 | config.py, commands/validate.py, commands/audio_apis.py, commands/models.py, commands/notebooks.py, commands/auth.py, core/comfyui_client.py, core/auth_manager.py |
| **sudoku/core/** | 5 | solvers.py (Norvig CSP), graph.py (edge index), dataset.py (parse_81 + collate_fn), generation.py (grid + puzzles), models.py (SudokuRRN + count_params). evaluate.py = GPU-only, non CPU-testable |
| **top-level scripts/** | 7 | fix_robust_dotenv.py, extract_pptx_titles.py, extract_slidev_titles.py, validate_pr_notebooks.py, weekly_digest.py, validate_sc_notebooks.py, epita_prcon_autograde.py |
| **datasets/** | 2 | stitch_crypto.py, build_panier_anti_bias.py |
| **autres** | 10 | validate_qc_projects.py, series_progress_manager.py, update_navigation.py, scan_student_forks.py, catalog_coverage.py, qc_classify.py, forensic_scan.py, generate_parcours.py, check_c2_compliance.py, verify_catalog_readme.py |

Lancer la suite : `python -m pytest scripts/tests/ -v` (depuis la racine du repo).

Modules genai-stack non testes (intentionnellement) : commands/docker.py (subprocess Docker), commands/gpu.py (nvidia-smi subprocess), commands/quant.py (API externe).

## Voir aussi

- [docs/common-commands.md](common-commands.md) — setup env, validation notebooks, slash commands
- [docs/kernels-runtime.md](kernels-runtime.md) — .NET / Python / WSL kernels, conda envs
- [docs/genai/genai-services.md](../genai/genai-services.md) — scripts genai-stack, mappings notebooks
- [.claude/rules/wsl-kernels.md](../../.claude/rules/wsl-kernels.md) — Papermill WSL
