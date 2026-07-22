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
| `pip_leak_delta.py` | **Guard delta pip-leak** : compare deux scans JSON d'`audit_pip_install_cells.py` et fail si la PR introduit des leaks HIGH *nouveaux* (pas un fail absolu `--check` — le repo porte encore des HIGH hérités drainés un-PR-par-notebook). CI-ready (exit 1 sur delta > 0) |
| `detect_fabricated_outputs.py` | Détecteur **sorties textuelles FABRIQUÉES** committes comme résultats d'exécution (Prong-A, registre #3801) : placeholder textuel (`Row N`) ou dataframe backtest-entièrement-à-0.0 en lieu et place du vrai résultat. Companion image-axis de `detect_blank_figures.py` |
| `strip_fabricated_quantbook_outputs.py` | Strip des sorties text/PNG fabriquées des `quantbook.ipynb` (cf #6891, Side A). Les 8 quantbooks QC non-ré-exécutables via MCP portaient des outputs fabriqués ; cet outil les retire proprement (exception quantbook QC, cf secrets-hygiene §6) |
| `detect_bare_cross_dir_load.py` | Détecte un `#load "X.cs"` **bare** (nom nu, sans séparateur) dont le `.cs` n'existe PAS dans le dossier du notebook — anti-pattern du rollout SVG inline (#6927) où le kernel résout un `#load` relatif et échoue silencieusement / charge le mauvais fichier |
| `check_notebook_navlinks.py` | Vérifie les liens de navigation relatifs **cassés dans les cellules markdown des `.ipynb`** (« précédent / suivant »). `check_docs_links.py` couvre uniquement les fichiers markdown (CLAUDE.md, docs/, README) ; cet outil couvre le markdown *intérieur* des notebooks |
| `check_plotly_static_risk.py` | Détecte les cellules Plotly-CDN dans les `.ipynb` = **blanc en static rendering** (cf #6927). Le pattern canonique `record PlotlyHtml + Formatter.Register` émet un `<script src="https://cdn.plot.ly/...">` externe qui rend en kernel live mais pas sur GitHub/nbviewer |

### Render-suite SVG inline (rollout #6927)
La migration Plotly-CDN → SVG inline `text/html` (canon ai-01 `svg-6927-canon.md`) est gardée par 5 détecteurs couvrant tous les cas de figure cassé. `detect_svg_decimal_commas.py` (dans la section Tests ci-dessous) traite le cas virgule-décimale fr-FR.
| Script | Usage |
|--------|-------|
| `detect_svg_broken_geometry.py` | Détecte les sorties SVG dont un élément a une **dimension négative** (`rect`/`use`/`image` à `width='-...'` ou `height='-...'`) = élément invisible, rendu cassé |
| `detect_svg_empty_display.py` | Détecte les cellules .NET qui `display()` un chart SVG mais produisent un output **vide** (figure blanche sur GitHub/nbviewer) |
| `detect_svg_offscreen_flat.py` | Détecte les SVG **plats** dont une géométrie de données est projetée au-delà du viewBox (>15% de sa hauteur) : barre/ligne/point rendu hors cadre = figure amputée (cas résiduel que les autres détecteurs ne voient pas) |

### Papermill forensic & path-leak (anti-leak metadata)
| Script | Usage |
|--------|-------|
| `detect_papermill_failed_state.py` | Détecte les notebooks dont l'exécution papermill ne s'est pas terminée proprement (#7079) : inspecte le bloc **top-level** `metadata.papermill` → deux classes `papermill_hard_failure` (exception non-None) et `papermill_pending` (status="pending") |
| `detect_papermill_cell_level_state.py` | Companion **cell-level** du précédent : papermill écrit un status par-cellule que le détecteur top-level ne voit pas. Inspecte `metadata.papermill` de chaque cellule pour les échecs granulaires |
| `detect_papermill_path_leak.py` | Détecteur **read-only** des fuites de chemins machine-locales dans les notebooks (companion de `scrub_papermill_paths.py`). Deux classes content-based : leak `metadata.papermill` chemin absolu + fuites dans les outputs. Cf secrets-hygiene §6 Stop & Repair (on ré-exécute, on ne scrubbe pas les outputs) |
| `scrub_papermill_paths.py` | Scrub des chemins absolus machine-locaux du metadata papermill (`metadata.papermill.output_path`/`input_path` au basename). **Seule normalisation manuelle tolérée** hors outputs (metadata, pas une sortie de cellule) — cf secrets-hygiene §6 exceptions |

### Cure des accents FR & gates de régression — #2876
| Script | Usage |
|--------|-------|
| `detect_accent_stripping.py` | Détecteur historique : dictionnaire conservateur `ACCENT_PAIRS` (source de vérité partagée). Le stripped form n'est pas un mot FR valide → non-ambigu |
| `detect_link_target_regression.py` | Détecteur de **régression des accents dans les TARGETS de liens markdown** `[texte](cible)` (registre #2876). Un cure ad-hoc par regex globale `\b(mot)\b` peut accentuer la cible d'un lien → 404 ; cet outil garde les targets intacts |
| `restore_accents_canonical.py` | **CURE canonique** (PR #7186). Markdown-only STRICT by construction : skip code/outputs/link-targets, préserve casse + structure (paragraph breaks). 4 bright-lines + 1 structurelle. Référence complète : [accent-cure-defense-in-depth.md](accent-cure-defense-in-depth.md) |
| `check_identifier_regression.py` | **GATE identifiants code** (PR #7157, MERGÉ). Détecte l'over-reach (cure qui accentue un identifiant). `_STRIP_RE` retire commentaires+chaînes avant comparaison base(main) vs head(branche). CI-ready (exit 1) |
| `detect_caps_regression.py` | **GATE caps** (PR #7198 MERGÉ ; #7197 CLOSED, son contenu absorbé en git-ref mode par PR #8917bd71b). Détecte une cure qui minuscule l'initiale capitalisée (H1/H2/table-header/début-phrase/all-caps). Scan line-aligned positionnel (clé anti-FP) |

**Workflow PR accents** : générer via `restore_accents_canonical.py` (passe les gates by construction), jamais via un script ad-hoc. Périmètre, défense-in-depth (3 rôles), 4 classes de défauts, bright-lines, méthodologie : cf [accent-cure-defense-in-depth.md](accent-cure-defense-in-depth.md).

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
| `scripts/lean/check_i18n_siblings.py` | **Checker i18n sibling-pair** (EPIC #4980) : vérifie la byte-identity du **body** (signatures, preuves, tactiques) entre un `Foo.lean` FR-canonical et son miroir `Foo_en.lean`. Seules les docstrings/commentaires diffèrent. Sorties `OK` / `OK-CONSUMER` / `DRIFT` / `ORPHAN` = point de départ d'investigation, jamais un grain verbatim (3 formes légitimes, cf [i18n-sibling-patterns.md](../lean/i18n-sibling-patterns.md)) |
| `scripts/lean/po2026_recover_build.py` | **Recette récupération `lake build`** po-2026 (codification #6771, self-repair règle F) : cold-rebuild unreliable → script documenté dans [po2026-local-build-troubleshooting.md](../archive/po2026-local-build-troubleshooting.md) (archivé c.700, canonique = script 309L). Valide firsthand sur knot_lean |
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

`scripts/tests/` regroupe **56 fichiers** de test (1701 tests) ; `scripts/notebook_tools/tests/` en regroupe **82** (3199 tests — couvre les modules notebook_tools : CLI, helpers, skeleton, lint, catalogue, qualité C.1/C.2/C.3, leak detection, forensic, execution, enrich, reporting), soit **4900 tests au total** (snapshot `pytest --collect-only` 2026-07-21). Couverture de `scripts/tests/` par domaine :

| Domaine | Fichiers | Modules couverts |
| ------- | -------- | --------------- |
| **genai-stack/** | 9 | config.py, commands/{validate,audio_apis,models,notebooks,auth,gpu}.py, core/{comfyui_client,auth_manager}.py, models.py |
| **sudoku/** | 9 | core/{solvers,graph,dataset,generation,models,training,evaluate}.py, sudoku_rrn, sudoku_solvers (evaluate.py = GPU-only, partiellement couvert) |
| **smartcontracts/** | 2 | validate_sc_notebooks.py |
| **extract-titles (top-level)** | 4 | extract_pptx_titles.py, extract_slidev_titles.py, extract_titles.py, extract_readme_figures.py |
| **ml/** | 1 | garch_baseline |
| **autres (top-level + misc)** | 26 | check_docs_links, convert_print_to_deploy, regen_quarto_render, render_envs (secrets), scan_student_forks, series_progress_manager, update_navigation, validate_qc_projects, execute_sudoku_python, execute_qcpy_docker, translation_sync, translate_csv, detect_{ascii_workaround,blank_figures,svg_decimal_commas}, verify_{prosody,transcript}, audit_exposed_services, auth_manager, configure_max_quantization, container_startup, download_yfinance, manage_crypto_archive, notebook_tools_pure, repair_genai_notebooks, validation_dispatch |

Lancer la suite : `python -m pytest scripts/tests/ -v` (depuis la racine du repo).

Modules genai-stack non testes (intentionnellement) : commands/docker.py (subprocess Docker), commands/quant.py (API externe).

## Voir aussi

- [docs/common-commands.md](common-commands.md) — setup env, validation notebooks, slash commands
- [docs/kernels-runtime.md](kernels-runtime.md) — .NET / Python / WSL kernels, conda envs
- [docs/genai/genai-services.md](../genai/genai-services.md) — scripts genai-stack, mappings notebooks
- [.claude/rules/wsl-kernels.md](../../.claude/rules/wsl-kernels.md) — Papermill WSL
