# Scripts Notebook Tools

Outillage canon de la partition `notebook_tools` du depot. Couvre la totalite
du cycle de vie notebook : detection anti-regression, validation CI,
execution, parsing, audits pedagogiques. **Cluster worker canonique**
(po-2024 + po-2025 + po-2026) pour les regles H.1-H.7 (validation reelle),
C.1-C.3 (notebooks), D (anti-regression), sota-not-workaround (#3801),
anti-banner (#6309), secrets-hygiene.

Le seul sous-dossier `scripts/` sans `README.md` avant ce fichier :
8 detecteurs + 3 validateurs + 2 scanners + 56 scripts utilitaires.
L'inventaire ci-dessous remplace la lecture en aveugle de 69 fichiers.

| Categorie | Scripts | Role |
|-----------|---------|------|
| **Detecteurs anti-regression** | `detect_blank_figures.py`, `detect_svg_decimal_commas.py`, `detect_ascii_workaround.py`, `detect_accent_stripping.py`, `detect_solution_leaks.py` | Flags deterministes par regle C.1 / H.1 / SOTA / #2876 / #4970 |
| **Validateurs CI** | `validate_pr_notebooks.py`, `check_c2_compliance.py`, `check_notebook_navlinks.py`, `check_plotly_static_risk.py` | Gates pre-merge, `--check` exit-code CI-ready |
| **Scanners structurels** | `scan_cell_ordering.py`, `scan_md_hierarchy.py` | Audit hierarchie markdown + ordre cellules pedagogiques |
| **Execution kernels** | `dotnet_executor.py`, `exec_dotnet_persist.py`, `exec_single_cell.py`, `batch_reexecute.py`, `wsl_papermill.py` | .NET Interactive + Python Papermill via WSL |
| **QC quantbooks** | `qc_quantbook_execute.py`, `qc_classify.py`, `execute_qcpy_docker.py`, `fix_qc_notebooks.py` | Subset QuantConnect (QuantBook non-executable via MCP) |
| **Anti-banner / hygiene** | `strip_probe_banner.py`, `strip_machine_paths.py`, `scrub_papermill_paths.py`, `audit_pip_install_cells.py`, `pip_leak_delta.py` | Stop & Repair (secrets-hygiene §6) + banner #6309 + pip leaks |
| **Catalogue & dashboards** | `generate_catalog.py`, `verify_catalog_readme.py`, `catalog_coverage.py`, `fix_catalog_drift.py`, `generate_health_dashboard.py`, `weekly_digest.py`, `extract_readme_figures.py` | Artefacts catalogue (#2632) + figures README + dashboards |
| **Audit & regression** | `audit_c1_c3.py`, `regression_scan.py`, `forensic_scan.py`, `diagnose_broken.py` | Audits structurels C.1/C.3 + regression cluster + diagnostics |
| **Extraction & parsing** | `notebook_tools.py`, `notebook_helpers.py`, `notebook_lint.py`, `extract_notebook_skeleton.py`, `count_exercises.py`, `count_notebooks_by_series.py`, `expand_catalog_markers.py`, `golden_set.yml`, `golden_set.lock.txt` | CLI multi-famille + helpers parsing + golden set |
| **C# / .NET persistence** | `_exec_bdd_csharp.py`, `_fix_gt15b_compilation.py`, `_fix_lean34_unused_vars.py` | Diagnostic + fix cibles C# specifiques (GT-15, Lean34) |
| **Leak-fix batch (legacy)** | `_fix_leaks_batch{1,2_probas,3_sudoku,4_remaining}.py`, `restructure_sw_2613.py` | Migration SW (#2613) + de-leak batchs legacy 2026 |
| **Divers** | `_alpha_diag.py`, `cell_order_ci.py`, `fix_audio_dependencies.py`, `fix_string_cells.py`, `flatten_import_notebook.py`, `generate_16e.py`, `generate_parcours.py`, `optimize_dvs.py`, `epita_prcon_autograde.py`, `sudoku_validate_outputs.py` | Cibles specifiques (diagnostics, EPITA autograde, parcours 16e) |

Tests unitaires dans `scripts/notebook_tools/tests/`.

---

## Detecteurs anti-regression (l'axe **DETECT**, jamais scrub)

Les 5 detecteurs implementent le **Prong A** de
[`.claude/rules/sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) :
detecter les sorties degradees qu'un notebook commit sans avoir execute le
vrai outil SOTA. Chaque detecteur a un **verdict deterministe** (zero faux
positif sur des sorties legitimes) et un mode `--check` CI-ready.

### `detect_blank_figures.py` (#6891)

Flag les figures PNG degenerees (1x1 px, ~70 o, blocks de couleur plats)
dans les outputs `image/png` d'un notebook. 0 faux positif : une vraie
figure PNG fait plusieurs Ko, pas 70 octets.

```bash
python scripts/notebook_tools/detect_blank_figures.py NB.ipynb --check
# exit 1 si defaut, CI-ready
```

**Owner** : QC-session pour les quantbooks (issue #6891) ; partition-mienne
pour les GenAI/Image.

### `detect_svg_decimal_commas.py` (#3801, EPIC #6927)

Flag les sorties SVG inline (`image/svg+xml` ou `text/html`) cassees par
le bug decimal-comma fr-FR : un `:F1` ou `double.ToString()` par defaut
sur machine fr-FR produit `"70,0"` au lieu de `"70.0"` -> SVG zigzag
sur Chromium/GitHub/nbviewer. Incident fondateur : PR #6946 (Infer-17).

```bash
python scripts/notebook_tools/detect_svg_decimal_commas.py --check
# sweep complet : 0/930 au 2026-07-17 post-#6946 amend canon
```

**Canon fix** : utiliser `CultureInfo.InvariantCulture` (ou helper canon
[Infer/SvgChartHelper.cs](../../MyIA.AI.Notebooks/Probas/Infer/SvgChartHelper.cs)
qui formate avec `.` en `private static string F(double v)` ligne 355,
cause-level propagation post-c.628).

### `detect_ascii_workaround.py` (#3801 Prong-A)

Detecte les charts ASCII (tableaux de caracteres, blocs Unicode) dans les
outputs de cellule en lieu d'une vraie figure generee. **Verdict Prong-A**
canon : un notebook qui commite de l'ASCII alors que matplotlib / Plotly /
service GenAI est invocable = workaround degrade INTERDIT.

### `detect_accent_stripping.py` (#2876)

Flag les cellules markdown/texte dont les accents francais ont ete
remplaces par leurs equivalentes ASCII (`a -> a`, `e -> e`, etc.) par
un pipeline de strip accidentel. **Rollout accent** : 183/183 cellules
traitees, ferme via Epic #2876.

### `detect_solution_leaks.py` (#4970, EPIC #1344)

Detecte les fuites de solution dans les cellules d'exercice :
verifie que les cellules de titre "Exercice" portent un stub
(`pass` / `return None` / `print("Exercice a completer")`) et non une
solution complete. Complementaire a
[.claude/rules/exercise-example-labeling.md](../../.claude/rules/exercise-example-labeling.md) :
labeling PAR CONTENU, pas par titre.

---

## Validateurs CI (l'axe **GATE**, pre-merge)

### `validate_pr_notebooks.py` (H.5 forensique)

Validateur principal pre-merge. Parse le diff et verifie pour chaque
notebook touche :

- **C.2** : `execution_count != null` ET `outputs != []` coherents
  (regle user 2026-04-26, JAMAIS committer un notebook sans outputs)
- **C.3** : scope strict re-exec Papermill (verifie `git diff` cellule
  source modifiee)
- **H.5 verdict** : `EXEC_PROVED` / `STRUCTURAL_ONLY` /
  `SUSPECT_REGRESSION` par parsing JSON du diff

Advisory `.NET execution_count` ≠ outputs vides autorises (#5214) : la CI
ne peut pas Papermill-exec les notebooks .NET, mais une cellule .NET
**DOIT** porter `execution_count != null` (preuve d'execution locale sur
chaque worker `dotnet-interactive`).

### `check_c2_compliance.py` (regle C.2)

Verification legere de la conformite C.2 (outputs presents, exec_count
non-null) sans parsing de diff. Pour audit/inventaire rapide.

### `check_notebook_navlinks.py` (#4959)

Verifie que les liens inter-notebooks d'un parcours (ex: Search Part 1 ->
Part 2) sont **non cassee** : cible renommee (stale-RESOLVES) = lien mort.
Methode : resolution de chemin relatif + check existence de la cible.

### `check_plotly_static_risk.py` (#6927)

Flag les notebooks Plotly.js-CDN (`<script src="https://cdn.plot.ly/...">`)
qui rendent en BLANC en static rendering GitHub/nbviewer. Issue : le
helper canon `SvgChartHelper.cs` (Infer) + pattern MIME `text/html` +
InvariantCulture est la voie de migration (Epic #6927).

---

## Scanners structurels (l'axe **PEDAGOGIE**)

### `scan_cell_ordering.py`

Verifie l'ordre logique des cellules (markdown intro -> code exemple ->
markdown interpretation -> code exercice -> ...) selon la convention
[.claude/rules/notebook-conventions.md](../../.claude/rules/notebook-conventions.md).

### `scan_md_hierarchy.py`

Audit hierarchie markdown : pas de saut H1->H3, titres uniques, structure
progressive pedagogique.

---

## Anti-banner / hygiene (Stop & Repair, secrets-hygiene §6)

### `strip_probe_banner.py` (#6309, #6312)

Le banner `probeAddresses` du kernel .NET Interactive est injecte dans
le PREMIER output `text/html` d'un notebook et embed les **interfaces
reseau de la machine hote** (LAN 192.168.x, Docker/WSL 172.x, IPv6
publique parfois). C'est un **leak machine-fingerprint** committe avec
les outputs.

- `--apply NB.ipynb` : strip chirurgical du banner (output-only surgical
  strip, conforme Stop & Repair, PAS un hand-edit de cellule)
- `--scan-all --check` : CI-ready gate
- Hook CI : `.github/workflows/banner-guard.yml`

**Hook executant** : la re-execution d'un notebook .NET re-injecte le
banner. Toujours `--apply` apres chaque re-exec .NET avant commit.

### `strip_machine_paths.py`, `scrub_papermill_paths.py`

Normalisent les chemins absolus machine dans les outputs :
`metadata.papermill.input/output_path` au `basename` (autorise par
secrets-hygiene §6 : metadata, pas un scrub d'output).

### `audit_pip_install_cells.py`, `pip_leak_delta.py`

Detecte les `!pip install` dans les cellules code avec fuite de cle
API / token / chemin machine. Hook CI : `.github/workflows/pip-leak-guard.yml`.

---

## QC quantbooks (subset QuantConnect)

`QuantBook()` requiert le SDK QC charge -- non-executable via MCP
`quantconnect/mcp-server`. Cf [docs/qc/quantconnect.md](../../docs/qc/quantconnect.md)
pour le fallback Playwright + execution **via QC Cloud** (`mcp__qc-mcp-lite__*`).

- `qc_quantbook_execute.py` : scaffolding execution locale (test mock)
- `qc_classify.py` : classifie un notebook QC (quantbook vs explore vs
  recherche)
- `execute_qcpy_docker.py` : variante Docker QuantConnect Lean engine
- `fix_qc_notebooks.py` : fix structures communes (imports,
  AddEquity calls)

**Regle user 2026-04-26** : QC quantbooks = exigence d'execution
**via QC Cloud**, JAMAIS de "markdown explicatif" comme contournement.

---

## Catalogue & dashboards (artefacts automatisation)

`generate_catalog.py`, `verify_catalog_readme.py`, `catalog_coverage.py`,
`fix_catalog_drift.py` : regeneration du catalogue (`COURSE_CATALOG.generated.json`,
marqueurs `<!-- CATALOG-STATUS:START -->...:END -->`).

**Regle HARD catalog-pr-hygiene R1** : JAMAIS regenerer le catalogue sur
une branche feature (propriete de l'automatisation). Qui regenere alors :

- `.github/workflows/catalog-cron.yml` (cron quotidien sur main, `[skip ci]`)
- `.github/workflows/catalog-drift.yml` (par-PR, auto-commit meme branche)

`generate_health_dashboard.py`, `weekly_digest.py`, `extract_readme_figures.py` :
dashboards cluster (etat sante, digest hebdomadaire, inventaire figures).
Sortie = dashboard RooSync / artefacts CI, JAMAIS dans le repo.

---

## Audit & regression

- `audit_c1_c3.py` : audit structurel conformite C.1 (pas d'erreur
  volontaire) + C.3 (scope re-exec). Verdict par notebook.
- `regression_scan.py` : scan cluster des symbols touches dans un diff
  vs reste du depot (regle B.5 anti-regression).
- `forensic_scan.py` : scanner forensics pour audit automatise (avec
  `regression_allowlist.json` pour les faux positifs reconnus).
- `diagnose_broken.py` : diagnostic notebook casse (execution_traceback
  et analyse statique).

---

## Extraction & parsing (la couche `lib`)

- `notebook_tools.py` : **CLI multi-famille** (2262 lignes) -- point
  d'entree canon pour les operations structurelles (`validate`,
  `execute`, `skeleton`, `analyze`).
- `notebook_helpers.py` : helpers parsing nbformat (1585 lignes).
- `notebook_lint.py` : linting structurel (333 lignes).
- `extract_notebook_skeleton.py` : extrait squelette (markdown +
  cellules stub) pour catalogues.
- `count_exercises.py`, `count_notebooks_by_series.py` : metriques
  regle #2161 (>= 3 exercices/nb pedagogique).
- `expand_catalog_markers.py` : expansion marqueurs `<!-- @dsCard -->` etc.
- `golden_set.yml` + `golden_set.lock.txt` : golden set de notebooks
  canoniques (regression baseline).

---

## Regle d'usage (HARD)

**Ne JAMAIS reecrire un script d'execution / validation / maintenance
ad-hoc.** Si un script manque, l'ajouter ICI (pas dans la racine
`scripts/`). Cette consigne est la propriete de la partition-mienne
Outillage commun canon (po-2024 + po-2025 + po-2026).

## Tests

`scripts/notebook_tools/tests/` : tests unitaires detecteurs + validateurs.
Lancer avant tout PR touchant cette partition :

```bash
python -m pytest scripts/notebook_tools/tests/ -v
```

## Voir aussi

- [.claude/rules/sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) -- Prong A (vrai outil SOTA) + Prong B (probleme non-trivial)
- [.claude/rules/secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) -- Stop & Repair §6 + scan gitleaks
- [.claude/rules/notebook-conventions.md](../../.claude/rules/notebook-conventions.md) -- C.1/C.2/C.3 (stubs sans erreur volontaire, outputs, scope re-exec)
- [.claude/rules/anti-regression.md](../../.claude/rules/anti-regression.md) -- preservation code production
- [.claude/rules/catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md) -- catalogue propriete automatisation
- [docs/reference/scripts-reference.md](../../docs/reference/scripts-reference.md) -- catalogue scripts depot (vue d'ensemble)
- **EPIC #3801** -- registre SOTA axe-2 + problem-richness
- **EPIC #6927** -- SVG inline rollout (helper canon SvgChartHelper.cs)
- **EPIC #6309** -- anti-banner probeAddresses durable
- **EPIC #2876** -- accents francais rollout
- **EPIC #2161** -- convention >= 3 exercices/nb
- **EPIC #4959** -- hubs + navlinks inter-notebooks
- **EPIC #4970** -- Planners de-leak + labelling
