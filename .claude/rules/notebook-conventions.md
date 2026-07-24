---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Notebook Conventions

**Regles user (C.1/C.2/C.3 detaillees)** : voir CLAUDE.md section C.

## Manipulation

- Utiliser `scripts/notebook_tools/notebook_helpers.py` et `notebook_tools.py` (PAS de code Python ad-hoc)
- `NotebookEdit` pour cell-level changes — references par `cell_id`, pas par index
- Insertions multiples : travailler BAS vers HAUT (evite index shift)
- Re-read le notebook apres chaque edit (indices changent)
- `git diff` apres modifs : enrichissement = insertions > deletions

## Structure pedagogique

- Header obligatoire : navigation, objectifs d'apprentissage, prerequis, duree estimee
- Pas de cellules code consecutives sans markdown entre elles
- Interpretation APRES chaque output significatif
- Introduction de section AVANT le code qu'elle introduit
- Conclusion avec table recap en fin de section majeure

## Enchainement et ordre canonique des cellules (Epic #3240)

Les cellules doivent suivre un **ordre canonique** sans glissement ni oubli. Friction observee en cours ("certaines choses n'etaient pas a leur place"). Regles :

- **Numerotation monotone** : un en-tete numerote (`## 3.`, `### 3.2`) ne revient jamais en arriere sous le meme parent. Un redemarrage a 1 = nouveau groupe legitime (nouvelle partie / apres un sommaire).
- **Exercice/Exemple ordonnes** : les labels `Exercice N` / `Exemple N` sont en ordre croissant dans leur sequence respective (les deux cohabitent, cf [exercise-example-labeling.md](exercise-example-labeling.md)).
- **Pas d'intro orpheline** : une cellule markdown qui annonce du code imminent ("executons le code ci-dessous :") est **suivie** d'une cellule code (sinon = cellule oubliee/deplacee).
- **Interpretation APRES le code** : un markdown d'interpretation ("on observe que...") suit l'output qu'il commente, jamais avant.

**Outil** : `scripts/notebook_tools/scan_cell_ordering.py` (`<nb>` | `--family <subpath>` | `--all`, `--severity`, `--fail-on`). Skill `/check-cell-order`. Chaque finding HIGH se **ground-truth** avant correction (G.1 — le signal n'est pas un verdict). Un reorder via `NotebookEdit` **vide les outputs** -> re-executer (C.2) avant commit. Detail workflow : skill `/check-cell-order`.

## Execution

- **Python notebooks** : Papermill pour batch (`notebook_tools.py execute <path>`)
- **.NET notebooks** : Papermill avec kernel `.net-csharp` fonctionne (verifie SW-3, 50/50 cells). Sauf `#!import` (MCP Jupyter cell-by-cell en fallback). Prefere Papermill quand possible.
- **.NET figures Plotly** (Prong-A #3801) : `#r "nuget:"` charting est bloque headless (c.547-L1) → utiliser la technique **C548-L2 « zero-restore »** (`record PlotlyHtml` + `Formatter.Register` + Plotly.js CDN, zero NuGet), jamais un workaround ASCII. Template canonique + piege du `layout` 3e argument + gate de merge : [docs/reference/dotnet-plotly-zero-restore.md](../../docs/reference/dotnet-plotly-zero-restore.md).
- **WSL notebooks** (GameTheory/Lean) : `wsl_papermill.py` (cf [.claude/rules/wsl-kernels.md](wsl-kernels.md))
- Working directory explicite pour notebooks avec paths relatifs
- `BATCH_MODE=true` pour notebooks avec widgets interactifs
- **Notebooks LLM/API** (SC-11, GenAI) : re-exec validation via `--scrub-keys` pour forcer le chemin mock deterministe sans appel API payant : `notebook_tools.py execute <path> --scrub-keys`. Cf [docs/scripts-reference.md](../../docs/reference/scripts-reference.md) pour le cookbook complet (`--kernel`, `--cwd`, `--env`, `--scrub-keys`).
- **QuantConnect QuantBook notebooks** (L574 ★★) : re-exec **QC Cloud uniquement** via MCP `qc-mcp` (`create_compile` + `create_backtest` + `read_backtest`). Tentative Papermill locale = FAIL (kernel `QuantBook()` absent, exécution QC Cloud obligatoire). Validateur `scripts/audit/check_cost_metadata.py` lit `cost.validator == qc_cloud` pour ces notebooks (sinon `MAJOR qc_notebook_no_validator`). Cf [CLAUDE.md QUANTCONNECT](../../CLAUDE.md#quantconnect-resume) pour la discipline backtest obligatoire après modification.

## Cellules code : output systematique (anti faux-positif maturite)

**Convention user 2026-05-31.** Toute cellule code executable doit produire un **output**, pour que la porte catalogue `all_have_outputs` soit un signal **vrai** (et non un cas a forgiver cote detecteur). On corrige l'**artefact**, pas l'instrument de mesure.

- Cellule setup / imports / defs / guards qui ne produit rien naturellement => ajouter un **print informatif de confirmation** : `print("Imports OK : semantic_kernel, nest_asyncio")`, `print(f"Kernel configure : {kernel.service_id}")`, `print(f"{len(funcs)} fonctions definies")`.
- **Print informatif, jamais du bruit.** `print("ok")` repete partout = gaming du detecteur (famille incident #1214), INTERDIT. Le print doit dire ce que la cellule a accompli.
- **JAMAIS printer une valeur de secret / cle** (`print(api_key)` interdit). Confirmer la presence sans reveler : `print("Cle API chargee" if key else "Cle MANQUANTE")`.
- Stub d'exercice : garde `print("Exercice a completer")` (deja conforme C.1, aucun changement).
- **Un print ne remplace PAS l'execution reelle** : une cellule LLM/API doit montrer sa **vraie** reponse, pas un `print("done")` creux sur un appel echoue. Provisionner le `.env` d'abord (regle F), puis re-executer.
- **Forward convention** : appliquer en editant/finalisant un notebook (surtout pour le faire passer BETA -> PROD) et pour tout nouveau notebook. Ne PAS reserialiser en masse des notebooks deja PRODUCTION juste pour ajouter des prints (churn C.3 interdit).

## Patterns stub d'exercice (rule C.1)

`raise NotImplementedError` / `assert False` / `1/0` **INTERDITS partout** (notebook doit s'executer end-to-end). Patterns corrects :

| Contexte | Pattern |
|----------|---------|
| Top-level | `print("Exercice a completer")` ou `pass` |
| Methode classe | `def foo(self): pass  # TODO etudiant : <desc>` |
| Fonction utilitaire | `def helper(...): return None  # TODO etudiant` |
| Variable attendue | `result = None  # TODO etudiant : remplacer par compute_thing()` |

Preserver TOUS les commentaires `# TODO`, `# Indice`, `# Etape N`. Remplacer `raise NotImplementedError` legacy par ce pattern = **conforme**, anti-regression ne s'applique pas.

## Commit avec outputs (rule C.2)

Tout notebook committe : `execution_count: <int>` + `outputs: [...]` coherents pour chaque cellule code executable. Modification source = re-execution complete avant commit. Exception : modifs uniquement markdown → outputs precedents valides.

## Scope strict re-execution (rule C.3)

Commit UNIQUEMENT les notebooks dont la source a change (`git diff <nb> | grep -cE '^\+\s*"source"' > 0`). Pour audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas dans le repo.

## Interprétation grounded (rule C.4)

**Convention issue #8364 (EPIC #8052).** Une cellule markdown d'interprétation ne cite **que** des valeurs présentes dans les outputs observés des cellules de code adjacentes (ou explicitement référencées). Complète le positionnement canonique « Interpretation APRES le code » (section *Enchainement* ci-dessus) en gouvernant le **contenu** cité, non plus seulement l'ordre.

- Une valeur citée absente de l'output → **re-executer pour la mesurer** (règle F HARD : install/invoke/re-plug le vrai outil, cf [sota-not-workaround.md](sota-not-workaround.md) Stop & Repair), ou **reformuler sans la citer**. Jamais de prose écrite d'abord puis « validée » contre l'output après.
- **Pour une PR « alignement doc-honesty »** : ne JAMAIS ré-aligner la prose sur un output qui la contredit sans **diagnostiquer la cause de la dérive**. Une contradiction prose↔output signale que le notebook a dérivé (env défectueux, claim antérieure fabriquée, moteur qui change, stochasticité non-seedée). Verdict obligatoire dans le body PR :

| Verdict | Critère | Action |
|---------|---------|--------|
| `CAUSE_FIXED` | Cause racine corrigée (env réparé règle F, claim antérieure revertée, seed ajouté) | Merge OK |
| `CAUSE_DOCUMENTED_ONLY` | Cause identifiée, non traitée (ré-alignement cosmétique = « jambe de bois repeinte ») | Issue fille ouverte + `See #N` |
| `CAUSE_INTRINSIC` | Cause structurelle non corrigeable (moteur upstream cassé sans alternative) | Bandeau honnête + issue engine-fix |

Ré-aligner sans diagnostic = consacrer la dégénérescence : le notebook re-dérive au cycle suivant (cf vague SW-13 #7751→#7872→#7944→#8343, 4 PRs pour colmater des claims fabriquées en série). Voir aussi [sota-not-workaround.md](sota-not-workaround.md) (axe-2 SOTA), [secrets-hygiene.md](secrets-hygiene.md) règle 6 (jamais hand-editer un output — corriger la cause + re-executer).

