# Réconciliation des dénominateurs de notebooks — forensic / catalogue / disque

> **Objet.** Cartographier, au même SHA, les 4 dénominateurs de notebooks utilisés
> par les outils du dépôt, et expliciter les règles d'exclusion de chacun. Répond à
> l'issue #8050 (P0, lane po-2023 — tooling/metadata).
>
> Toutes les valeurs ci-dessous sont **calculées firsthand** au SHA
> `ae7cffdb011198f3ea2b6a226e10862d3d788c5b` (origin/main), pas reprises d'un
> snapshot antérieur.

## 1. Les 4 dénominateurs au SHA `ae7cffdb0`

| Dénominateur | Valeur | Outil | Méthode de parcours |
|---|---|---|---|
| **Disque (git-tracked)** | **946** | `git ls-tree -r --name-only origin/main` | tous les `.ipynb` sous `MyIA.AI.Notebooks/` |
| **Forensic scan** | **944** | `scripts/notebook_tools/forensic_scan.py` | parcours filesystem (`rglob`) sous `MyIA.AI.Notebooks/`, exclusions voir §2 |
| **Catalogue (committé)** | **830** | `COURSE_CATALOG.generated.json` @ origin/main | parcours pédagogique (`generate_catalog.py`), généré 2026-07-22 06:12 |
| **Catalogue (regen frais)** | **832** | `generate_catalog.py` au même SHA | idem, régénéré localement — voir §5 (dérive de 2) |

### Correction d'une valeur de l'issue (G.1)

L'issue #8050 cite **« forensic = 934 »**. Au SHA courant, forensic = **944**, pas 934.
Le chiffre 934 provient d'un snapshot antérieur ; il est stale. Toute décision basée
sur 934 doit repartir de 944 (recommandé : `python scripts/notebook_tools/forensic_scan.py`).

## 2. forensic_scan.py — règles d'exclusion (946 → 944, −2)

Source : `scripts/notebook_tools/forensic_scan.py` (lignes 25, 98-106, 118, 131).

Forensic parcourt le **filesystem** (`root.rglob("*.ipynb")`, `--root MyIA.AI.Notebooks`)
et exclut un notebook si (`is_excluded`, ligne 98) :

- un segment de chemin est dans `EXCLUDE_DIRS = {.ipynb_checkpoints, TrashBin,
  _archive_obsoletes, _archives, _old, node_modules, trashbin}` ;
- **ou** le nom finit par `_output.ipynb` (artefacts Papermill, `ARTIFACT_SUFFIXES`) ;
- **ou** le chemin contient un segment `_pending_execution`.

Au SHA courant, seuls **2 fichiers** tombent dans ces exclusions (dir `_archives` /
`_old`). D'où 946 − 2 = **944**.

Forensic est donc le dénominateur le **plus large** des outils « pédagogiques » :
il garde les dossiers `research/`, `archive/`, `examples/`, `partner-course/`,
`projects/`, `ML-Training-Pipeline/` que le catalogue exclut (§3).

## 3. generate_catalog.py — règles d'exclusion (946 → 830, −116)

Source : `scripts/notebook_tools/generate_catalog.py` (lignes 36-39, 698-735, 534-542).

Le catalogue parcourt `MyIA.AI.Notebooks/` **répertoire-série par répertoire-série**
(`NOTEBOOKS_DIR.iterdir()`, ligne 707 ; seuls les **sous-répertoires** top-level sont
parcourus — un `.ipynb` posé à la racine de `MyIA.AI.Notebooks/` n'est jamais vu).

Deux ensembles d'exclusion (ligne 38-39) :

```python
EXCLUDE_ALWAYS     = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "output", "partner-course", "examples"}
```

`EXCLUDE_PEDAGOGICAL` est appliquée en mode pédagogique (défaut) par un test de
**sous-chaîne** sur le chemin relatif à la série (ligne 726-730) :

```python
any(exc in str(nb_path.relative_to(series_dir)) for exc in EXCLUDE_PEDAGOGICAL)
```

Conséquence importante : la correspondance est une **sous-chaîne**, pas un segment.
`"research"` exclut donc **à la fois** le dossier `/research/` **et** tout fichier dont
le nom contient `research` (ex. `m4_dlinear_vol_research.ipynb`, `research_l1_tsmom.ipynb`).

`analyze_notebook` (ligne 534) ne renvoie `None` que sur échec de parsing JSON
(`JSONDecodeError` / `UnicodeDecodeError`). Sinon elle produit toujours une entrée.

### Décomposition des 114 exclus (946 disque − 832 catalogue frais)

Calculé par diff exact de l'ensemble des chemins (fresh regen 832) vs `git ls-tree` (946) :

| Raison | Nombre | Détail |
|---|---|---|
| `QuantConnect/projects/` non catalogués | 61 | stratégie/scaffolding QC (le catalogue QC = 105 vient surtout des notebooks Python/research hors `projects/`) |
| sous-chaîne `research` (dossier `/research/`) | 19 | QC 17, autres 2 |
| sous-chaîne `examples` | 7 | GenAI/…/examples |
| sous-chaîne `archive` | 4 | |
| sous-chaîne `research` (nom de fichier `*_research.ipynb`) | 11 | `QuantConnect/ML-Training-Pipeline/*_research.ipynb` |
| sous-chaîne `partner-course` + `research` | 4 | `QuantConnect/partner-course-quant-trading/kit-transitoire/…/research.ipynb` |
| dirs d'archive (`_archives`/`_old`) | 2 | (exclus aussi par forensic) |
| fichier racine (hors sous-répertoire-série) | 1 | `GradeBook.ipynb` — jamais parcouru (walk = dirs top-level uniquement) |
| **résidu non expliqué** | **5** | voir §6 |

Total : 61 + 19 + 7 + 4 + 11 + 4 + 2 + 1 + 5 = **114**.

> Note : 114 = 946 − 832 (regen frais). Versus le catalogue **committé** (830), le delta
> est 116 ; la différence de 2 est la dérive §5.

## 4. GenAI 144 → 141 (−3) — ligne par ligne, **clos**

Le décompte disque de la famille GenAI (144) se décompose en sous-répertoires-séries :
Audio 30, Texte 20, SemanticKernel 20, Image 20, Video 17, PostTraining 7, Open-WebUI 7,
Vibe-Coding 6, 00-GenAI-Environment 6, FineTuning 5, CaseStudies 4, RAG 1, racine 1.

Le catalogue en compte **141**. Les **3 exclus** sont exactement les notebooks GenAI
situés dans un sous-répertoire `EXCLUDE_PEDAGOGICAL` (règle §3, sous-chaîne) :

```
GenAI/…/research/…       (1)
GenAI/…/examples/…       (1)
GenAI/…/archive/…        (1)
```

Le compte « TEMPLATE: 3 » du catalogue GenAI est un **label de maturité** (fichiers
*inclus* classés TEMPLATE), pas une exclusion — ces 3 TEMPLATE font partie des 141.
L'écart 144→141 est donc **entièrement expliqué** par les 3 fichiers en dossiers
pédagogiques-exclus.

## 5. Dérive du catalogue committé (830) vs regen frais (832)

Un regen local au même SHA produit **832** entrées, soit **2 de plus** que le
`COURSE_CATALOG.generated.json` committé (830, généré 2026-07-22 06:12). Les 2
notebooks présents au regen frais mais absents du catalogue committé :

```
Search/Part4-Metaheuristics/MGS-7c-RosenbrockGriewank.ipynb
Search/Part4-Metaheuristics/MGS-7d-MichalewiczDixonPrice.ipynb
```

Ce sont 2 notebooks ajoutés après la dernière régénération cron du catalogue. Le cron
quotidien (`catalog-cron.yml`) les intégrera au prochain cycle — **aucune action manuelle
requise** (cf [.claude/rules/catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md) :
le catalogue appartient à l'automatisation).

## 6. Résidu ouvert — 5 `GameTheory-8-CombinatorialGames*`

5 notebooks restent exclus du catalogue **sans** correspondre à aucune règle documentée :

```
GameTheory/GameTheory-8-CombinatorialGames.ipynb
GameTheory/GameTheory-8-CombinatorialGames-Csharp.ipynb
GameTheory/GameTheory-8b-Lean-CombinatorialGames.ipynb
GameTheory/GameTheory-8c-CombinatorialGames-Csharp.ipynb
GameTheory/GameTheory-8c-CombinatorialGames-Python.ipynb
```

Vérifications faites (firsthand) : JSON valide (24-26 cellules), fichier tracké à
origin/main, aucun segment `EXCLUDE_PEDAGOGICAL`, pas en `EXCLUDE_DIRS`, pas `_output`.
Pourtant, un regen frais les exclut tous les 5, alors que `GameTheory-1-Setup`,
`GameTheory-10-*`, etc. sont bien catalogués. Cause racine **non identifiée** dans ce
passage (piste : chemin `analyze_notebook` de retour `None` au-delà du parsing, ou
déduplication par titre ; à investiguer dans un follow-up). **Ce résidu est documenté
ici volontairement (G.2) plutôt que masqué.**

## 7. Reproduire les chiffres

```bash
SHA=ae7cffdb011198f3ea2b6a226e10862d3d788c5b

# Disque (git-tracked)
git ls-tree -r --name-only $SHA | grep 'MyIA.AI.Notebooks/.*\.ipynb$' | wc -l   # = 946

# Forensic (recommandé ; le 934 de l'issue est stale → 944)
python scripts/notebook_tools/forensic_scan.py 2>&1 | head -1                    # = 944

# Catalogue (regen frais au même SHA)
python scripts/notebook_tools/generate_catalog.py --json-only                   # = 832
python -c "import json;d=json.load(open('COURSE_CATALOG.generated.json'));print(len(d))"

# Catalogue (committé)
git show $SHA:COURSE_CATALOG.generated.json \
  | python -c "import json,sys;print(len(json.load(sys.stdin)))"                 # = 830
```

## 8. Suggestion de garde-fou CI (optionnel, non livré ici)

Pour empêcher la re-staleness du dénominateur, un check léger pourrait comparer le
`Total notebooks:` du `COURSE_CATALOG.generated.md` committé au regen frais et FAIL
si l'écart dépasse un seuil (ex. > 5, pour tolérer le drift entre deux runs cron).
**Non implémenté dans ce passage** — laissé comme suite possible de #8050.

## Récapitulatif

- **946** (disque) → **944** (forensic) : exclusion des dirs d'archive (`_archives`,
  `_old`, …) + suffixe `_output.ipynb`.
- **946** (disque) → **830** (catalogue committé) / **832** (regen frais) : exclusion
  pédagogique par **sous-chaîne** (`research`, `archive`, `examples`, `partner-course`,
  `output`, `_output`) + `QuantConnect/projects/` + fichiers hors-série-racine.
- **GenAI 144 → 141** : 3 fichiers en dossiers pédagogiques-exclus (**clos**).
- **Issue « 934 »** : stale, forensic = **944** au SHA courant (**corrigé**).
- **Résidu ouvert** : 5 `GameTheory-8-*` exclus sans règle identifiée (§6).
