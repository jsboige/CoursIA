# Réconciliation des dénominateurs de notebooks

> **Issue** : [#8050](https://github.com/jsboige/CoursIA/issues/8050) — réconcilier les dénominateurs forensic (934) / catalogue (830) / disque afin que les ratios « X % exécutés » soient interprétables.
>
> **Parent** : See [#4208](https://github.com/jsboige/CoursIA/issues/4208) (open-courseware fiabilisé). Cette note résout entièrement #8050.

## TL;DR — pourquoi 934 ≠ 830 ≠ 945

Quatre outils cohabitent et **mesurent des choses différentes**. Tant que le dénominateur varie, un ratio « 93 % exécutés » est ininterprétable. Les compteurs se réconcilient ainsi (SHA `644bb656d`, 2026-07-23) :

| Dénominateur | Compte | Outil | Ce qu'il mesure |
|---|---|---|---|
| **Disque (git-tracked)** | **945** | `git ls-files '*.ipynb'` | Tous les notebooks suivis par git (périmètre repo entier) |
| **Forensic (live)** | **943** | [`forensic_scan.py`](../../scripts/notebook_tools/forensic_scan.py) | Tous les notebooks sous `MyIA.AI.Notebooks/` sauf `_archives/_old/TrashBin/_output.ipynb/_pending_execution` |
| **Forensic (snapshot gelé)** | **934** | [`STABLE_SNAPSHOT.md`](../../STABLE_SNAPSHOT.md) (2026-07-17, SHA `d8ea11a`) | Le forensic **au moment du gel** — référence figée, pas le live |
| **Catalogue (curé)** | **830** | [`COURSE_CATALOG.generated.json`](../../COURSE_CATALOG.generated.json) | Les notebooks **pédagogiques primaires** (les jumeaux C#/.NET/Lean, les research QuantConnect, les examples et les outils ne sont pas listés séparément) |

**Corriger une prémisse fausse de l'audit originel** ([#8050](https://github.com/jsboige/CoursIA/issues/8050) body) : le forensic n'inclut **ni** `_output.ipynb` **ni** les `archives` — il les **exclut** ([`forensic_scan.py:117-125`](../../scripts/notebook_tools/forensic_scan.py), `EXCLUDE_DIRS` + `is_excluded`). Les seules choses que le forensic compte en plus du catalogue curé sont les notebooks `REFERENCE` (quantbooks `qc_reference`, 25) et les `NO_CODE`, classés comme catégories propres. Et le « 934 » du body est le nombre du **snapshot gelé**, pas le live (943 au SHA courant).

## Détail des écarts (vérifié firsthand, SHA `644bb656d`)

### 1. Disque (945) → Forensic (943) : −2

Le forensic exclut 2 notebooks situés dans `_archives/` :

- `SymbolicAI/SymbolicLearning/_archives/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Compose.ipynb`
- `SymbolicAI/SymbolicLearning/_archives/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Explore.ipynb`

> Note outillage : `git ls-files` échappe les chemins non-ASCII en octal (ex. `Cr/303/251ateur` pour `Créateur`). Ces 2 chemins échappés (`GenAI/SemanticKernel/Créateur…`, `Search/archive/…non-informée…`) apparaissent à tort comme « sur disque mais pas en forensic » — ce sont des **artefacts de quoting git**, les fichiers réels sont bien comptés dans les 943.

### 2. Forensic (943) → Catalogue (830) : écart net −114 / +1

| Ensemble | Compte |
|---|---|
| `forensic ∩ catalogue` | 829 |
| Forensic-only (en forensic, pas au catalogue) | **114** |
| Catalogue-only (au catalogue, pas en forensic) | **1** (fantôme, voir §4) |

**Les 114 forensic-only** se répartissent par série :

| Série | Forensic-only | Raison (non-catalogué car…) |
|---|---|---|
| QuantConnect | **99** | Notebooks **research / projets / examples** non pédagogiques : `projects/` 61, `research/` 17, `ML-Training-Pipeline/` 12, `partner-course-quant-trading/examples/` 7, `Python/` 2 |
| GameTheory | 5 | Jumeaux **C# / Lean** non listés séparément (le catalogue indexe l'entrée primaire) |
| Search | 4 | Jumeaux C# / variants |
| SymbolicAI | 2 | Variants / twins |
| GenAI | 3 | Notebooks `examples/` non primaires (voir §3) |
| GradeBook.ipynb (racine) | 1 | **Outil de notation**, pas un notebook pédagogique |

**Lecture** : le catalogue currise les **entrées pédagogiques primaires**. Les jumeaux C#/.NET/Lean d'un même concept, les notebooks de recherche QuantConnect, les dossiers `examples/` et les notebooks-outils (GradeBook) ne sont pas des entrées catalogue distinctes — d'où l'écart structurel et sain entre 943 (tout fichier) et 830 (pédagogique primaire).

### 3. GenAI : forensic 144 vs catalogue 141 (écart 3, ligne par ligne)

Les 3 notebooks GenAI comptés par le forensic mais absents du catalogue :

| Notebook | Pourquoi absent du catalogue |
|---|---|
| `GenAI/Image/examples/history-geography.ipynb` | Dossier `examples/` — cas d'usage illustratif, pas une entrée de série primaire |
| `GenAI/Image/examples/literature-visual.ipynb` | idem |
| `GenAI/Image/examples/science-diagrams.ipynb` | idem |

Aucun notebook du catalogue n'est absent du forensic côté GenAI (0 dans l'autre sens). L'écart 144 vs 141 est donc **entièrement expliqué** par les 3 notebooks `GenAI/Image/examples/`.

### 4. Le fantôme du catalogue (1 entrée catalogue non scannée)

Le catalogue référence `IIT/ICT-Series/ICT-15c-MetaProxyObstruction-executed.ipynb`, **mais ce fichier n'existe pas**. Le fichier réel est `IIT/ICT-Series/ICT-15c-MetaProxyObstruction.ipynb` (sans le suffixe `-executed`). Il s'agit d'une **entrée fantôme du catalogue** (résidu d'un renommage/suppression non propagé).

> Action : le catalogue est propriété de l'automatisation (`catalog-cron.yml` / `catalog-drift.yml`, cf [`.claude/rules/catalog-pr-hygiene.md`](../../.claude/rules/catalog-pr-hygiene.md)) — cette entrée fantôme sera nettoyée par le cron à la prochaine régénération. Ne pas éditer le catalogue sur une branche feature.

## Règles d'exclusion canoniques (par outil)

| Outil | Exclut | Inclut comme catégorie propre |
|---|---|---|
| `forensic_scan.py` | `_archive_obsoletes`, `_archives`, `_old`, `TrashBin`/`trashbin`, `.ipynb_checkpoints`, `node_modules`, `*_output.ipynb`, `*_pending_execution/` | `REFERENCE` (`qc_reference`), `NO_CODE`, `PARSE_ERROR` |
| `generate_catalog.py` | Jumeaux secondaires, research/projets QC, `examples/`, notebooks-outils (GradeBook), archives | — (curration pédagogique) |
| `git ls-files` | Untracked + gitignored uniquement | tout le suivi |

## Check CI léger : [`check_denominators.py`](../../scripts/notebook_tools/check_denominators.py)

Un script dédié rend cette réconciliation **vérifiable en continu** (acceptance « idéalement » de [#8050](https://github.com/jsboige/CoursIA/issues/8050)) :

- importe `is_excluded` de `forensic_scan` (donc **même périmètre** que le forensic, zéro dérive de logique) ;
- recalcule l'ensemble forensic (comptage rapide, sans catégorisation lourde) et l'ensemble catalogue ;
- **détecte les entrées fantômes du catalogue** (catalogue → fichier inexistant) — c'est le signal CI actionnable (le seul écart qui indique un vrai bug, pas une exclusion saine) ;
- catégorise le forensic-only (research QC / jumeaux / examples / outils) pour qu'un écart inattendu soit visible ;
- exit 1 si une entrée catalogue pointe vers un notebook absent du disque.

```
python scripts/notebook_tools/check_denominators.py [--root MyIA.AI.Notebooks]
```

Le check est **intentionnellement non bloquant sur l'écart structurel** (forensic 943 vs catalogue 830 est sain : les deux mesurent des choses différentes). Il **bloque uniquement** sur les entrées fantômes du catalogue (drift = bug réel).

## Méthode (G.1, reproductible)

```
# 1. Forensic live (parse JSON seul, ~30 s, zéro exécution de notebook)
python scripts/notebook_tools/forensic_scan.py --root MyIA.AI.Notebooks --json-out /tmp/forensic.json

# 2. Réconcilier (cf scripts/notebook_tools/check_denominators.py)
python scripts/notebook_tools/check_denominators.py
```

Chaque chiffre de cette note est issu d'une exécution firsthand au SHA `644bb656d` (2026-07-23), pas d'une lecture de snapshot. Le snapshot `STABLE_SNAPSHOT.md` (934) est une **référence gelée** à `d8ea11a` (2026-07-17) — entre les deux, +9 notebooks ont été ajoutés, ce qui explique 934 → 943.
