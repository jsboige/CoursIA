# Compteurs de notebooks — catalogue / outil / disque

**Date** : 2026-08-07
**Issue** : [#9857](https://github.com/jsboige/CoursIA/issues/9857)
**Lane** : po-2023 (CoursIA-2)

---

## TL;DR — les trois compteurs au même SHA (`e7307a717`, 2026-08-07)

| Source | Compte | Définition courte | Répond à la question |
|--------|-------:|-------------------|----------------------|
| **Catalogue** | **863** | `COURSE_CATALOG.generated.json` (cron `catalog-cron.yml`) | « Combien de notebooks le dépôt **présente** publiquement ? » |
| **Outil** | **863** | `count_notebooks_by_series.py` (mode pédagogique) | « Combien de notebooks **pédagogiques** (hors recherche/archive/artefacts) ? » |
| **Disque** | **974** | `find MyIA.AI.Notebooks -name '*.ipynb'` (hors `.ipynb_checkpoints`) | « Combien de fichiers `.ipynb` **physiquement présents** ? » |

> **Les compteurs catalogue et outil convergent à 863** depuis le correctif
> `#9851` (bug `bin`/`CombinatorialGames` qui sous-comptait l'outil à 866).
> L'écart résiduel **863 vs 974 = 111 fichiers** est entièrement expliqué par
> les règles d'exclusion ci-dessous (réconciliation fichier-près, qui se
> referme exactement).

---

## Les trois définitions, en détail

### 1. Catalogue — `COURSE_CATALOG.generated.json` (863)

**Source** : le fichier généré par [`scripts/notebook_tools/generate_catalog.py`](../../scripts/notebook_tools/generate_catalog.py), régénéré quotidiennement par le cron [`.github/workflows/catalog-cron.yml`](../../.github/workflows/catalog-cron.yml) sur `main`.

**Compte** : tout `.ipynb` non exclu par `EXCLUDE_PEDAGOGICAL` du générateur, **et** qui porte une entrée curée (`issue_pr_associee`, `owner_logique`, etc.). Le catalogue est donc un sous-ensemble **curé** : un notebook présent sur le disque mais non encore curé n'apparaît pas.

**Exclut** (par design du générateur) : `research/`, `archive/`, `_output`, `output`, `partner-course`, `examples`. Les notebooks non-curés (drift) sont également absents jusqu'à curation manuelle ou passage du cron.

**Répond à** : « Combien de notebooks le dépôt présente-t-il publiquement ? » — c'est le chiffre citable dans un README, des release notes, ou la vitrine Pages.

### 2. Outil — `count_notebooks_by_series.py` mode pédagogique (863)

**Source** : [`scripts/notebook_tools/count_notebooks_by_series.py`](../../scripts/notebook_tools/count_notebooks_by_series.py).

**Compte** : tout `.ipynb` sous `MyIA.AI.Notebooks/` dont le **segment racine** (`parts[0]`) est l'une des 11 séries reconnues (`GenAI`, `Search`, `ML`, `SymbolicAI`, `QuantConnect`, `GameTheory`, `Sudoku`, `Probas`, `IIT`, `RL`, `EPF`), après application des exclusions. Les notebooks hors de ces 11 séries (ex. `CaseStudies/`) tombent dans la ligne `(other)` — **comptés dans le TOTAL mais pas rattachés à une série**.

**Exclut** deux ensembles distincts (cf code lignes 30-43) :

- `EXCLUDE_ALWAYS` (noms de **répertoires** uniquement, jamais le nom de fichier — leçon `#9851`) : `.ipynb_checkpoints`, `obj`, `bin`, `__pycache__`, `.git`.
- `EXCLUDE_PEDAGOGICAL` (sous-chaîne sur le **chemin relatif**) : `research`, `archive`, `_output`, `partner-course`, `examples`.

**Répond à** : « Combien de notebooks pédagogiques (hors recherche, archives, artefacts papermill, exemples partenaires) ? » — c'est le chiffre de cohérence interne entre séries.

### 3. Disque — `find` brut (974)

**Source** : `find MyIA.AI.Notebooks -name '*.ipynb' -not -path '*/.ipynb_checkpoints/*'` (équivalent Python : `pathlib.Path("MyIA.AI.Notebooks").rglob("*.ipynb")`).

**Compte** : **tout** fichier `.ipynb` physiquement présent sous `MyIA.AI.Notebooks/`, y compris la recherche, les archives, les artefacts, les exemples partenaires. **Aucun filtre** sémantique.

**Répond à** : « Combien de fichiers `.ipynb` existe-t-il sur le disque ? » — c'est la mesure la plus large, et celle qu'un clone frais obtient.

> **Note `git ls-files`** : `git ls-files 'MyIA.AI.Notebooks/**/*.ipynb'` donne **973** (un de moins que le disque = un fichier non-tracké résiduel). La mesure « disque » de cette doc utilise le `find` brut (974), conforme à l'acceptance de #9857.

---

## Réconciliation disque → outil (111 fichiers exclus, fichier-près)

La réconciliation se referme **exactement** : `974 (disque) − 111 (exclus) = 863 (outil)`.
Les 111 exclus se décomposent en deux ensembles, chacun reproductible par script.

### (a) `EXCLUDE_PEDAGOGICAL` — 110 fichiers

| Catégorie | Compte | Motif | Exemples typiques |
|-----------|-------:|-------|-------------------|
| `research/` | 101 | notebooks de recherche (ML-Training-Pipeline, quantbooks QC) | `QuantConnect/ML-Training-Pipeline/*_research.ipynb`, `QuantConnect/research/` |
| `archive/` | 6 | archives/legacy | `SymbolicAI/_archive/`, `SymbolicAI/Planners/_archive/`, `Search/_archive/` |
| `partner-course` | 0 | cours partenaires (aucun sur le disque à ce SHA) | — |
| `examples/` | 3 | démonstrations techniques sans valeur catalogue | `GenAI/Image/examples/*.ipynb` |
| `_output` | 0 | artefacts papermill (gitignored) | — |

> **Somme exacte, sans recouvrement** : `101 + 6 + 0 + 3 + 0 = 110`. Chaque
> fichier est attribué à son **premier** motif matché dans l'ordre du tableau
> (logique `count_notebooks_by_series.py` lignes 69-73). À ce SHA, aucun
> fichier ne matche plusieurs motifs à la fois.

### (b) Hors 11 séries — 7 fichiers, deux destins distincts

Les 7 fichiers dont le segment racine n'est pas dans `SERIES_ORDER` ne sont
**pas** traités uniformément par l'outil : tout dépend de savoir si l'entrée
racine est un **répertoire** (parcouru) ou un **fichier** (ignoré).

| Entrée racine | Compte | Compté par l'outil ? | Raison |
|---------------|-------:|----------------------|--------|
| `CaseStudies/` (répertoire) | 6 | **Oui** — ligne `(other)` du TOTAL | Répertoire, donc parcouru ; racine `CaseStudies` hors `SERIES_ORDER` → bucket `(other)` |
| `GradeBook.ipynb` (fichier racine) | 1 | **Non** | Fichier à la racine de `MyIA.AI.Notebooks/` ; l'outil n'itère que les **répertoires** (`if not series_dir.is_dir(): continue`, ligne 162 du script) |

**Conséquence sur les totaux** :

- L'outil compte `857 (11 séries) + 6 (CaseStudies → other) = 863`.
- `GradeBook.ipynb` est le **111ᵉ fichier** du gap disque→outil : `974 − 863 = 111 = 110 (EXCLUDE_PEDAGOGICAL) + 1 (fichier racine non parcouru)`.
- Le catalogue compte lui aussi **863 entrées** : les 6 `CaseStudies` sont
  curés (la 1ʳᵉ entrée du catalogue est `CaseStudies/Diagnostic-Medical/...`),
  `GradeBook.ipynb` en est absent, et les 110 pédagogiquement exclus le sont
  aussi. D'où la convergence catalogue = outil = 863.

### (c) `EXCLUDE_ALWAYS` — 0 fichier

Sur le worktree frais (`e7307a717`), aucun notebook ne vit sous
`.ipynb_checkpoints/`, `obj/`, `bin/`, `__pycache__/` ou `.git/` de manière
trackée. Cette catégorie est **structurellement vide** sur `main` ; elle
n'existe dans le code que comme garde-fou contre les artefacts locaux.

---

## Vérification reproductible

```bash
# Disque (974)
find MyIA.AI.Notebooks -name '*.ipynb' -not -path '*/.ipynb_checkpoints/*' | wc -l

# Outil pédagogique (863)
python scripts/notebook_tools/count_notebooks_by_series.py | tail -3   # → TOTAL 863

# Catalogue (863)
python -c "import json; print(len(json.load(open('COURSE_CATALOG.generated.json'))))"

# Réconciliation détaillée : --all inclut research/archive/examples (toujours 110),
# mais GradeBook.ipynb (fichier racine) reste non parcouru → 973 = 974 - 1
python scripts/notebook_tools/count_notebooks_by_series.py --all | tail -3   # → 973

# Assertion outillée (acceptance #9857) : rougit si catalogue et outil divergent
python scripts/notebook_tools/count_notebooks_by_series.py --check           # → OK (863 == 863)
```

---

## Assertion outillée — `--check` (acceptance #9857)

Le mode `--check` de [`count_notebooks_by_series.py`](../../scripts/notebook_tools/count_notebooks_by_series.py)
compare le compte **outil** (pédagogique) au compte **catalogue** (curé) et
**sort en code 1** (`sys.exit(1)`) s'ils divergent :

```
CHECK -- convergence catalogue / outil
  Outil (pedagogical) : 863
  Catalogue (curated) : 863
  Statut              : OK -- convergent (863 == 863)
```

**Pourquoi cette assertion** : les deux sources appliquent le même ensemble
`EXCLUDE_PEDAGOGICAL`, donc toute divergence est un signal actionnable — pas
un bruit attendu. Deux causes légitimes (diagnostiquées dans le message de
sortie) :

- **`outil > catalogue`** : drift de curation (notebook fraîchement ajouté,
  non encore curé) → résolu par `catalog-cron.yml` en `< 24h`.
- **`catalogue > outil`** : notebook curé mais exclu par chemin outil (ex. un
  `examples/` promu manuellement au catalogue).

L'investigation chemin-par-chemin (drift / phantom au niveau fichier) se fait
avec le script sœur [`scripts/audit/check_denominators.py --strict`](../../scripts/audit/check_denominators.py)
(issue `#8050`), qui compare disque / forensic / catalogue et liste les paths
en défaut. `--check` est le **seuil minimal** (alerte sur l'écart de total) ;
`check_denominators.py` est le **diagnostic** (localise les fichiers).

---

## Source canonique pour les affirmations publiques

**Le marqueur `CATALOG-STATUS` par série** (maintenu quotidiennement par
`catalog-cron.yml` dans chaque `README.md` de série) est la source canonique
pour tout chiffre cité en prose (README racine, release notes, vitrine Pages).

**Règle** ([`catalog-pr-hygiene`](../../.claude/rules/catalog-pr-hygiene.md)) :
aucun nombre de notebooks n'est **codé en dur** dans la prose d'une PR. On
cite le marqueur `CATALOG-STATUS` (qui dérive du catalogue 863), jamais un
compte mesuré à la main — le compte dérive avec chaque merge, le marqueur est
régénéré.

---

## Pourquoi catalogue et outil convergent (et quand ils divergeraient)

Depuis `#9851` (correctif `bin`/`CombinatorialGames`), catalogue et outil
donnent le même total **863**. Cette convergence est **accidentelle sur le
total** mais **structurelle sur la définition** : les deux appliquent le même
ensemble `EXCLUDE_PEDAGOGICAL` (`research`/`archive`/`_output`/`partner-course`/
`examples`).

**Ils divergeraient légitimement si** :

- le catalogue **cure** manuellement un notebook que l'outil exclut par chemin
  (ex. un notebook `examples/` promu au catalogue) → catalogue > outil ;
- le catalogue **n'a pas encore curé** un notebook fraîchement ajouté que
  l'outil compte déjà → outil > catalogue (drift de curation, résolu par le
  cron quotidien).

Un check d'écart catalogue/outil hors des catégories documentées est prévu
par le détecteur [`scripts/audit/check_denominators.py`](../../scripts/audit/check_denominators.py)
(cf doc sœur [`notebook-counts-reconciliation.md`](notebook-counts-reconciliation.md),
périmètre 2026-07-23, chiffres alors périmés — la présente doc la supersede
pour les chiffres courants).

---

## Voir aussi

- [`notebook-counts-reconciliation.md`](notebook-counts-reconciliation.md) — doc sœur (2026-07-23, `#8050`) : 4 dénominateurs (forensic/catalogue/disque/snapshot) au SHA `be59980`. **Chiffres périmés** (946/944/830) ; la présente doc la supersede pour l'état courant et les 3 sources de `#9857`.
- [`catalog-pr-hygiene.md`](../../.claude/rules/catalog-pr-hygiene.md) — le marqueur `CATALOG-STATUS` appartient au cron, jamais édité sur une branche.
- `#9851` — correctif du filtre `bin` substring (directory-segments only), qui a porté l'outil de 866 à 863 et aligné sur le catalogue.
