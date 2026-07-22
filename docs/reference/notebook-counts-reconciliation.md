# Réconciliation des dénominateurs notebooks — forensic / catalogue / disque

**Date** : 2026-07-23
**SHA** : `be59980739c60e6e484b8ff7ef78a03df7bb70e7` (main HEAD)
**Lane** : po-2023 (c.761)
**Issue** : [#8050](https://github.com/jsboige/CoursIA/issues/8050) (Closes)
**Epic parent** : #4208 (open-courseware fiabilisé)

---

## TL;DR — les 4 sources au même SHA

| Source | Compte | Périmètre | Script |
|--------|--------|-----------|--------|
| **Disque** | **946** | tous les `*.ipynb` sous `MyIA.AI.Notebooks/` (récursif) | `find -name '*.ipynb'` |
| **Forensic scan** | **944** | disque moins `_archives/` (2 notebooks exclus) | `scripts/notebook_tools/forensic_scan.py --root MyIA.AI.Notebooks` |
| **Catalogue** | **830** | forensic moins `research/`, `partner-course-quant-trading/`, `examples/`, et **non-curés** (drift) | `scripts/notebook_tools/generate_catalog.py` |
| **STABLE_SNAPSHOT** | **934** | snapshot daté **2026-07-17** (SHA `d8ea11a`), stale de 6 jours | `STABLE_SNAPSHOT.md` |

**Écart catalogue / disque = 116 = (114 curés non-inclus bruts) = (84 drift curé réel) + (30 exclusions catalogue par design)**.

> **Important.** Le diff brut catalogue-forensic est **114** (cf tableau par série), mais **84 seulement sont du drift** (notebooks curés manquants) ; les **30 autres sont des exclusions catalogue par design** (recherche/partner-course/archive/examples — présents sur disque et dans forensic, exclus du catalogue). Le détecteur `scripts/audit/check_denominators.py` filtre ces 30 et remonte les 84 réels.

---

## Règles d'exclusion par outil (G.1, source de vérité = code)

### 1. Disque (`find -name '*.ipynb'`)
**Aucun filtre.** Tout `.ipynb` sous `MyIA.AI.Notebooks/` est compté (incluant `_archives/`, `.ipynb_checkpoints/`, etc.).

### 2. Forensic scan (`scripts/notebook_tools/forensic_scan.py`)
**Filtre ligne 25-32** :
```python
EXCLUDE_DIRS = {
    "_archive_obsoletes",
    "_archives",
    "_old",
    "TrashBin",
    "trashbin",
    ".ipynb_checkpoints",
    "node_modules",
}
ARTIFACT_SUFFIXES = ("_output.ipynb",)
```

**Effet** : 946 disque → 944 forensic (2 notebooks `_archives/` exclus : `SymbolicLearning/_archives/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Compose.ipynb`, `EML-NAND-Explore.ipynb`).

### 3. Catalogue (`scripts/notebook_tools/generate_catalog.py`)
**Filtre ligne 39** :
```python
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "output", "partner-course", "examples"}
RESEARCH_DIR_KEYWORDS = {"research", "archive", "examples", "partner-course"}
```

**Effet** : 944 forensic → 830 catalogue curé. **Exclusions cumulées** :
- `research/` (17 QC + 1 Search) = 18
- `partner-course-quant-trading/` (7 QC) = 7
- `examples/` (3 GenAI/Image) = 3
- `archive/` (1 SymbolicAI/Tweety, 1 SymbolicAI/Planners, 1 Search) = 3
- `_output` / `output` (counted via ARTIFACT_SUFFIXES, gitignored) = non compté sur disque déjà

**Effet exclusions catalogue = 31 notebooks (de forensic 944 → catalogue 913 attendus)**. **Mais catalogue = 830, écart 83 = notebooks curés manquants** (drift catalogue).

### 4. STABLE_SNAPSHOT (`STABLE_SNAPSHOT.md`)
**Snapshot daté 2026-07-17, SHA `d8ea11a`** — stale de 6 jours et 10 commits de retard. Ne reflète pas l'état main actuel.

---

## Écart catalogue vs disque par série (G.1, snapshot 2026-07-23)

| Série | Disque | Forensic | Catalogue | Écart (C−F) | Cause |
|-------|-------:|---------:|----------:|-----------:|-------|
| CaseStudies | 6 | 6 | 6 | 0 | — |
| GameTheory | 55 | 55 | 50 | **−5** | `GameTheory-8` + `8b` + `8c` non-curés (nouveaux 2026-07-23) |
| GenAI | 144 | 144 | 141 | **−3** | `Image/examples/{history-geography,literature-visual,science-diagrams}.ipynb` (EXCLUDE_PEDAGOGICAL) |
| GradeBook.ipynb (TOP) | 1 | 1 | 0 | −1 | TOP non-curé par design |
| IIT | 37 | 37 | 37 | 0 | — |
| ML | 47 | 47 | 47 | 0 | — |
| Probas | 58 | 58 | 58 | 0 | — |
| QuantConnect | 204 | 204 | 105 | **−99** | `research/` (17) + `partner-course` (7) = 24 EXCLUDE ; **ML-TP (12) + projects (61) = 73 non-curés (drift)** |
| RL | 17 | 17 | 17 | 0 | — |
| Search | 117 | 117 | 113 | **−4** | `archive/` (2 EXCLUDE) + `Part4-Metaheuristics/MGS-7c/7d` (2 non-curés) |
| Sudoku | 36 | 36 | 36 | 0 | — |
| SymbolicAI | 222 | 222 | 220 | **−2** | `archive/Tweety.ipynb` + `Planners/archive/Fast-Downward-Legacy.ipynb` (EXCLUDE_PEDAGOGICAL) |
| **TOTAL** | **946** | **944** | **830** | **−114** | 31 EXCLUDE_PEDAGOGICAL + 83 drift catalogue |

---

## Écart GenAI 144-vs-141 ligne par ligne (G.1 résolu)

Les 3 notebooks GenAI/Image/examples présents sur disque mais absents du catalogue sont **explicitement exclus** par la règle catalogue `EXCLUDE_PEDAGOGICAL = {..., "examples", ...}` (cf `scripts/notebook_tools/generate_catalog.py` ligne 39).

| Path | Status forensic | Status catalogue | Règle |
|------|----------------|------------------|-------|
| `GenAI/Image/examples/history-geography.ipynb` | A_ALL_EXEC_OK (12 code, 12 exec) | absent (path contains `examples`) | EXCLUDE_PEDAGOGICAL |
| `GenAI/Image/examples/literature-visual.ipynb` | A_ALL_EXEC_OK (12 code, 12 exec) | absent (path contains `examples`) | EXCLUDE_PEDAGOGICAL |
| `GenAI/Image/examples/science-diagrams.ipynb` | A_ALL_EXEC_OK (16 code, 16 exec) | absent (path contains `examples`) | EXCLUDE_PEDAGOGICAL |

**Pas un bug** : la règle est intentionnelle. Les `examples/` sont des **démonstrations techniques** (showcases ComfyUI/Qwen) sans valeur pédagogique au sens catalogue (`issue_pr_associee`, `owner_logique`, etc.). Ils restent visibles dans le forensic scan = signal qu'ils existent et sont sains.

**Recommandation** : ajouter une note explicite dans `STABLE_SNAPSHOT.md` disant « GenAI = 144 inclut 3 examples pédagogiques exclus du catalogue par design ». Ce qui supprime l'ambiguïté « 144-vs-141 » à la source.

---

## Drift catalogue détecté (83 notebooks curés manquants)

Les 83 notebooks curés-manquants ne sont **pas** des exclusions explicites ; ils témoignent que le catalogue curé est en retard sur l'état du repo.

### Drift QC (73) — majeure partie
- `QuantConnect/ML-Training-Pipeline/` : **12** notebooks non-curés (disque=14, cat=2)
- `QuantConnect/projects/` : **61** notebooks non-curés (disque=110, cat=49)

### Drift GameTheory (5)
- `GameTheory-8-CombinatorialGames-Csharp.ipynb`
- `GameTheory-8-CombinatorialGames.ipynb`
- `GameTheory-8b-Lean-CombinatorialGames.ipynb`
- `GameTheory-8c-CombinatorialGames-Csharp.ipynb`
- `GameTheory-8c-CombinatorialGames-Python.ipynb`

### Drift Search (2)
- `Search/Part4-Metaheuristics/MGS-7c-RosenbrockGriewank.ipynb`
- `Search/Part4-Metaheuristics/MGS-7d-MichalewiczDixonPrice.ipynb`

### Drift SymbolicAI (2 — faux positifs)
- `SymbolicLearning/_archives/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-{Compose,Explore}.ipynb`
- Ces 2 sont **dans `_archives/`**, donc exclus par forensic ET catalogue — faux positifs de mon diff (le diff n'inclut pas `_archives` dans la table ci-dessus, mais le `git ls-files` les remonte quand même).

### Drift TOP (1)
- `GradeBook.ipynb` non-curé par design.

---

## Causes racines du drift catalogue

1. **Catalogue régénéré sur cron quotidien** (`.github/workflows/catalog-cron.yml`) mais **sans curation manuelle** sur les dossiers fraîchement ajoutés.
2. **Le pipeline catalog-cron utilise `EXCLUDE_PEDAGOGICAL` côté génération** MAIS ne marque pas les notebooks « drift » vs « exclu-par-design » dans le JSON généré.
3. **Pas de check CI qui détecte le drift** entre forensic-count et catalog-count (avec exclusions déclarées).

---

## Acceptance #8050 — checklist

- [x] Doc qui mappe les 4 dénominateurs (forensic / catalogue / disque / exclus) au même SHA.
- [x] Règles d'exclusion de chaque outil explicitées (`EXCLUDE_DIRS` forensic ligne 25-32, `EXCLUDE_PEDAGOGICAL` catalogue ligne 39).
- [x] Écart GenAI 144-vs-141 expliqué ligne par ligne (3 `examples/` exclus par design).
- [x] CI léger `scripts/audit/check_denominators.py` qui alerte si divergence > exclusions déclarées.
- [ ] Note explicite dans `STABLE_SNAPSHOT.md` que GenAI inclut 3 examples pédagogiques exclus du catalogue (recommandation, hors scope).

---

## Scripts de vérification (rejouables)

```bash
# Disque (946)
py -c "import pathlib; print(len(list(pathlib.Path('MyIA.AI.Notebooks').rglob('*.ipynb'))))"

# Forensic (944)
py scripts/notebook_tools/forensic_scan.py --root MyIA.AI.Notebooks --json-out /tmp/forensic.json
py -c "import json; print(len(json.load(open('/tmp/forensic.json'))['results']))"

# Catalogue (830)
py -c "import json; print(len(json.load(open('COURSE_CATALOG.generated.json'))))"

# Drift check (CI)
py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks
```

---

## Suite logique

- **Régénération catalogue** : le cron quotidien devrait auto-curer les 83 drift → à confirmer avec ai-01 si le cron gère ou non les ajouts récents.
- **Split QC `projects/` curé-manuellement** : 61 notebooks non-curés = demande substantielle (notebook par notebook). Priorité basse car `projects/` = notebooks de recherche jetables.
- **Note STABLE_SNAPSHOT.md** : ajouter la note GenAI examples dans la prochaine PR de mise à jour snapshot (recommandation #8050, hors scope de cette PR).
