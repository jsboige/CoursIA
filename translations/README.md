# CSV de synchro traduction — source de vérité multilingue

**Statut** : T1 baseline multi-familles (Epic #4957 / #1650). Arborescence des CSV source de vérité pour la synchronisation traduction des notebooks pédagogiques. Chaque CSV capture l'extraction (`src_lang=fr`, colonne pivot `text_fr`) d'une série ; les colonnes cibles (`text_en`…`text_pt`) restent vides tant que le moteur Argumentum (T3, gated #1650 Phase 1) n'est pas branché.

## Structure

```text
translations/
├── README.md                 ← ce fichier
├── casestudies/              ├─ gametheory/        ├─ genai/ (7 séries : audio, casestudies, finetuning, image, posttraining, texte, video)
├── iit/                      ├─ ml-datascience/    ├─ mlnet/
├── partner-course-quant-...  ├─ planners/          ├─ probas-decinfer/
├── probas-infer/             ├─ probas-pymc/       ├─ quantconnect/
├── rl/                       ├─ search-applications/ ├─ search-part1/
├── search-part2/             ├─ search-part3/      ├─ search-part4/
├── semanticweb/              ├─ smartcontracts/    ├─ smt/ (z3-api, z3-linq2z3)
├── sudoku/                   ├─ symbolicai/        ├─ symbolicai-lean/
├── symboliclearning/         └─ tweety/
```

Sous-répertoire par famille (`translations/<famille>/`), un CSV par série pédagogique. `smt/` porte deux séries (`z3-api`, `z3-linq2z3`) et `genai/` en porte **sept** (`audio`, `casestudies`, `finetuning`, `image`, `posttraining`, `texte`, `video` — consolidation 2026-07-17, cf `genai/README.md`).

Convention : `translations/<famille>/<série>.csv`, une ligne par cellule de notebook. Cf. `scripts/translation/README.md` pour le schéma détaillé.

## Familles couvertes (T1 baseline)

**33 CSV, 24 470 cellules** au total (extraction `src_lang=fr`, comptage enregistrements `csv.reader` hors en-tête, audit Python `csv.DictReader` c.1252 2026-08-06). Regroupement par domaine pédagogique :

| Domaine | CSV | Cellules | Série source |
|---------|-----|---------:|--------------|
| SymbolicAI — Tweety | `tweety/tweety.csv` | 864 | `SymbolicAI/Tweety/` |
| SymbolicAI — SemanticWeb | `semanticweb/semanticweb.csv` | 1193 | `SymbolicAI/SemanticWeb/` |
| SymbolicAI — Planning | `planners/planners.csv` | 1006 | `SymbolicAI/Planners/` |
| SymbolicAI — SMT/Z3-API | `smt/z3-api.csv` | 541 | `SymbolicAI/SMT/Z3-API/` |
| SymbolicAI — SMT/Z3.Linq | `smt/z3-linq2z3.csv` | 525 | `SymbolicAI/SMT/Z3-Linq2Z3/` |
| SymbolicAI — Argument | `symbolicai/argument_analysis.csv` | 421 | `SymbolicAI/Argument_Analysis/` |
| SymbolicAI — Lean | `symbolicai-lean/symbolicai-lean.csv` | 1178 | `SymbolicAI/Lean/` |
| SymbolicLearning | `symboliclearning/symboliclearning.csv` | 738 | `SymbolicAI/SymbolicLearning/` |
| SmartContracts | `smartcontracts/smartcontracts.csv` | 965 | `SymbolicAI/SmartContracts/` |
| CaseStudies | `casestudies/casestudies.csv` | 149 | `CaseStudies/` |
| Search — Part 1 | `search-part1/search-part1.csv` | 1170 | `Search/Part1-Foundations/` |
| Search — Part 2 | `search-part2/search-part2.csv` | 784 | `Search/Part2-CSP/` |
| Search — Part 3 | `search-part3/search-part3.csv` | 131 | `Search/Part3-Advanced/` |
| Search — Part 4 | `search-part4/search-part4.csv` | 453 | `Search/Part4-Metaheuristics/` |
| Search — Applications | `search-applications/search-applications.csv` | 1468 | `Search/Applications/` |
| Probas — Infer.NET | `probas-infer/probas_infer.csv` | 940 | `Probas/Infer/` |
| Probas — PyMC | `probas-pymc/probas_pymc.csv` | 571 | `Probas/PyMC/` |
| Probas — Decision (Infer.NET) | `probas-decinfer/probas_decinfer.csv` | 383 | `Probas/DecisionTheory/DecInfer/` |
| IIT / ICT | `iit/iit.csv` | 776 | `IIT/ICT-Series/` |
| ML.NET | `mlnet/mlnet.csv` | 599 | `ML/ML.Net/` |
| ML — Data Science with Agents | `ml-datascience/ml-datascience.csv` | 708 | `ML/DataScienceWithAgents/` |
| RL | `rl/rl.csv` | 513 | `RL/` |
| Sudoku | `sudoku/sudoku.csv` | 1337 | `Sudoku/` |
| GameTheory | `gametheory/gametheory.csv` | 1897 | `GameTheory/` |
| GenAI — Audio | `genai/audio.csv` | 1128 | `GenAI/Audio/` |
| GenAI — CaseStudies | `genai/casestudies.csv` | 113 | `GenAI/CaseStudies/` |
| GenAI — FineTuning | `genai/finetuning.csv` | 161 | `GenAI/FineTuning/` |
| GenAI — Image | `genai/image.csv` | 533 | `GenAI/Image/` |
| GenAI — PostTraining | `genai/posttraining.csv` | 171 | `GenAI/PostTraining/` |
| GenAI — Texte | `genai/texte.csv` | 718 | `GenAI/Texte/` |
| GenAI — Video | `genai/video.csv` | 486 | `GenAI/Video/` |
| QuantConnect — Python | `quantconnect/quantconnect-py.csv` | 1436 | `QuantConnect/Python/` |
| QuantConnect — Partner Course | `partner-course-quant-trading/partner-course.csv` | 198 | `QuantConnect/partner-course-quant-trading/` |

> Note : les séries **QuantConnect C# / QuantBooks** et **partner-course** ne sont pas couvertes par l'extraction T1 (exécution gated QC Cloud). Les sous-séries QC-Py-Cloud-* et partner-course sont en follow-up.

## Workflow (T1 → T2 → T3)

| T# | Script | Statut |
|----|--------|--------|
| **T1** | `scripts/translation/extract_cells_to_csv.py` | **Livré** (Phase 1 INFRA, PR #5657) — 29 séries extraites |
| **T2** | `scripts/translation/check_translation_sync.py` | **Livré**, CI non-bloquante `.github/workflows/translation-drift.yml` |
| **T3** | Moteur Argumentum `datasetupdater` (8 langues) | À venir (gated #1650 Phase 1 connecteur) |

Pour resynchroniser un CSV après modification du notebook source (T1, non-destructif tant que les colonnes cibles sont vides) :

```bash
python scripts/translation/extract_cells_to_csv.py --src-lang fr --repo-root . \
  -o translations/<famille>/<série>.csv <notebooks...>
python scripts/translation/check_translation_sync.py   # 0 anomalie attendue
```

## Doctrine c.31 — pas de PR *resync-only* tant que le moteur T3 est gated

Érigée par po-2023 (c.31, 2026-07-22) sur [#6949](https://github.com/jsboige/CoursIA/issues/6949), entérinée par décision coordinateur (myia-ai-01, même thread) :

> Tant que `scripts/translation/translate_csv.py` reste `ENABLED = False` (ligne 53), une PR de type *resync CSV* qui zerote un compteur `SRC_DRIFT` sans livrer de cellule traduite est **indiscernable d'un travail fait** — c'est une falsification du signal de dérive (cf. incidents fondateurs #8678 et #8680). Elle **doit rester visible** : `N cellules modifiées depuis la dernière traduction` est un signal vrai et utile au moment du GO.

**Règle, effective immédiatement (c.31 → c.1252)** : plus de PR *resync-only* sur `translations/**/*.csv` jusqu'au GO moteur T3. `check_translation_sync.py` continue de **détecter** la dérive ; on cesse de la **zeroter**. Un resync reste légitime **couplé** à une livraison qui le consomme (extraction d'un notebook neuf, ou première traduction réelle).

**Application post-clôture textuelle #6949** : PR [#8431](https://github.com/jsboige/CoursIA/pull/8431) (2026-07-25) a zeroté 100 SRC_DRIFT sur Planners **après** la clôture textuelle (#7967, 2026-07-22). **Violation documentée** : le compteur `100 → 0` a été publié sans livraison de traduction. Cet incident **renforce** la doctrine (ne la renverse pas) et reste **ouvert** comme exemple pour les futurs agents qui évalueraient un resync.

Voir le diagnostic de référence : [docs/translation/translations-root-diagnostic.md](../docs/translation/translations-root-diagnostic.md) (c.1252, 2026-08-06).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- Issue #6949 — T3 moteur fork Argumentum (OUVERTE par décision coord)
- `scripts/translation/README.md`
- `docs/translation/translations-root-diagnostic.md` — diagnostic de l'état + options de disposition
