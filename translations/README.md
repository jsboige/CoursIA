# CSV de synchro traduction — source de vérité multilingue

**Statut** : T1 baseline multi-familles (Epic #4957 / #1650). Arborescence des CSV source de vérité pour la synchronisation traduction des notebooks pédagogiques. Chaque CSV capture l'extraction (`src_lang=fr`, colonne pivot `text_fr`) d'une série ; les colonnes cibles (`text_en`…`text_pt`) restent vides tant que le moteur Argumentum (T3, gated #1650 Phase 1) n'est pas branché.

## Structure

```text
translations/
├── README.md                 ← ce fichier
├── casestudies/              ├─ gametheory/        ├─ genai/ (texte, finetuning, posttraining)
├── genai-audio/              ├─ genai-image/       ├─ iit/
├── ml-datascience/           ├─ mlnet/             ├─ planners/
├── probas-decinfer/          ├─ probas-infer/      ├─ probas-pymc/
├── quantconnect/             ├─ rl/                ├─ search-applications/
├── search-part1/             ├─ search-part2/      ├─ search-part3/
├── search-part4/             ├─ semanticweb/       ├─ smartcontracts/
├── smt/ (z3-api, z3-linq2z3) ├─ sudoku/            ├─ symbolicai/
├── symboliclearning/         └─ tweety/
```

Sous-répertoire par famille (`translations/<famille>/`), un CSV par série pédagogique. `smt/` porte deux séries (`z3-api`, `z3-linq2z3`) et `genai/` en porte trois (`texte`, `finetuning`, `posttraining`).

Convention : `translations/<famille>/<série>.csv`, une ligne par cellule de notebook. Cf. `scripts/translation/README.md` pour le schéma détaillé.

## Familles couvertes (T1 baseline)

**29 CSV, 22 265 cellules** au total (extraction `src_lang=fr`, comptage lignes hors en-tête). Regroupement par domaine pédagogique :

| Domaine | CSV | Cellules | Série source |
|---------|-----|---------:|--------------|
| SymbolicAI — Tweety | `tweety/tweety.csv` | 864 | `SymbolicAI/Tweety/` |
| SymbolicAI — SemanticWeb | `semanticweb/semanticweb.csv` | 1193 | `SymbolicAI/SemanticWeb/` |
| SymbolicAI — Planning | `planners/planners.csv` | 1006 | `SymbolicAI/Planners/` |
| SymbolicAI — SMT/Z3-API | `smt/z3-api.csv` | 541 | `SymbolicAI/SMT/` |
| SymbolicAI — SMT/Z3.Linq | `smt/z3-linq2z3.csv` | 525 | `SymbolicAI/SMT/` |
| SymbolicAI — Argument | `symbolicai/argument_analysis.csv` | 421 | `SymbolicAI/Argument_Analysis/` |
| SymbolicLearning | `symboliclearning/symboliclearning.csv` | 738 | `SymbolicAI/SymbolicLearning/` |
| SmartContracts | `smartcontracts/smartcontracts.csv` | 965 | `SymbolicAI/SmartContracts/` |
| CaseStudies | `casestudies/casestudies.csv` | 149 | `CaseStudies/` |
| Search — Part 1 | `search-part1/search-part1.csv` | 1168 | `Search/Part1-Foundations/` |
| Search — Part 2 | `search-part2/search-part2.csv` | 784 | `Search/Part2-CSP/` |
| Search — Part 3 | `search-part3/search-part3.csv` | 131 | `Search/Part3-Advanced/` |
| Search — Part 4 | `search-part4/search-part4.csv` | 453 | `Search/Part4-Metaheuristics/` |
| Search — Applications | `search-applications/search-applications.csv` | 1468 | `Search/Applications/` |
| Probas — Infer.NET | `probas-infer/probas_infer.csv` | 940 | `Probas/` |
| Probas — PyMC | `probas-pymc/probas_pymc.csv` | 571 | `Probas/` |
| Probas — Decision (Infer.NET) | `probas-decinfer/probas_decinfer.csv` | 383 | `Probas/DecisionTheory/DecInfer/` |
| IIT / ICT | `iit/iit.csv` | 776 | `IIT/ICT-Series/` |
| ML.NET | `mlnet/mlnet.csv` | 599 | `ML/` |
| ML — Data Science with Agents | `ml-datascience/ml-datascience.csv` | 708 | `ML/DataScienceWithAgents/` |
| RL | `rl/rl.csv` | 513 | `RL/` |
| Sudoku | `sudoku/sudoku.csv` | 1325 | `Sudoku/` |
| GameTheory | `gametheory/gametheory.csv` | 1897 | `GameTheory/` |
| GenAI — Texte | `genai/texte.csv` | 718 | `GenAI/Texte/` |
| GenAI — FineTuning | `genai/finetuning.csv` | 161 | `GenAI/Texte/` |
| GenAI — PostTraining | `genai/posttraining.csv` | 171 | `GenAI/Texte/` |
| GenAI — Image | `genai-image/genai-image.csv` | 533 | `GenAI/Image/` |
| GenAI — Audio | `genai-audio/genai-audio.csv` | 1128 | `GenAI/Audio/` |
| QuantConnect — Python | `quantconnect/quantconnect-py.csv` | 1436 | `QuantConnect/` (QC-Py-01..41) |

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

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md`
