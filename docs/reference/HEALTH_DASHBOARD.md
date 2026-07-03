# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-07-03**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**670** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 518 | 77.3% |
| DEMO | 147 | 21.9% |
| BROKEN | 5 | 0.7% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 369 |
| WSL requis | 42 |
| GPU requis | 83 |
| Cloud requis (QC / GenAI Docker) | 105 |
| API key requise | 133 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 28 | 0 | 0 | 28 | 100% |
| GenAI | 59 | 80 | 2 | 141 | 42% |
| IIT | 18 | 0 | 0 | 18 | 100% |
| ML | 33 | 3 | 1 | 37 | 89% |
| Probas | 53 | 0 | 0 | 53 | 100% |
| QuantConnect | 48 | 57 | 0 | 105 | 46% |
| RL | 16 | 0 | 0 | 16 | 100% |
| Search | 71 | 0 | 0 | 71 | 100% |
| Sudoku | 30 | 1 | 2 | 33 | 91% |
| SymbolicAI | 156 | 6 | 0 | 162 | 96% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 486 |
| .NET (C#) | 117 |
| Python 3 (ipykernel) | 18 |
| Lean 4 (WSL) | 17 |
| Python (GameTheory WSL + OpenSpiel) | 9 |
| Python 3 (WSL) | 7 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| Python 3 (coursia-ml-training) | 2 |
| .venv | 2 |
| pyphi | 1 |
| .venv (3.14.3) | 1 |
| .venv (3.12.3) | 1 |
| Python (CoursIA SemanticWeb) | 1 |
| cours-ia | 1 |

## BROKEN (5 — à traiter en priorité)

| Série | Notebook | Maturité | Dernière validation |
|-------|----------|----------|---------------------|
| GenAI | Notebook de travail | TEMPLATE | 2026-06-26 |
| GenAI | Notebook de travail | TEMPLATE | 2026-06-26 |
| ML | ML-5 : Time Series Forecasting avec ML.NET | DRAFT | 2026-06-24 |
| Sudoku | Sudoku-10 : Resolution avec OR-Tools (C#) | PRODUCTION | 2026-07-02 |
| Sudoku | Sudoku-6 : Resolution par CSP Academique (AIMA) | PRODUCTION | 2026-07-02 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
