# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-07-21**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**830** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 664 | 80.0% |
| DEMO | 164 | 19.8% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 518 |
| WSL requis | 42 |
| GPU requis | 93 |
| Cloud requis (QC / GenAI Docker) | 105 |
| API key requise | 135 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 50 | 0 | 0 | 50 | 100% |
| GenAI | 57 | 82 | 2 | 141 | 40% |
| IIT | 37 | 0 | 0 | 37 | 100% |
| ML | 44 | 3 | 0 | 47 | 94% |
| Probas | 58 | 0 | 0 | 58 | 100% |
| QuantConnect | 38 | 67 | 0 | 105 | 36% |
| RL | 16 | 1 | 0 | 17 | 94% |
| Search | 113 | 0 | 0 | 113 | 100% |
| Sudoku | 34 | 2 | 0 | 36 | 94% |
| SymbolicAI | 211 | 9 | 0 | 220 | 96% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 535 |
| .NET (C#) | 225 |
| Python 3 (ipykernel) | 20 |
| Lean 4 (WSL) | 17 |
| Python (GameTheory WSL + OpenSpiel) | 8 |
| Python 3 (WSL) | 7 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| Python 3 (coursia-ml-training) | 2 |
| .venv | 2 |
| pyphi | 1 |
| Python (coursia-ml-training) | 1 |
| .venv (3.14.3) | 1 |
| .venv (3.12.3) | 1 |
| cours-ia | 1 |
| Python 3 (SC-16 Concrete, WSL) | 1 |
| Python (difflogic-sl12) | 1 |

## BROKEN (2 — à traiter en priorité)

| Série | Notebook | Maturité | Dernière validation |
|-------|----------|----------|---------------------|
| GenAI | Notebook de travail | TEMPLATE | 2026-06-26 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-18 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
