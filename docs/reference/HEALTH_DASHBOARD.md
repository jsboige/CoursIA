# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-08-07**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**863** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 716 | 83.0% |
| DEMO | 145 | 16.8% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 549 |
| WSL requis | 43 |
| GPU requis | 93 |
| Cloud requis (QC / GenAI Docker) | 106 |
| API key requise | 135 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 55 | 0 | 0 | 55 | 100% |
| GenAI | 57 | 82 | 2 | 141 | 40% |
| IIT | 53 | 0 | 0 | 53 | 100% |
| ML | 45 | 3 | 0 | 48 | 94% |
| Probas | 58 | 0 | 0 | 58 | 100% |
| QuantConnect | 58 | 48 | 0 | 106 | 55% |
| RL | 16 | 1 | 0 | 17 | 94% |
| Search | 116 | 0 | 0 | 116 | 100% |
| Sudoku | 35 | 2 | 0 | 37 | 95% |
| SymbolicAI | 217 | 9 | 0 | 226 | 96% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 560 |
| .NET (C#) | 229 |
| Python 3 (ipykernel) | 20 |
| Lean 4 (WSL) | 18 |
| Python (GameTheory WSL + OpenSpiel) | 10 |
| Python 3 (WSL) | 7 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| Python 3 (coursia-ml-training) | 2 |
| .venv | 2 |
| unknown | 1 |
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
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
