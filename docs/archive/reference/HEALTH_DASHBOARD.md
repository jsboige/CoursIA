# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-08-11**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**886** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 731 | 82.5% |
| DEMO | 153 | 17.3% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 556 |
| WSL requis | 43 |
| GPU requis | 102 |
| Cloud requis (QC / GenAI Docker) | 107 |
| API key requise | 143 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 56 | 0 | 0 | 56 | 100% |
| GenAI | 67 | 90 | 2 | 159 | 42% |
| IIT | 53 | 0 | 0 | 53 | 100% |
| ML | 45 | 3 | 0 | 48 | 94% |
| Probas | 58 | 0 | 0 | 58 | 100% |
| QuantConnect | 58 | 48 | 0 | 106 | 55% |
| RL | 16 | 1 | 0 | 17 | 94% |
| Search | 118 | 0 | 0 | 118 | 100% |
| Sudoku | 35 | 2 | 0 | 37 | 95% |
| SymbolicAI | 218 | 9 | 0 | 227 | 96% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 576 |
| .NET (C#) | 230 |
| Python 3 (ipykernel) | 22 |
| Lean 4 (WSL) | 18 |
| Python (GameTheory WSL + OpenSpiel) | 10 |
| Python 3 (WSL) | 7 |
| Python 3 (coursia-ml-training) | 4 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| Python (coursia-ml-training) | 2 |
| .venv | 2 |
| coursia-ml-training | 1 |
| unknown | 1 |
| pyphi | 1 |
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
