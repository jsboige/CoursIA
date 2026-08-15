# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-08-15**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**903** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 748 | 82.8% |
| DEMO | 153 | 16.9% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 567 |
| WSL requis | 46 |
| GPU requis | 102 |
| Cloud requis (QC / GenAI Docker) | 110 |
| API key requise | 145 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| FallacyDetection | 2 | 0 | 0 | 2 | 100% |
| GameTheory | 56 | 0 | 0 | 56 | 100% |
| GenAI | 77 | 90 | 2 | 169 | 46% |
| IIT | 53 | 0 | 0 | 53 | 100% |
| ML | 45 | 3 | 0 | 48 | 94% |
| Probas | 58 | 0 | 0 | 58 | 100% |
| QuantConnect | 60 | 48 | 0 | 108 | 56% |
| RL | 16 | 1 | 0 | 17 | 94% |
| Search | 118 | 0 | 0 | 118 | 100% |
| Sudoku | 35 | 2 | 0 | 37 | 95% |
| SymbolicAI | 221 | 9 | 0 | 230 | 96% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 582 |
| .NET (C#) | 234 |
| Python 3 (ipykernel) | 23 |
| Lean 4 (WSL) | 18 |
| Python (GameTheory WSL + OpenSpiel) | 10 |
| Python 3 (WSL) | 7 |
| coursia-ml-training | 4 |
| Python 3 (coursia-ml-training) | 4 |
| Python (coursia-ml-training) | 4 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| .venv | 2 |
| Coursia ML Training | 1 |
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
