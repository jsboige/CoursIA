# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-08-29**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1064** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 898 | 84.4% |
| DEMO | 164 | 15.4% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 669 |
| WSL requis | 71 |
| GPU requis | 117 |
| Cloud requis (QC / GenAI Docker) | 113 |
| API key requise | 169 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| FallacyDetection | 2 | 0 | 0 | 2 | 100% |
| GameTheory | 88 | 1 | 0 | 89 | 99% |
| GenAI | 95 | 105 | 2 | 202 | 47% |
| IIT | 65 | 0 | 0 | 65 | 100% |
| ML | 65 | 3 | 0 | 68 | 96% |
| Probas | 65 | 0 | 0 | 65 | 100% |
| QuantConnect | 65 | 44 | 0 | 109 | 60% |
| RL | 21 | 2 | 0 | 23 | 91% |
| Search | 138 | 0 | 0 | 138 | 100% |
| Sudoku | 36 | 1 | 0 | 37 | 97% |
| SymbolicAI | 251 | 8 | 0 | 259 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 681 |
| .NET (C#) | 251 |
| Lean 4 (WSL) | 36 |
| Python 3 (ipykernel) | 31 |
| Python (coursia-ml-training) | 11 |
| Python (GameTheory WSL + OpenSpiel) | 8 |
| Python 3 (WSL) | 7 |
| Python 3 (coursia-ml-training) | 6 |
| coursia-ml-training | 5 |
| Python 3 (PyPhi/IIT) | 5 |
| unknown | 3 |
| Lean 4 | 3 |
| Coursia ML Training | 2 |
| Python 3 (coursia2) | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python (CoursIA-2 venv) | 1 |
| Python 3 (coursia-sae) | 1 |
| pyphi | 1 |
| .venv (3.14.3) | 1 |
| .venv (3.12.3) | 1 |
| cours-ia | 1 |
| Python 3 (SC-16 Concrete, WSL) | 1 |
| Python 3 (smartcontracts) | 1 |
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
