# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-07**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1137** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 961 | 84.5% |
| DEMO | 174 | 15.3% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 717 |
| WSL requis | 79 |
| GPU requis | 127 |
| Cloud requis (QC / GenAI Docker) | 114 |
| API key requise | 177 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 100 | 1 | 0 | 101 | 99% |
| GenAI | 102 | 111 | 2 | 215 | 47% |
| IIT | 71 | 1 | 0 | 72 | 99% |
| ML | 74 | 7 | 0 | 81 | 91% |
| Probas | 69 | 0 | 0 | 69 | 100% |
| QuantConnect | 67 | 43 | 0 | 110 | 61% |
| RL | 23 | 3 | 0 | 26 | 88% |
| Search | 150 | 0 | 0 | 150 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 261 | 7 | 0 | 268 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 738 |
| .NET (C#) | 260 |
| Lean 4 (WSL) | 41 |
| Python 3 (ipykernel) | 34 |
| Python (coursia-ml-training) | 12 |
| Python 3 (WSL) | 7 |
| Python 3 (coursia-ml-training) | 7 |
| coursia-ml-training | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Lean 4 | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| Coursia ML Training | 2 |
| Python 3 (coursia2) | 2 |
| unknown | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python (CoursIA-2 venv) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (coursia-sae) | 1 |
| pyphi | 1 |
| Lean 4 (WSL, percolation) | 1 |
| Foundation-Py-Default | 1 |
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
