# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-01**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1090** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 922 | 84.6% |
| DEMO | 166 | 15.2% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 684 |
| WSL requis | 74 |
| GPU requis | 123 |
| Cloud requis (QC / GenAI Docker) | 113 |
| API key requise | 174 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 90 | 1 | 0 | 91 | 99% |
| GenAI | 104 | 107 | 2 | 213 | 49% |
| IIT | 69 | 0 | 0 | 69 | 100% |
| ML | 68 | 3 | 0 | 71 | 96% |
| Probas | 66 | 0 | 0 | 66 | 100% |
| QuantConnect | 66 | 43 | 0 | 109 | 61% |
| RL | 21 | 3 | 0 | 24 | 88% |
| Search | 142 | 0 | 0 | 142 | 100% |
| Sudoku | 36 | 1 | 0 | 37 | 97% |
| SymbolicAI | 253 | 8 | 0 | 261 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 698 |
| .NET (C#) | 256 |
| Lean 4 (WSL) | 37 |
| Python 3 (ipykernel) | 32 |
| Python (coursia-ml-training) | 12 |
| Python (GameTheory WSL + OpenSpiel) | 8 |
| Python 3 (WSL) | 7 |
| coursia-ml-training | 6 |
| Python 3 (coursia-ml-training) | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Lean 4 | 3 |
| Coursia ML Training | 2 |
| Python 3 (coursia2) | 2 |
| unknown | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python (CoursIA-2 venv) | 1 |
| Python (dia-tts) | 1 |
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
