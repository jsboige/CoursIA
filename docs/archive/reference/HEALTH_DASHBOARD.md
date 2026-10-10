# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-10-10**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1397** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1183 | 84.7% |
| DEMO | 212 | 15.2% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 835 |
| WSL requis | 132 |
| GPU requis | 192 |
| Cloud requis (QC / GenAI Docker) | 124 |
| API key requise | 200 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 14 | 0 | 0 | 14 | 100% |
| Compression | 1 | 0 | 0 | 1 | 100% |
| GameTheory | 110 | 1 | 0 | 111 | 99% |
| GenAI | 138 | 127 | 2 | 267 | 52% |
| IIT | 91 | 7 | 0 | 98 | 93% |
| ML | 114 | 21 | 0 | 135 | 84% |
| NLP | 5 | 0 | 0 | 5 | 100% |
| Probas | 83 | 0 | 0 | 83 | 100% |
| QuantConnect | 74 | 46 | 0 | 120 | 62% |
| RL | 31 | 4 | 0 | 35 | 89% |
| Search | 157 | 0 | 0 | 157 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 320 | 5 | 0 | 325 | 98% |
| cross-series | 2 | 0 | 0 | 2 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 913 |
| .NET (C#) | 268 |
| Python 3 (ipykernel) | 50 |
| Lean 4 (WSL) | 49 |
| Python 3 (coursia-ml-training) | 18 |
| Python (coursia-ml-training) | 17 |
| coursia-ml-training | 12 |
| unknown | 7 |
| Python 3 (WSL) | 6 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Python 3 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Lean 4 | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
| Python 3.13.15 (CPython canonique serie Lean) | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python 3 (venv projet) | 1 |
| Lean (WSL) | 1 |
| Python 3 (c820) | 1 |
| .venv (3.12.14) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| Python 3 (venv) | 1 |
| Python 3 (py310-gpu) | 1 |
| pyphi | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Py310-Gpu | 1 |
| Lean 4 (WSL, percolation) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
| Python 3 (leandojo-v2) | 1 |
| Lean 4 (WSL, conway-build) | 1 |
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
