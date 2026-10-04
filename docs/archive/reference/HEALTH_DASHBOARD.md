# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-10-04**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1354** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1149 | 84.9% |
| DEMO | 203 | 15.0% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 819 |
| WSL requis | 123 |
| GPU requis | 182 |
| Cloud requis (QC / GenAI Docker) | 119 |
| API key requise | 193 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 10 | 0 | 0 | 10 | 100% |
| Compression | 1 | 0 | 0 | 1 | 100% |
| GameTheory | 109 | 1 | 0 | 110 | 99% |
| GenAI | 133 | 124 | 2 | 259 | 51% |
| IIT | 88 | 6 | 0 | 94 | 94% |
| ML | 109 | 18 | 0 | 127 | 86% |
| NLP | 5 | 0 | 0 | 5 | 100% |
| Probas | 77 | 0 | 0 | 77 | 100% |
| QuantConnect | 71 | 44 | 0 | 115 | 62% |
| RL | 33 | 4 | 0 | 37 | 89% |
| Search | 157 | 0 | 0 | 157 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 312 | 5 | 0 | 317 | 98% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 887 |
| .NET (C#) | 266 |
| Lean 4 (WSL) | 48 |
| Python 3 (ipykernel) | 48 |
| Python (coursia-ml-training) | 17 |
| Python 3 (coursia-ml-training) | 17 |
| coursia-ml-training | 12 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 6 |
| Coursia ML Training | 3 |
| unknown | 3 |
| Lean 4 | 3 |
| Python 3.13.x (CPython canonique serie Lean) | 3 |
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
| Python 3 (py310-gpu) | 1 |
| pyphi | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Lean 4 (WSL, percolation) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
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
