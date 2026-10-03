# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-10-02**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1340** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1137 | 84.9% |
| DEMO | 201 | 15.0% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 814 |
| WSL requis | 118 |
| GPU requis | 180 |
| Cloud requis (QC / GenAI Docker) | 119 |
| API key requise | 191 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 9 | 0 | 0 | 9 | 100% |
| Compression | 1 | 0 | 0 | 1 | 100% |
| GameTheory | 108 | 1 | 0 | 109 | 99% |
| GenAI | 131 | 124 | 2 | 257 | 51% |
| IIT | 88 | 5 | 0 | 93 | 95% |
| ML | 108 | 18 | 0 | 126 | 86% |
| NLP | 5 | 0 | 0 | 5 | 100% |
| Probas | 76 | 0 | 0 | 76 | 100% |
| QuantConnect | 71 | 44 | 0 | 115 | 62% |
| RL | 33 | 3 | 0 | 36 | 92% |
| Search | 156 | 0 | 0 | 156 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 307 | 5 | 0 | 312 | 98% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 879 |
| .NET (C#) | 265 |
| Python 3 (ipykernel) | 49 |
| Lean 4 (WSL) | 48 |
| Python (coursia-ml-training) | 17 |
| Python 3 (coursia-ml-training) | 17 |
| coursia-ml-training | 12 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 6 |
| Coursia ML Training | 3 |
| unknown | 3 |
| Lean 4 | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
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
| pyphi | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Lean 4 (WSL, percolation) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
| Python 3.13.x (CPython canonique serie Lean) | 1 |
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
