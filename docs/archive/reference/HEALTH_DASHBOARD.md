# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-11-13**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1633** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1409 | 86.3% |
| DEMO | 222 | 13.6% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 955 |
| WSL requis | 205 |
| GPU requis | 215 |
| Cloud requis (QC / GenAI Docker) | 128 |
| API key requise | 227 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 22 | 2 | 0 | 24 | 92% |
| Compression | 9 | 0 | 0 | 9 | 100% |
| GameTheory | 139 | 2 | 0 | 141 | 99% |
| GenAI | 167 | 142 | 2 | 311 | 54% |
| IIT | 107 | 7 | 0 | 114 | 94% |
| ML | 117 | 20 | 0 | 137 | 85% |
| NLP | 11 | 0 | 0 | 11 | 100% |
| Physique | 11 | 0 | 0 | 11 | 100% |
| Probas | 92 | 1 | 0 | 93 | 99% |
| QuantConnect | 90 | 34 | 0 | 124 | 73% |
| RL | 33 | 5 | 0 | 38 | 87% |
| Search | 165 | 1 | 0 | 166 | 99% |
| Sudoku | 38 | 1 | 0 | 39 | 97% |
| SymbolicAI | 401 | 6 | 0 | 407 | 99% |
| cross-series | 1 | 1 | 0 | 2 | 50% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 1072 |
| .NET (C#) | 277 |
| Python 3 (ipykernel) | 74 |
| Lean 4 (WSL) | 65 |
| Python (coursia-ml-training) | 21 |
| Python 3 (coursia-ml-training) | 15 |
| Python3 | 12 |
| coursia-ml-training | 11 |
| unknown | 10 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| Python 3 (venv projet) | 4 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Python 3.13.15 (CPython canonique serie Lean) | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| Python 3.10 (gsplat) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
| Lean 4 (WSL, percolation) | 2 |
| Lean 4 | 2 |
| .venv | 2 |
| Python 3.13 (coursia-py313) | 1 |
| Python 3 (c820) | 1 |
| Lean (WSL) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python (basicpitch-t4) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| Python 3 (venv) | 1 |
| Ict-Py313 | 1 |
| Python 3 (py310-gpu) | 1 |
| Python 3 (pyphi) | 1 |
| Python 3 (coursia-canonical) | 1 |
| pyphi | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Py310-Gpu | 1 |
| Python 3 (CoursIA venv) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Python 3 (CoursIA-2) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| Python 3.13 (coursia-py313, argumentation) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
| Python 3 (leandojo-v2) | 1 |
| Lean 4 (WSL, conway-build) | 1 |
| Python 3.11 (po-2028) | 1 |
| .venv (3.12.3) | 1 |
| cours-ia | 1 |
| Python 3 (SC-16 Concrete, WSL) | 1 |
| Python 3 (smartcontracts) | 1 |
| Python (difflogic-sl12) | 1 |

## BROKEN (2 — à traiter en priorité)

| Série | Notebook | Maturité | Dernière validation |
|-------|----------|----------|---------------------|
| GenAI | Notebook de travail | TEMPLATE | 2026-11-04 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
