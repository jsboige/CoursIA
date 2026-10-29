# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-10-28**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1549** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1331 | 85.9% |
| DEMO | 216 | 13.9% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 911 |
| WSL requis | 182 |
| GPU requis | 206 |
| Cloud requis (QC / GenAI Docker) | 127 |
| API key requise | 218 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 18 | 1 | 0 | 19 | 95% |
| Compression | 8 | 0 | 0 | 8 | 100% |
| GameTheory | 132 | 2 | 0 | 134 | 99% |
| GenAI | 157 | 138 | 2 | 297 | 53% |
| IIT | 101 | 7 | 0 | 108 | 94% |
| ML | 118 | 21 | 0 | 139 | 85% |
| NLP | 6 | 0 | 0 | 6 | 100% |
| Probas | 91 | 1 | 0 | 92 | 99% |
| QuantConnect | 89 | 34 | 0 | 123 | 72% |
| RL | 32 | 5 | 0 | 37 | 86% |
| Search | 160 | 0 | 0 | 160 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 375 | 5 | 0 | 380 | 99% |
| cross-series | 1 | 1 | 0 | 2 | 50% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 1015 |
| .NET (C#) | 271 |
| Python 3 (ipykernel) | 65 |
| Lean 4 (WSL) | 63 |
| Python (coursia-ml-training) | 21 |
| Python 3 (coursia-ml-training) | 18 |
| coursia-ml-training | 11 |
| unknown | 9 |
| Python 3 (WSL) | 6 |
| Python3 | 5 |
| Python 3 (PyPhi/IIT) | 5 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Python 3.13.15 (CPython canonique serie Lean) | 3 |
| Python 3 (venv projet) | 2 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| Python 3.10 (gsplat) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
| Lean 4 (WSL, percolation) | 2 |
| Lean 4 | 2 |
| .venv | 2 |
| Lean (WSL) | 1 |
| Python 3 (c820) | 1 |
| .venv (3.12.14) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python (basicpitch-t4) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| Python 3 (venv) | 1 |
| Python 3 (py310-gpu) | 1 |
| Python 3 (pyphi) | 1 |
| pyphi | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Py310-Gpu | 1 |
| Python 3 (CoursIA venv) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Python 3 (CoursIA-2) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
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
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
