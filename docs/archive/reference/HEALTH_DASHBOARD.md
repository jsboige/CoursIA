# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-27**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1312** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1111 | 84.7% |
| DEMO | 198 | 15.1% |
| BROKEN | 3 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 809 |
| WSL requis | 104 |
| GPU requis | 173 |
| Cloud requis (QC / GenAI Docker) | 119 |
| API key requise | 189 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 9 | 0 | 0 | 9 | 100% |
| GameTheory | 107 | 1 | 1 | 109 | 98% |
| GenAI | 124 | 121 | 2 | 247 | 50% |
| IIT | 85 | 5 | 0 | 90 | 94% |
| ML | 104 | 16 | 0 | 120 | 87% |
| NLP | 5 | 0 | 0 | 5 | 100% |
| Probas | 74 | 0 | 0 | 74 | 100% |
| QuantConnect | 71 | 44 | 0 | 115 | 62% |
| RL | 33 | 3 | 0 | 36 | 92% |
| Search | 155 | 0 | 0 | 155 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 300 | 7 | 0 | 307 | 98% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 859 |
| .NET (C#) | 264 |
| Python 3 (ipykernel) | 48 |
| Lean 4 (WSL) | 47 |
| Python (coursia-ml-training) | 17 |
| Python 3 (coursia-ml-training) | 15 |
| coursia-ml-training | 12 |
| Python 3 (WSL) | 7 |
| Python 3 (PyPhi/IIT) | 6 |
| Coursia ML Training | 3 |
| unknown | 3 |
| Lean 4 | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| Python 3 (coursia2) | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python 3 (venv projet) | 1 |
| Lean (WSL) | 1 |
| Python 3 (c820) | 1 |
| Python (CoursIA-2 venv) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| pyphi | 1 |
| Lean 4 (WSL, percolation) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| Lean 4 (WSL, conway-build) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
| .venv (3.12.3) | 1 |
| cours-ia | 1 |
| Python 3 (SC-16 Concrete, WSL) | 1 |
| Python 3 (smartcontracts) | 1 |
| Python (difflogic-sl12) | 1 |

## BROKEN (3 — à traiter en priorité)

| Série | Notebook | Maturité | Dernière validation |
|-------|----------|----------|---------------------|
| GameTheory | GameTheory-06g — Agents à budget explicite (companion Lean natif) | DRAFT | 2026-09-21 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
