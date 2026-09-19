# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-19**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1227** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1036 | 84.4% |
| DEMO | 188 | 15.3% |
| BROKEN | 3 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 757 |
| WSL requis | 94 |
| GPU requis | 159 |
| Cloud requis (QC / GenAI Docker) | 116 |
| API key requise | 181 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 2 | 0 | 0 | 2 | 100% |
| GameTheory | 104 | 1 | 1 | 106 | 98% |
| GenAI | 113 | 118 | 2 | 233 | 48% |
| IIT | 77 | 2 | 0 | 79 | 97% |
| ML | 97 | 12 | 0 | 109 | 89% |
| Probas | 72 | 0 | 0 | 72 | 100% |
| QuantConnect | 68 | 44 | 0 | 112 | 61% |
| RL | 31 | 3 | 0 | 34 | 91% |
| Search | 152 | 0 | 0 | 152 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 276 | 7 | 0 | 283 | 98% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 802 |
| .NET (C#) | 261 |
| Lean 4 (WSL) | 43 |
| Python 3 (ipykernel) | 39 |
| Python (coursia-ml-training) | 16 |
| coursia-ml-training | 10 |
| Python 3 (coursia-ml-training) | 10 |
| Python 3 (WSL) | 7 |
| Python 3 (PyPhi/IIT) | 5 |
| unknown | 3 |
| Lean 4 | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| Coursia ML Training | 2 |
| Python 3 (coursia2) | 2 |
| Python3 | 2 |
| .venv | 2 |
| Lean (WSL) | 1 |
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
| GameTheory | GameTheory-06g — Agents à budget explicite (companion Lean natif) | DRAFT | 2026-09-12 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
