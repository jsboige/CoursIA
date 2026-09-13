# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-07**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1146** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 967 | 84.4% |
| DEMO | 176 | 15.4% |
| BROKEN | 3 | 0.3% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 722 |
| WSL requis | 81 |
| GPU requis | 129 |
| Cloud requis (QC / GenAI Docker) | 114 |
| API key requise | 178 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 102 | 1 | 1 | 104 | 98% |
| GenAI | 102 | 112 | 2 | 216 | 47% |
| IIT | 72 | 2 | 0 | 74 | 97% |
| ML | 74 | 7 | 0 | 81 | 91% |
| Probas | 71 | 0 | 0 | 71 | 100% |
| QuantConnect | 67 | 43 | 0 | 110 | 61% |
| RL | 23 | 3 | 0 | 26 | 88% |
| Search | 150 | 0 | 0 | 150 | 100% |
| Sudoku | 37 | 1 | 0 | 38 | 97% |
| SymbolicAI | 262 | 7 | 0 | 269 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 743 |
| .NET (C#) | 260 |
| Lean 4 (WSL) | 41 |
| Python 3 (ipykernel) | 34 |
| Python (coursia-ml-training) | 14 |
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
| Lean (WSL) | 1 |
| Python (CoursIA-2 venv) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (mert2-gpu) | 1 |
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

## BROKEN (3 — à traiter en priorité)

| Série | Notebook | Maturité | Dernière validation |
|-------|----------|----------|---------------------|
| GameTheory | GameTheory-06g — Agents à budget explicite (companion Lean natif) | DRAFT |  |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |
| GenAI | Notebook de travail | TEMPLATE | 2026-07-30 |

## Voir aussi

- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.
- See #4210 (onboarding/packaging, acceptance #4).
- See #4208 (CoursIA → référence publique).
