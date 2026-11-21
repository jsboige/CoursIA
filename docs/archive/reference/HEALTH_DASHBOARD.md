# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-11-21**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1815** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1578 | 86.9% |
| DEMO | 235 | 12.9% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 1109 |
| WSL requis | 211 |
| GPU requis | 225 |
| Cloud requis (QC / GenAI Docker) | 129 |
| API key requise | 240 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 175 | 2 | 0 | 177 | 99% |
| GenAI | 186 | 150 | 2 | 338 | 55% |
| IIT | 105 | 6 | 0 | 111 | 95% |
| InformationCalcul | 61 | 4 | 0 | 65 | 94% |
| ML | 137 | 20 | 0 | 157 | 87% |
| NLP | 20 | 0 | 0 | 20 | 100% |
| Physique | 24 | 0 | 0 | 24 | 100% |
| Probas | 95 | 1 | 0 | 96 | 99% |
| QuantConnect | 89 | 36 | 0 | 125 | 71% |
| RL | 39 | 5 | 0 | 44 | 89% |
| Search | 180 | 2 | 0 | 182 | 99% |
| Sudoku | 43 | 1 | 0 | 44 | 98% |
| SymbolicAI | 416 | 6 | 0 | 422 | 99% |
| cross-series | 2 | 2 | 0 | 4 | 50% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 1098 |
| .NET (C#) | 393 |
| Python 3 (ipykernel) | 76 |
| Lean 4 (WSL) | 65 |
| Python3 | 33 |
| Python (coursia-ml-training) | 21 |
| Python 3 (coursia-ml-training) | 15 |
| coursia-ml-training | 11 |
| unknown | 10 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Python 3 (venv projet) | 5 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| .Net-Csharp | 4 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Rust | 3 |
| Python 3.13.15 (CPython canonique serie Lean) | 3 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| .NET C# | 2 |
| Python 3.10 (gsplat) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
| Python 3 (coursia-canonical) | 2 |
| Python 3 (pyphi) | 2 |
| Lean 4 (WSL, percolation) | 2 |
| Lean 4 | 2 |
| .venv | 2 |
| Python 3 (c820) | 1 |
| Lean (WSL) | 1 |
| Python 3 (WSL + RVC) | 1 |
| Python (dia-tts) | 1 |
| pipecat-kokoro | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python (basicpitch-t4) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| Python 3 (venv) | 1 |
| Ict-Py313 | 1 |
| Python 3.13 (ict) | 1 |
| Python 3 (py310-gpu) | 1 |
| pyphi | 1 |
| Python 3.13 (coursia-py313) | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Py310-Gpu | 1 |
| Python 3 (CoursIA venv) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Python 3 (CoursIA-2) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| .NET(C#) | 1 |
| Python 3.13 (coursia-py313, argumentation) | 1 |
| Lean 4 (WSL, grothendieck-16200) | 1 |
| Python 3 (leandojo-v2) | 1 |
| Lean 4 (WSL, conway-build) | 1 |
| Python 3.13.x (CPython canonique série Lean) | 1 |
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
