# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-11-20**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1786** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1553 | 87.0% |
| DEMO | 231 | 12.9% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 1086 |
| WSL requis | 209 |
| GPU requis | 223 |
| Cloud requis (QC / GenAI Docker) | 129 |
| API key requise | 238 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| Complexity | 42 | 2 | 0 | 44 | 95% |
| Compression | 15 | 2 | 0 | 17 | 88% |
| GameTheory | 168 | 2 | 0 | 170 | 99% |
| GenAI | 184 | 149 | 2 | 335 | 55% |
| IIT | 104 | 6 | 0 | 110 | 95% |
| ML | 137 | 20 | 0 | 157 | 87% |
| NLP | 20 | 0 | 0 | 20 | 100% |
| Physique | 23 | 0 | 0 | 23 | 100% |
| Probas | 95 | 1 | 0 | 96 | 99% |
| QuantConnect | 91 | 34 | 0 | 125 | 73% |
| RL | 39 | 5 | 0 | 44 | 89% |
| Search | 177 | 2 | 0 | 179 | 99% |
| Sudoku | 41 | 1 | 0 | 42 | 98% |
| SymbolicAI | 409 | 6 | 0 | 415 | 99% |
| cross-series | 2 | 1 | 0 | 3 | 67% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 1090 |
| .NET (C#) | 378 |
| Python 3 (ipykernel) | 75 |
| Lean 4 (WSL) | 65 |
| Python3 | 32 |
| Python (coursia-ml-training) | 21 |
| Python 3 (coursia-ml-training) | 15 |
| coursia-ml-training | 11 |
| unknown | 10 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| Python 3 (venv projet) | 4 |
| .Net-Csharp | 4 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Python 3.13.15 (CPython canonique serie Lean) | 3 |
| Python 3 (coursia-canonical) | 2 |
| Python (GameTheory WSL + OpenSpiel) | 2 |
| .NET C# | 2 |
| Python 3.10 (gsplat) | 2 |
| base | 2 |
| Python 3 (coursia2) | 2 |
| Lean 4 (WSL, percolation) | 2 |
| Lean 4 | 2 |
| .venv | 2 |
| Python 3.13 (coursia-py313) | 1 |
| Python 3 (pyphi) | 1 |
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
| Python 3.11 (coursia-drift) | 1 |
| Py310-Gpu | 1 |
| Python 3 (CoursIA venv) | 1 |
| Python 3 (PyMC 3.11) | 1 |
| Python 3 (CoursIA-2) | 1 |
| Foundation-Py-Default | 1 |
| .venv (3.14.3) | 1 |
| .NET(C#) | 1 |
| Rust | 1 |
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
