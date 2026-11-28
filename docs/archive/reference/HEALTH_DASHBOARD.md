# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-11-28**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**2093** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 1848 | 88.3% |
| DEMO | 243 | 11.6% |
| BROKEN | 2 | 0.1% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 1347 |
| WSL requis | 239 |
| GPU requis | 230 |
| Cloud requis (QC / GenAI Docker) | 130 |
| API key requise | 247 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| BioMedecine | 2 | 0 | 0 | 2 | 100% |
| CaseStudies | 7 | 0 | 0 | 7 | 100% |
| GameTheory | 226 | 2 | 0 | 228 | 99% |
| GenAI | 197 | 155 | 2 | 354 | 56% |
| IIT | 123 | 6 | 0 | 129 | 95% |
| InformationCalcul | 94 | 6 | 0 | 100 | 94% |
| ML | 144 | 20 | 0 | 164 | 88% |
| NLP | 21 | 0 | 0 | 21 | 100% |
| Physique | 59 | 0 | 0 | 59 | 100% |
| Probas | 97 | 2 | 0 | 99 | 98% |
| QuantConnect | 90 | 36 | 0 | 126 | 71% |
| RL | 46 | 5 | 0 | 51 | 90% |
| Search | 203 | 2 | 0 | 205 | 99% |
| Sudoku | 49 | 1 | 0 | 50 | 98% |
| SymbolicAI | 485 | 6 | 0 | 491 | 99% |
| cross-series | 5 | 2 | 0 | 7 | 71% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 1123 |
| .NET (C#) | 536 |
| Rust | 84 |
| Python 3 (ipykernel) | 83 |
| Lean 4 (WSL) | 66 |
| Python3 | 39 |
| Python (coursia-ml-training) | 21 |
| Python 3 (coursia-ml-training) | 15 |
| coursia-ml-training | 11 |
| unknown | 10 |
| .Net-Csharp | 8 |
| Python 3 (WSL) | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Python 3 (venv projet) | 5 |
| Python 3.13.x (CPython canonique serie Lean) | 5 |
| Python 3.9 (PyPhi/IIT) | 4 |
| Coursia ML Training | 3 |
| Python 3.13 (ict) | 3 |
| Lean 4 (WSL, linear-build) | 3 |
| Python 3.13.x (CPython canonique série Lean) | 3 |
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
| rust | 1 |
| Python (dia-tts) | 1 |
| Python 3 (WSL + RVC) | 1 |
| coursia-genai-audio | 1 |
| Coursia-Genai-Audio | 1 |
| pipecat-kokoro | 1 |
| Python 3 (mert2-gpu) | 1 |
| Python (sheetsage2-gpu) | 1 |
| Python (basicpitch-t4) | 1 |
| Python 3 (PyTorch) | 1 |
| Python 3 (coursia-sae) | 1 |
| Python 3 (venv) | 1 |
| Ict-Py313 | 1 |
| Python 3 (py310-gpu) | 1 |
| pyphi | 1 |
| Python 3.13 (coursia-py313) | 1 |
| Python 3.11 (coursia-drift) | 1 |
| Coursia-Ml-Training | 1 |
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
