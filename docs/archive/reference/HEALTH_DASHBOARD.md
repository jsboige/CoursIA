# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-09-02**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**1105** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 939 | 85.0% |
| DEMO | 164 | 14.8% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 697 |
| WSL requis | 76 |
| GPU requis | 124 |
| Cloud requis (QC / GenAI Docker) | 113 |
| API key requise | 172 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| GameTheory | 91 | 1 | 0 | 92 | 99% |
| GenAI | 106 | 106 | 2 | 214 | 50% |
| IIT | 71 | 0 | 0 | 71 | 100% |
| ML | 73 | 3 | 0 | 76 | 96% |
| Probas | 67 | 0 | 0 | 67 | 100% |
| QuantConnect | 67 | 42 | 0 | 109 | 61% |
| RL | 21 | 3 | 0 | 24 | 88% |
| Search | 146 | 0 | 0 | 146 | 100% |
| Sudoku | 36 | 1 | 0 | 37 | 97% |
| SymbolicAI | 254 | 8 | 0 | 262 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 710 |
| .NET (C#) | 257 |
| Lean 4 (WSL) | 38 |
| Python 3 (ipykernel) | 32 |
| Python (coursia-ml-training) | 12 |
| Python (GameTheory WSL + OpenSpiel) | 8 |
| Python 3 (WSL) | 7 |
| Python 3 (coursia-ml-training) | 7 |
| coursia-ml-training | 6 |
| Python 3 (PyPhi/IIT) | 5 |
| Lean 4 | 3 |
| Coursia ML Training | 2 |
| Python 3 (coursia2) | 2 |
| unknown | 2 |
| Python3 | 2 |
| .venv | 2 |
| Python (CoursIA-2 venv) | 1 |
| Python (dia-tts) | 1 |
| Python 3 (coursia-sae) | 1 |
| pyphi | 1 |
| .venv (3.14.3) | 1 |
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
