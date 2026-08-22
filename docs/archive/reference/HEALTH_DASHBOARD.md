# Tableau de santé du dépôt — snapshot dérivé du catalogue

> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **2026-08-22**).
> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).
> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.

**939** notebooks référencés au catalogue.

## État global

| Statut | Count | % |
|--------|-------|---|
| READY | 776 | 82.6% |
| DEMO | 161 | 17.1% |
| BROKEN | 2 | 0.2% |

## Exigences d'environnement (badges)

| Exigence | Notebooks concernés |
|----------|---------------------|
| **local** (exécutable sans GPU/cloud/WSL) | 578 |
| WSL requis | 58 |
| GPU requis | 105 |
| Cloud requis (QC / GenAI Docker) | 111 |
| API key requise | 155 |

## Distribution par série

| Série | READY | DEMO | BROKEN | Total | % READY |
|-------|-------|------|--------|-------|---------|
| CaseStudies | 6 | 0 | 0 | 6 | 100% |
| FallacyDetection | 2 | 0 | 0 | 2 | 100% |
| GameTheory | 58 | 0 | 0 | 58 | 100% |
| GenAI | 80 | 100 | 2 | 182 | 44% |
| IIT | 58 | 0 | 0 | 58 | 100% |
| ML | 46 | 3 | 0 | 49 | 94% |
| Probas | 58 | 0 | 0 | 58 | 100% |
| QuantConnect | 61 | 47 | 0 | 108 | 56% |
| RL | 19 | 2 | 0 | 21 | 90% |
| Search | 118 | 0 | 0 | 118 | 100% |
| Sudoku | 36 | 1 | 0 | 37 | 97% |
| SymbolicAI | 233 | 8 | 0 | 241 | 97% |
| cross-series | 1 | 0 | 0 | 1 | 100% |

## Kernels

| Kernel | Count |
|--------|-------|
| Python 3 | 599 |
| .NET (C#) | 239 |
| Lean 4 (WSL) | 26 |
| Python 3 (ipykernel) | 24 |
| Python (GameTheory WSL + OpenSpiel) | 9 |
| Python 3 (WSL) | 7 |
| Python (coursia-ml-training) | 7 |
| coursia-ml-training | 4 |
| Python 3 (coursia-ml-training) | 4 |
| Python 3 (PyPhi/IIT) | 4 |
| Lean 4 | 3 |
| Python3 | 2 |
| .venv | 2 |
| Python 3 (coursia-sae) | 1 |
| Coursia ML Training | 1 |
| unknown | 1 |
| pyphi | 1 |
| .venv (3.14.3) | 1 |
| .venv (3.12.3) | 1 |
| cours-ia | 1 |
| Python 3 (SC-16 Concrete, WSL) | 1 |
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
