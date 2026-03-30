---
name: Series numbering fix status
description: Status of the (X/13) -> (X/20) series numbering fix across all 20 Infer.NET notebooks
type: project
---

All 20 notebooks in `D:\dev\CoursIA\MyIA.AI.Notebooks\Probas\Infer\` had their series numbering corrected from `(X/13)` to `(X/20)`.

**Why:** Notebooks 14-20 (decision theory series) were added later, bringing the total from 13 to 20. The first 13 notebooks still showed the old total.

**Status as of 2026-03-16:** COMPLETED - all 20 notebooks verified via grep showing no remaining `(X/13)` patterns.

**How to apply:** If new notebooks are added beyond 20, the same process must be repeated. Use grep to find old totals and NotebookEdit to fix first markdown cell of each notebook.

## Cell IDs for first markdown cell (header) per notebook

| Notebook | Cell ID |
|----------|---------|
| Infer-1-Setup | ab8b7b64 |
| Infer-2-Gaussian-Mixtures | 0b71b238 |
| Infer-3-Factor-Graphs | ab0e007e |
| Infer-4-Bayesian-Networks | 628e4ed2 |
| Infer-5-Skills-IRT | acede045 |
| Infer-6-TrueSkill | 579661f9 |
| Infer-7-Classification | 7a615707 |
| Infer-8-Model-Selection | 72aac374 |
| Infer-9-Topic-Models | 1452f2aa |
| Infer-10-Crowdsourcing | 9df317ec |
| Infer-11-Sequences | 087a352c |
| Infer-12-Recommenders | 3e3a7357 |
| Infer-13-Debugging | cell-0 (older format) |
| Infer-14 to Infer-20 | Already had correct (X/20) numbering |
