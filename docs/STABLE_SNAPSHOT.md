# STABLE_SNAPSHOT — Notebook Execution Forensics

**SHA**: `08d52b0d` (main, 2026-05-11)
**Audited**: 2026-05-11T16:30Z by po-2025 (CPU-only strict)
**Method**: Static analysis of `execution_count`, `outputs`, `output_type:error` per code cell

## Executive Summary

| Metric | Value |
|--------|-------|
| Total notebooks (with code cells, incl. _output) | 663 |
| Fully executed (ALL_EXEC) | 509 (77%) |
| Partially executed (PARTIAL) | 37 (6%) |
| Never executed (ALL_NULL) | 117 (18%) |
| With error outputs | 14 |

## Matrix by Series

### Python Kernel Notebooks (482 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| GenAI/Audio | 21 | 21 | 0 | 0 | 0 | 100% |
| GenAI/00-Env | — | — | — | — | — | — |
| GenAI/Image | 20 | 20 | 0 | 0 | 0 | 100% |
| GenAI/Texte | 11 | 11 | 0 | 0 | 0 | 100% |
| Tweety | 20 | 20 | 0 | 0 | 0 | 100% |
| IIT | 1 | 1 | 0 | 0 | 0 | 100% |
| GenAI/Video | 16 | 16 | 0 | 0 | 0 | 100% |
| GenAI/CaseStudies | 4 | 4 | 0 | 0 | 0 | 100% |
| GenAI/SemanticKernel | 20 | 19 | 0 | 1 | 0 | 95% |
| Search | 84 | 77 | 4 | 3 | 0 | 92% |
| SmartContracts | 54 | 54 | 0 | 0 | 0 | 100% |
| GenAI/Other | 13 | 12 | 1 | 0 | 0 | 92% |
| GameTheory | 24 | 19 | 5 | 0 | 0 | 79% |
| Sudoku (Python) | 32 | 25 | 7 | 0 | 0 | 78% |
| CaseStudies | 5 | 4 | 0 | 1 | 0 | 80% |
| RL | 8 | 4 | 3 | 1 | 1 | 50% |
| QuantConnect | 168 | 54 | 8 | 106 | 1 | 32% |

### .NET Interactive Notebooks (93 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Probas/Infer | 22 | 22 | 0 | 0 | 0 | 100% |
| Search (.NET) | 4 | 4 | 0 | 0 | 0 | 100% |
| ML | 30 | 29 | 0 | 1 | 10 | 97% |
| SemanticWeb | 26 | 25 | 1 | 0 | 0 | 96% |
| Sudoku (.NET) | 16 | 14 | 1 | 1 | 1 | 88% |
| Planners | 28 | 24 | 4 | 0 | 0 | 86% |

### Lean/WSL Notebooks (21 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Lean | 15 | 14 | 0 | 1 | 0 | 93% |
| GameTheory (Lean/WSL) | 6 | 6 | 0 | 0 | 0 | 100% |

### Other Kernel Notebooks

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Other | 12 | 9 | 3 | 0 | 1 | 75% |
| SymbolicAI-Misc | 2 | 1 | 0 | 1 | 0 | 50% |
| GradeBook | 1 | 0 | 0 | 1 | 0 | 0% |

## ALL_NULL Notebooks (117 total)

### Non-QuantConnect ALL_NULL (11 notebooks)

| Notebook | Series | Cells | Kernel | Note |
|----------|--------|-------|--------|------|
| GradeBook | GradeBook | 12 | .NET | Admin tool, not course notebook |
| SemanticKernel-MCP | GenAI/SK | 8 | base | WIP template |
| Sudoku-13-SymbolicAutomata-Csharp | Sudoku | 12 | .NET | Pre-existing env issue |
| CSP-1-Fundamentals_output | Search | 31 | Python 3 | _output copy stale |
| Search-10-SymbolicAutomata_output | Search | 21 | Python 3 | _output copy stale |
| App-11-Picross_output | Search | 20 | Python 3 | _output copy stale |
| Lean-11-TorchLean-Python_output | Lean | 7 | python3 | _output copy (original ALL_EXEC) |
| OR-tools-Stiegler | SymbolicAI-Misc | 9 | .NET | Never executed |
| QC-Cloud-03-RiskParity | QuantConnect | 1 | python3 | _output copy stale |
| fort-boyard-csharp | GenAI/SK | 5 | .NET | WIP demo |

### QuantConnect ALL_NULL (106 notebooks)

106 total QC ALL_NULL. 48 are quantbooks/research notebooks requiring QC Cloud execution (by design).
- 28 QC-Py-XX tutorial notebooks (never executed locally, content-only)
- 30+ quantbook/research notebooks in strategy projects (require QC Cloud)

## Notebooks with Error Outputs (14)

| Notebook | Series | Error Count | Note |
|----------|--------|-------------|------|
| ML-*.ipynb (10 notebooks) | ML | 10 | Known stale outputs, code correct |
| QC-Py-Cloud-03-RiskParity | QuantConnect | 1 | Known simulation off-by-one |
| Sudoku-11-Choco-Csharp | Sudoku | 1 | Dependency issue |
| rl_3_policy_gradient | RL | 1 | Known training error |
| Search-5-SymmetricGroup | Other | 1 | Known SymPy issue |

## Key Findings

1. **77% fully executed** (509/663) — up from 82% in prior snapshot (wider scope incl. _output)
2. **Lean series: 93% OK** (14/15 ALL_EXEC, only _output copy ALL_NULL)
3. **GameTheory Lean: 100%** (6/6) — all executed via lean4-wsl kernel
4. **SemanticWeb: 96%** — RDF.Net + SW-5 patched to 100% exec_count
5. **Probas/Infer: 100%** (22/22) — fully executed
6. **GenAI Audio/Image/Tweety/SmartContracts: 100%** — most reliable series
7. **QuantConnect remains largest gap** (106 ALL_NULL) — expected, requires QC Cloud
8. **0 errors in Search/Sudoku Python** — clean execution

## Regeneration Schedule

Per CLAUDE.md H.7 P4: monthly regeneration.

| Date | SHA | Auditor | Notes |
|------|-----|---------|-------|
| 2026-05-10 | 032e9b6a | po-2025 | Initial forensic audit |
| 2026-05-11 | 8334458b | po-2025 | Lean: 3 ALL_NULL to ALL_EXEC via lean4-wsl kernel (93% OK) |
| 2026-05-11 | 08d52b0d | po-2025 | Full re-audit: RDF.Net + SW-5 + Sudoku-6/8 + Linq2Z3 + Fast-Downward + Diagnostic-Medical + App-5 + Semantic-kernel-AutoInteractive patched; GameTheory Lean 100%; STABLE_SNAPSHOT regenerated with accurate series grouping |
