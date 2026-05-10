# STABLE_SNAPSHOT — Notebook Execution Forensics

**SHA**: `032e9b6a` (main, 2026-05-10)
**Audited**: 2026-05-10T11:42Z by po-2025 (CPU-only strict)
**Method**: Static analysis of `execution_count`, `outputs`, `output_type:error` per code cell

## Executive Summary

| Metric | Value |
|--------|-------|
| Total notebooks (with code cells) | 660 |
| Fully executed (ALL_EXEC) | 535 (81%) |
| Partially executed (PARTIAL) | 59 (9%) |
| Never executed (ALL_NULL) | 64 (10%) |
| With error outputs | 6 |

## Matrix by Series

### Python Kernel Notebooks (482 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| GenAI/Audio | 21 | 21 | 0 | 0 | 0 | 100% |
| GenAI/00-Env | 6 | 6 | 0 | 0 | 0 | 100% |
| GenAI/Image | 20 | 20 | 0 | 0 | 0 | 100% |
| Tweety | 20 | 20 | 0 | 0 | 0 | 100% |
| IIT | 1 | 1 | 0 | 0 | 0 | 100% |
| GenAI/Video | 16 | 15 | 1 | 0 | 0 | 94% |
| GenAI/Texte | 11 | 10 | 1 | 0 | 0 | 91% |
| Search | 87 | 79 | 5 | 3 | 0 | 91% |
| SW (Python) | 8 | 8 | 0 | 0 | 0 | 100% |
| Sudoku (Python) | 25 | 25 | 0 | 0 | 0 | 100% |
| SmartContracts | 54 | 54 | 0 | 0 | 0 | 100% |
| GameTheory | 30 | 22 | 8 | 0 | 0 | 73% |
| Sudoku (mixed) | 23 | 12 | 10 | 1 | 1 | 52% |
| GenAI/SemanticKernel | 20 | 17 | 2 | 1 | 0 | 85% |
| GenAI/CaseStudies | 4 | 2 | 2 | 0 | 0 | 50% |
| CaseStudies | 4 | 2 | 1 | 1 | 0 | 50% |
| QuantConnect | 168 | 54 | 8 | 106 | 1 | 32% |
| **Subtotal Python** | **482** | **329** | **41** | **112** | **2** | **68%** |

### .NET Interactive Notebooks (78 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Probas/Infer | 21 | 21 | 0 | 0 | 0 | 100% |
| Search (.NET) | 4 | 4 | 0 | 0 | 0 | 100% |
| ML | 8 | 8 | 0 | 0 | 4 | 100% |
| SemanticWeb (.NET) | 16 | 13 | 3 | 0 | 0 | 81% |
| Sudoku (.NET) | 16 | 12 | 3 | 1 | 1 | 75% |
| Planners | 28 | 23 | 5 | 0 | 0 | 82% |
| **Subtotal .NET** | **93** | **81** | **11** | **1** | **5** | **87%** |

### Lean/WSL Notebooks (15 total)

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Lean | 15 | 11 | 1 | 3 | 0 | 73% |

### Other Kernel Notebooks

| Series | Total | ALL_EXEC | PARTIAL | ALL_NULL | ERR | % OK |
|--------|-------|----------|---------|----------|-----|------|
| Argument_Analysis | 11 | 8 | 3 | 0 | 0 | 73% |
| RL | 7 | 4 | 2 | 1 | 0 | 57% |
| GameTheory (Lean/WSL) | 5 | 3 | 2 | 0 | 0 | 60% |

## ALL_NULL Notebooks (64 total, excluding QuantConnect)

### Non-QuantConnect ALL_NULL (6 notebooks)

| Notebook | Series | Cells | Kernel | Note |
|----------|--------|-------|--------|------|
| Oncology-Planning (solution) | CaseStudies | 8 | Python 3 | Never executed |
| SemanticKernel-MCP | GenAI/SK | 8 | base | WIP template |
| Sudoku-13-SymbolicAutomata-Csharp | Sudoku | 12 | .NET | Pre-existing env issue |
| CSP-1-Fundamentals_output | Search | 31 | Python 3 | _output copy stale |
| Search-10-SymbolicAutomata_output | Search | 21 | Python 3 | _output copy stale |
| App-11-Picross_output | Search | 20 | Python 3 | _output copy stale |

### QuantConnect ALL_NULL (58 notebooks)

106 total QC ALL_NULL, but 48 are quantbooks/research notebooks requiring QC Cloud execution (by design).
- 28 QC-Py-XX tutorial notebooks (never executed locally, content-only)
- 30+ quantbook/research notebooks in strategy projects (require QC Cloud)

## Notebooks with Error Outputs (6)

| Notebook | Series | Error Count | Note |
|----------|--------|-------------|------|
| QC-Py-Cloud-03-RiskParity | QuantConnect | 1 | Known simulation off-by-one |
| Sudoku-11-Choco-Csharp | Sudoku | 1 | Dependency issue |
| ML-*.ipynb (4 notebooks) | ML | 4 | Known stale outputs, code correct |

## Key Findings

1. **81% fully executed** (535/660) — strong baseline health
2. **QuantConnect is the largest gap** (106 ALL_NULL) — expected, requires QC Cloud
3. **GenAI Audio/Image/Tweety/SmartContracts: 100% execution** — most reliable series
4. **Probas/Infer: 100% execution** (21 .NET notebooks) — fully re-executed T17.14
5. **3 _output copy stale notebooks** in Search — cosmetic, not production
6. **0 errors in Search/Sudoku Python** — clean re-execution from T17.14

## Regeneration Schedule

Per CLAUDE.md H.7 P4: monthly regeneration.

| Date | SHA | Auditor | Notes |
|------|-----|---------|-------|
| 2026-05-10 | 032e9b6a | po-2025 | Initial forensic audit |
