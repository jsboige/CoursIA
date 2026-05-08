# Stabilization Phase 1 — Matrix

**Date**: 2026-05-08
**Source**: Aggregation of audit_c1_c3.py scan, COURSE_CATALOG.generated.json, qc-stabilization-phase2.md
**Scope**: 1106 pedagogical notebooks across 12 families

---

## C.1 Compliance (No Intentional Errors)

Full scan via `scripts/notebook_tools/audit_c1_c3.py --check c1`:

| Family | Notebooks | C.1 Violations | Status |
|--------|-----------|----------------|--------|
| QuantConnect | 620 | 0 | CLEAN |
| SymbolicAI | 154 | 0 | CLEAN |
| GenAI | 102 | 0 | CLEAN |
| Search | 87 | 0 | CLEAN |
| Sudoku | 48 | 0 | CLEAN |
| ML | 30 | 0 | CLEAN |
| GameTheory | 30 | 0 | CLEAN |
| Probas | 22 | 0 | CLEAN |
| RL | 7 | 0 | CLEAN |
| EPF | 4 | 0 | CLEAN |
| IIT | 1 | 0 | CLEAN |
| GradeBook | 1 | 0 | CLEAN |
| **TOTAL** | **1106** | **0** | **ALL CLEAN** |

## Catalog Coverage

Current `COURSE_CATALOG.generated.json` covers 40/1106 notebooks (3.6%):

| Family | Total NBs | In Catalog | Coverage | Maturity Breakdown |
|--------|-----------|------------|----------|--------------------|
| QuantConnect | 620 | 20 | 3.2% | DRAFT:20 |
| SymbolicAI | 154 | 5 | 3.2% | ALPHA:1, DRAFT:4 |
| GenAI | 102 | 5 | 4.9% | DRAFT:5 |
| Search | 87 | 0 | 0% | N/A |
| Sudoku | 48 | 4 | 8.3% | BETA:3, PRODUCTION:1 |
| ML | 30 | 4 | 13.3% | ALPHA:2, BETA:1, DRAFT:1 |
| GameTheory | 30 | 0 | 0% | N/A |
| Probas | 22 | 0 | 0% | N/A |
| RL | 7 | 0 | 0% | N/A |
| EPF | 4 | 1 | 25% | DRAFT:1 |
| IIT | 1 | 1 | 100% | ALPHA:1 |
| GradeBook | 1 | 0 | 0% | N/A |
| **TOTAL** | **1106** | **40** | **3.6%** | DRAFT:31, ALPHA:4, BETA:4, PRODUCTION:1 |

## Kernel Distribution (SymbolicAI Focus)

89 primary notebooks in SymbolicAI require 7 kernel types:

| Kernel | Count | Family | Machine Required |
|--------|-------|--------|------------------|
| Python 3 | 27 | SmartContracts | Any |
| Python (SmartContracts + Foundry) | 27 | SmartContracts | ai-01 (Foundry/Anvil) |
| .NET (C#) | 10 | SemanticWeb, Probas | ai-01 (.NET SDK) |
| mcp-jupyter-py310 | 10 | Tweety | Any |
| Python 3 (WSL) | 6 | Planners | WSL machine |
| Lean 4 | 6 | Lean | WSL + Lean machine |
| base | 3 | Argument_Analysis | Any |

## Known Issues (from Previous Audits)

| Issue | Source | Status | Families Affected |
|-------|--------|--------|-------------------|
| NanoClaw false positives (60-83%) | audit-reassessment rule | Resolved (#499) | All |
| QC strategies BROKEN vs PEDAGOGICAL | qc-stabilization-phase2.md | Phase 2 planned | QuantConnect |
| GenAI .env service dependencies | genai-config rule | Config-dependent | GenAI |
| WSL kernel timeout (60s cold start) | wsl-kernels rule | Known limitation | SymbolicAI/Planners, GameTheory |
| GPU training thermal crashes (10x) | MEMORY.md postmortems | STOPPED | ML-Training-Pipeline |

## Priority Actions

### Phase 1.1 — Catalog Expansion (coverage 3.6% → target 50%)
- Run `generate_catalog.py` for uncovered families: Search, GameTheory, Probas, RL
- Assign maturity labels based on notebook execution history

### Phase 1.2 — SymbolicAI Smoke Test (13-14/05)
- Schedule Papermill re-runs for 89 notebooks
- Coordinate across machines for kernel availability
- Post-exec: run audit_c1_c3.py to verify C.3 compliance

### Phase 1.3 — QC Strategy Classification (Phase 2)
- Apply decision tree from qc-stabilization-phase2.md to 70+ open issues
- Label: BROKEN_PEDAGOGICAL, BROKEN_TO_FIX, NEEDS_IMPROVEMENT, HEALTHY

## Tools Available

| Tool | Usage |
|------|-------|
| `scripts/notebook_tools/audit_c1_c3.py` | C.1 + C.3 repo-wide scan (1106 NBs) |
| `scripts/notebook_tools/notebook_lint.py` | C.1 + C.2 + structure + metadata (per NB/family) |
| `scripts/notebook_tools/notebook_tools.py validate` | Structural validation |
| `scripts/notebook_tools/notebook_tools.py execute` | Papermill execution |
| `COURSE_CATALOG.generated.json` | Maturity + metadata index (40 entries) |
