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

Updated `COURSE_CATALOG.generated.json` covers 453/1106 notebooks (41%). All families now represented.

| Family | Total NBs | In Catalog | Coverage | Maturity Breakdown |
|--------|-----------|------------|----------|--------------------|
| QuantConnect | 97 | 97 | 100% | ALPHA:13, BETA:3, DRAFT:67, PRODUCTION:14 |
| GenAI | 99 | 99 | 100% | ALPHA:60, BETA:5, DRAFT:24, PRODUCTION:10 |
| SymbolicAI | 90 | 90 | 100% | ALPHA:56, BETA:29, DRAFT:4, PRODUCTION:1 |
| Search | 45 | 45 | 100% | ALPHA:33, BETA:4, DRAFT:7, PRODUCTION:1 |
| Sudoku | 32 | 32 | 100% | ALPHA:19, BETA:11, PRODUCTION:2 |
| ML | 30 | 30 | 100% | ALPHA:25, BETA:3, DRAFT:2 |
| GameTheory | 27 | 27 | 100% | ALPHA:21, BETA:3, DRAFT:3 |
| Probas | 22 | 22 | 100% | ALPHA:18, PRODUCTION:4 |
| EPF | 4 | 4 | 100% | ALPHA:1, DRAFT:2, PRODUCTION:1 |
| RL | 6 | 6 | 100% | ALPHA:6 |
| IIT | 1 | 1 | 100% | ALPHA:1 |
| **TOTAL** | **453** | **453** | **100%** | **PRODUCTION:33, BETA:58, ALPHA:253, DRAFT:109** |

Status summary: 233 READY, 203 DEMO, 0 RESEARCH, 17 BROKEN.

Note: 453 excludes research/archive/examples notebooks (pedagogical only). 1106 total includes all.

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

### Phase 1.1 — Catalog Expansion (DONE)
- Regenerated full catalog via `generate_catalog.py` (no series filter)
- Coverage: 3.6% (40 entries) -> 100% (453 entries, pedagogical only)
- All 11 series covered with maturity labels
- 17 BROKEN notebooks identified across GenAI (5), Sudoku (4), ML (4), EPF (1), IIT (1)
- Completed by po-2025, 2026-05-08

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
