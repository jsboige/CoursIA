# scripts/validation/

Validation infrastructure for CoursIA notebook quality gates.

## matrix.yml

Per-family validation configuration for all 11 notebook series. Declares:

- **kernel**: which Jupyter kernel each family requires
- **strategy**: execution method (`papermill`, `cell-by-cell`, `cloud-only`)
- **timeout**: per-family timeout in seconds
- **prerequisites**: external deps required (Docker, API keys, WSL)
- **acceptance**: pass criteria (outputs present, zero errors)

### Usage

```bash
# Validate a specific family
python scripts/validation/dispatch.py --family Search

# Quick check (structure only, no execution)
python scripts/validation/dispatch.py --family QuantConnect --quick

# Execute and validate
python scripts/validation/dispatch.py --family GenAI --execute
```

Activation: Phase 2 (#623), post-20 mai 2026.

### Families overview

| Family | Kernel | Strategy | Key prerequisite |
|--------|--------|----------|-----------------|
| Search | python3 | papermill | none |
| Sudoku | mixed | mixed | .NET Interactive for C# |
| SymbolicAI | mixed | mixed | WSL for Lean, .NET for SemanticWeb |
| GenAI | python3 | papermill | Docker services + API keys |
| ML | mixed | mixed | .NET for ML.NET |
| QuantConnect | python3 | papermill | QC Cloud for projects |
| Probas | .net-interactive | cell-by-cell | .NET 9.0 |
| GameTheory | python-wsl | papermill | WSL + OpenSpiel |
| IIT | python3 | papermill | PyPhi |
| RL | python3 | papermill | none |

### Severity levels

| Maturity | CI behavior |
|----------|------------|
| PRODUCTION | Fail on any violation |
| BETA | Fail on any violation |
| ALPHA | Warn only |
| DRAFT | Skip |
| RESEARCH | Skip |

### Known limitations

- **.NET Interactive**: `System.Collections.Immutable 9.0` binding failure affects 16 notebooks (ML.NET, Sudoku C#, Probas)
- **Lean 4**: Requires WSL kernel, cold start ~60s
- **OpenSpiel**: Requires WSL + custom kernel, not available on all machines
- **GenAI**: Docker services must be UP; 7 notebooks need API keys (OpenAI, ComfyUI)
- **QC Cloud projects**: Cannot be validated locally (cloud-only strategy)

## Related tools

| Tool | Location | Purpose |
|------|----------|---------|
| `notebook_lint.py` | `scripts/notebook_tools/` | C.1 + C.2 + structure + metadata |
| `diagnose_broken.py` | `scripts/notebook_tools/` | Classify BROKEN notebooks by root cause |
| `check_c2_compliance.py` | `scripts/notebook_tools/` | C.2 compliance report |
| `batch_reexecute.py` | `scripts/notebook_tools/` | Batch re-execution with Papermill |
| `catalog_coverage.py` | `scripts/notebook_tools/` | Coverage report by series |
| `generate_catalog.py` | `scripts/notebook_tools/` | Generate COURSE_CATALOG.generated.json |
