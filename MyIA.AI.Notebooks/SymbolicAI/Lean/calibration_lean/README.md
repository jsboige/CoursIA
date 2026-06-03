# Calibration Lean

Prover calibration targets for benchmarking the multi-agent Lean prover.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 0 production (all 4 calibration targets proved; previous "4 sorry" claim matched docstring text inside `/-- ... -/` blocks, not actual `sorry` terms)
- **Build**: `lake build Calibration` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `Calibration/Nash.lean` | 0 | Prover calibration targets (C/D/E/F) |

## Calibration Targets

- **Target C**: Proved
- **Target D**: Proved
- **Target E**: Proved
- **Target F**: Proved (docstring of this lemma mentions the word "sorry" — previous grep scans were misled by this)

## Notes

- This module benchmarks the multi-agent Lean prover's ability to close textbook-style proofs
- All targets now closed; module is retained as a permanent regression suite for prover changes
- Verification: `grep -nE '^[^/]*\bsorry\b' Calibration/Nash.lean` returns 0 production hits (cf [LEAN_INVENTORY.md](../LEAN_INVENTORY.md))
