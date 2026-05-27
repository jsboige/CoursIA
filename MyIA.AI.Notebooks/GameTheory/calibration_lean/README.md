# Calibration Lean

Prover calibration targets for benchmarking the multi-agent Lean prover.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 4 (intentional harness calibration -- NOT production code)
- **Build**: `lake build Calibration` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `Calibration/Nash.lean` | 4 | Prover calibration targets |

## Calibration Targets

- **Target C**: Proved
- **Target D**: Proved
- **Target E**: Proved
- **Target F**: Proved (includes 2 intentional sorry to test harness sorry-increase detection)

## Notes

- The 4 sorry are **intentional scaffolding** for calibrating prover harness behavior
- Used to verify that the prover correctly detects sorry count changes
- Not production formalization code -- serves as a benchmark suite
