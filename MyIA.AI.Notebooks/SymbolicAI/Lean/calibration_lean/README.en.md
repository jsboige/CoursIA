# Calibration Lean

Prover calibration targets for benchmarking the multi-agent Lean prover.

## Status

- **Toolchain**: v4.31.0-rc1
- **Sorry count**: 0 production (all 4 calibration targets proved; previous "4 sorry" claim matched docstring text inside `/-- ... -/` blocks, not actual `sorry` terms)
- **Build**: `lake build Calibration` -- SUCCESS
- **Dependencies**: Mathlib4
- **i18n coverage (EPIC #4980)**: lake fully bilingual FR/EN — 3 `.lean` modules shipped as FR canonical + 3 `*_en.lean` mirror siblings on `main` (`Calibration/Doomsday_en.lean`, `Calibration/Nash_en.lean`, `Calibration/Nim_en.lean`, added by PR #5543 step 2). Convention EPIC #4980 Option A: docstrings `/-- ... -/` and `-- ...` comments differ between FR and EN, signatures and proofs remain byte-identical.

## Modules

| File | `_en` | sorry | Description |
|------|-------|-------|-------------|
| `Calibration/Doomsday.lean` | `Doomsday_en.lean` | 0 | Doomsday algorithm (day-of-week computation, anchor calendar) |
| `Calibration/Nash.lean` | `Nash_en.lean` | 0 | Prover calibration targets on the 2×2 Prisoner's Dilemma (C/D/E/F) |
| `Calibration/Nim.lean` | `Nim_en.lean` | 0 | Nim game theory (winning-strategy Nim-sum) |

## Calibration Targets

- **Target C**: Proved
- **Target D**: Proved
- **Target E**: Proved
- **Target F**: Proved (docstring of this lemma mentions the word "sorry" — previous grep scans were misled by this)

## Notes

- This module benchmarks the multi-agent Lean prover's ability to close textbook-style proofs
- All targets now closed; module is retained as a permanent regression suite for prover changes
- Verification: `grep -nE '^[^/]*\bsorry\b' Calibration/Nash.lean` returns 0 production hits (cf [Lean README](../Lean-1-Setup.ipynb))

## Conclusion

This project is a **calibration suite** for the multi-agent Lean prover: four
textbook-style proof targets (C / D / E / F) in `Calibration/Nash.lean`, all
**proved with 0 `sorry`** (`lake build Calibration` SUCCESS, toolchain
`v4.31.0-rc1`).

### Why it exists

The targets benchmark the prover's ability to close short, self-contained
proofs end-to-end. With all four now closed, the module is retained as a
**permanent regression suite**: any prover change that breaks one of these
proofs surfaces here as a build failure.

### The grep false-positive lesson

An earlier "4 `sorry`" count was a **measurement artefact** — the word "sorry"
appeared inside `/-- ... -/` docstrings (prose), not as proof terms. A naive
`grep sorry` over-counted; the correct check
`grep -nE '^[^/]*\bsorry\b'` (excluding comments/docstrings) returns 0. The
same distinction — `sorry` the tactic vs "sorry" the word — applies across the
whole Lean series.

### Where to go next

- **Prover harness**: [`agent_tests/prover/`](../agent_tests/prover/) — the
  multi-agent prover these targets calibrate.
- **Production targets**: [`conway_lean/`](../conway_lean/),
  [`knot_lean/`](../knot_lean/) — Lean projects the prover also runs against.
