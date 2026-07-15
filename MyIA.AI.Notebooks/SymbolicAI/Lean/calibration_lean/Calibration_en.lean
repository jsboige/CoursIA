/-
  Calibration targets for the multi-agent Lean prover (Epic #1452).

  Each theorem exercises a specific harness path:
  - P1: no-progress detection (stuck agents)
  - P2: distant-error diagnosis
  - P3: phantom-identifier blocklist (searches for nonexistent Mathlib lemmas)

  Target difficulty: 3-10 prover iterations (Goldilocks zone).

  i18n convention #4980 (sibling pair): this root is EN-only, the canonical
  French aggregator twin is `Calibration.lean`.
-/
import Calibration.Nash_en
import Calibration.Nim_en
import Calibration.Doomsday_en
