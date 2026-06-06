/-
  Calibration targets for the multi-agent Lean prover (Epic #1452).

  Each theorem exercises a specific harness path:
  - P1: no-progress detection (stuck agents)
  - P2: distant-error diagnosis
  - P3: phantom-identifier blocklist (searches for nonexistent Mathlib lemmas)

  Target difficulty: 3-10 prover iterations (Goldilocks zone).
-/
import Calibration.Nash
