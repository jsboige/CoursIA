/-
Conway's FRACTRAN — companion lemmas
John Horton Conway (1937-2020)

These lemmas sit on top of `Conway.Fractran` (the FRACTRAN universal machine) and
form a calibration ladder over its step/run semantics, parallel to the existing
`Conway.DoomsdayLemmas` and `Conway.LookAndSayLemmas` companion files. Until now
`Fractran.lean` was the only Conway module with definitions but no companion theorems.

  - `fractranStep_empty` / `fractranRun_zero`
        : definitionally-true base cases (halt on empty program; 0-step run)   -> rfl
  - `fracMulNat_den_one`
        : a fraction num/1 is a whole multiplier, hence always applicable      -> simp + omega
  - `fracMulNat_six_halves` / `fracMulNat_seven_not_halves`
        : closed applicability checks (6 divisible by 2; 7 not)                -> decide
  - `fractranStep_single_two_to_three` / `fractranStep_single_halts_at_three`
        : the single-fraction program {3/2} sends 2 → 3, then halts at 3       -> decide
  - `fractranRun_single_trace`
        : the bounded trace 2 → 3 (halt) of {3/2}                               -> decide

All proofs discharged with no stubs. These facts are pure core Lean 4 (no Mathlib needed) — FRACTRAN's
step/run are structural recursions over Nat/List, decidable on concrete inputs.
See #2162 (Conway family).
-/

import Conway.Fractran

namespace Conway

/-- BASE (rfl): an empty FRACTRAN program halts immediately — no fraction applies. -/
theorem fractranStep_empty (n : Nat) : fractranStep [] n = none := rfl

/-- BASE (rfl): running any program for 0 steps yields just the starting value. -/
theorem fractranRun_zero (prog : List Frac) (n : Nat) : fractranRun prog n 0 = [n] := rfl

/-- STEP (simp+omega): a fraction num/1 is an integer multiplier, hence always
    applicable (`n * num` is divisible by 1 trivially). -/
theorem fracMulNat_den_one (n : Nat) (f : Frac) (h : f.den = 1) :
    fracMulNat n f = true := by
  simp [fracMulNat, h, Nat.mod_one]

/-- CALIBRATION (decide): 6 is divisible by 2, so the fraction {3/2} applies at 6. -/
theorem fracMulNat_six_halves : fracMulNat 6 (frac 3 2 (by omega)) = true := by
  decide

/-- CALIBRATION (decide): 7 is NOT divisible by 2, so {3/2} does not apply at 7. -/
theorem fracMulNat_seven_not_halves : fracMulNat 7 (frac 3 2 (by omega)) = false := by
  decide

/-- STEP (decide): the single-fraction program {3/2} sends 2 → 3 (2 · 3 / 2 = 3). -/
theorem fractranStep_single_two_to_three :
    fractranStep [frac 3 2 (by omega)] 2 = some 3 := by
  decide

/-- HALT (decide): the single-fraction program {3/2} halts at 3 (3 · 3 = 9 is not
    divisible by 2, so no fraction applies). -/
theorem fractranStep_single_halts_at_three :
    fractranStep [frac 3 2 (by omega)] 3 = none := by
  decide

/-- RUN (decide): running {3/2} from 2 for 5 steps yields the trace [2, 3]
    (2 → 3, then halt at 3). -/
theorem fractranRun_single_trace :
    fractranRun [frac 3 2 (by omega)] 2 5 = [2, 3] := by
  decide

end Conway
