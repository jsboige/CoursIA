/-
Conway calibration track — Doomsday lemmas (P2: closed-eval vs. case-decomposition)
John Horton Conway (1937-2020).

English mirror of `DoomsdayLemmas.lean` (FR canonical). Convention EPIC #4980
(decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
files — no inline bilingual block in a single file (Option B rejected). The module
docstring and the public theorem docstrings below differ from the FR version; the body
signatures, proofs and tactics remain byte-identical between the two files.

These lemmas sit on top of `Conway.Doomsday` (the day-of-week algorithm). They form
a HARNESS CALIBRATION ladder for the prover co-evolution Epic (#1453):

  - `isLeapYear_2000` / `isLeapYear_1900` / `isLeapYear_2024`
        : closed boolean evaluations            -> decide / native_decide   (easy)
  - `dayOfWeek_conway_death`
        : the homage — Conway died Sat 2020-04-11; closed eval over the algorithm
        : naive `rfl` may stall on `%`-arithmetic -> decide / native_decide  (easy-med)
  - `dayOfWeek_add_seven`
        : NOT closed (free `d`); a naive `decide` fails because `d` is a variable.
          The Director must DECOMPOSE: `cases d <;> rfl`.                    (medium)

All `sorry`s have been eliminated (Epic #1453, #1651).
-/

import Conway.Doomsday

namespace Conway_en

open Conway

/-- CALIBRATION (decide): 2000 is a leap year (divisible by 400). -/
theorem isLeapYear_2000 : isLeapYear 2000 = true := by
  native_decide

/-- CALIBRATION (decide): 1900 is NOT a leap year (divisible by 100, not 400). -/
theorem isLeapYear_1900 : isLeapYear 1900 = false := by
  native_decide

/-- CALIBRATION (decide): 2024 is a leap year. -/
theorem isLeapYear_2024 : isLeapYear 2024 = true := by
  native_decide

/-- HOMAGE + CALIBRATION: John Conway passed away on Saturday, April 11, 2020.
    Closed evaluation of the Doomsday algorithm. -/
theorem dayOfWeek_conway_death : dayOfWeek 2020 4 11 = DayOfWeek.saturday := by
  native_decide

/-- CALIBRATION (case-decomposition): adding a full week is the identity.
    A naive `decide` fails (`d` is free); requires `cases d`. -/
theorem dayOfWeek_add_seven (d : DayOfWeek) : DayOfWeek.add d 7 = d := by
  cases d <;> rfl

end Conway_en
