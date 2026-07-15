/-
  Conway — root of the `conway_lean` sub-lake (EN sibling)
  ========================================================

  * Root of the `conway_lean` sub-lake (`namespace Conway`), English
    sibling of `Conway.lean` per the i18n convention EPIC #4980 (sibling
    pair: this file is the canonical EN twin, aggregated via
    `globs := #[.submodules `Conway, `Conway_en]` in `lakefile.lean`).

  * Tribute to John Horton Conway (1937-2020), accessible formalizations
    of lesser-known results:
    - `Conway.Doomsday` + `Conway.DoomsdayLemmas` — Doomsday algorithm
      (1973 *Tomorrow is the Day After Doomsday*) for mental day-of-week
      calculation on any Gregorian calendar date.
    - `Conway.LookAndSay` + `Conway.LookAndSayLemmas` — audioactive
      decay (1986 *The Weird and Wonderful Chemistry of Audioactive
      Decay*), Conway sequence (1, 11, 21, 1211, 111221, 312211, ...).
    - `Conway.Fractran` + `Conway.FractranLemmas` — FRACTRAN universal
      machine (1987 *FRACTRAN: A Simple Universal Programming Language
      for Arithmetic*); any Turing machine encoded as a list of
      fractions, execution by repeated multiplication.
    - `Conway.Nim` — Nim (impartial combinatorial game), Sprague-Grundy
      theorem (1935 / 1946): every position has an integer Grundy value,
      winning strategy is deterministic.
    - `Conway.Life` (+ 12 Life sub-modules) — Conway's Game of Life
      (1970 *The Game of Life*, Scientific American, M. Gardner); fast
      Hashlife computation (Gosper 1984); correctness proof
      `HashlifeCorrectness`, complexity bounds (`HashlifeMarginDemo`,
      `LightCone`, `Pillars`).
    - `Conway.KochenSpecker` + `Conway.FreeWillTheorem` — Kochen-Specker
      theorem (1967) and Conway-Kochen Free Will Theorem (2006 *The
      Free Will Theorem*): non-contextuality and determinism in quantum
      mechanics.
    - `Conway.CollatzLike` — Collatz-type generalizations (3n+1),
      Syracuse conjecture reformalized in Lean.
    - `Conway.Angel` — Conway's Angel problem (1996 / 2002 *Angel
      Problem*, solved 2006 by Máthé, completed 2017 by Bowditch).
    - `Conway.MathlibMap` — correspondence table between the formalized
      concepts and the underlying Mathlib 4 modules.

  * Calibration track (Epic #1453): Nim/Sprague-Grundy +
    Doomsday/LookAnd-Say lemmas as a prover-harness difficulty gradient
    (intentional `sorry` as a calibration scale; see also
    `Conway.DoomsdayLemmas` and `Conway.LookAndSayLemmas`).

  * Convention: `namespace Conway`, proofs and theorem statements in
    English (Mathlib 4 / tactic DSL compatibility); this `_en` mirror
    carries the English documentation strings and prose comments
    (cf EPIC #4980 ratified 2026-07-04).
-/

import Conway.Doomsday_en
import Conway.LookAndSay_en
import Conway.Fractran_en
import Conway.Nim_en
import Conway.DoomsdayLemmas_en
import Conway.LookAndSayLemmas_en
import Conway.Angel_en
import Conway.Life_en
import Conway.KochenSpecker_en
import Conway.FreeWillTheorem_en
import Conway.MathlibMap_en
import Conway.CollatzLike_en
import Conway.FractranLemmas_en
