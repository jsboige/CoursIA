/-
  Knots — root of the `knot_lean` sub-lake (EN sibling)
  ====================================================

  * Root of the `knot_lean` sub-lake (`namespace Knots`), English
    sibling of `Knots.lean` per the i18n convention #4980 (sibling
    pair: this file is the canonical EN twin, aggregated via
    `globs := #[.submodules `Knots, `Knots_en]` in `lakefile.lean`).

  * Target EPIC #2874 (Phase 1) — formalisation of knot theory in
    Lean 4 / Mathlib 4, bricks:
    - `Knots.Basic` — combinatorial foundations (crossings,
      diagrams, PD-codes, Gauss codes, Dowker-Thistlethwaite notation)
    - `Knots.Reidemeister` — Reidemeister moves (RI, RII, RIII) and
      invariance of the polynomial / combinatorial invariants
    - `Knots.Invariant` — polynomial invariants (Alexander, Jones),
      tricolourability, genus
    - `Knots.Conway` — Conway notations and conventions
    - `Knots.Lidman` — external collaboration layer (Joshua Lidman),
      orientation of knot varieties
    - `Knots.MathlibPrerequisites` — Mathlib 4 compatibility shim

  * Inspired by `shua/leanknot` (https://github.com/shua/leanknot)
    and Prathamesh (2015), *Formalising Knot Theory in Isabelle/HOL*.

  * Convention: `namespace Knots`, proofs and theorem statements in
    English (Mathlib 4 / tactic DSL compatibility); this `_en` mirror
    carries the English documentation strings and prose comments
    (cf #4980 ratified 2026-07-04).
-/

import Knots.Basic_en
import Knots.Reidemeister_en
import Knots.Invariant_en
import Knots.Conway_en
import Knots.Lidman_en
import Knots.MathlibPrerequisites_en
