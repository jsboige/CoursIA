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
    - `Knots.ReidemeisterMoves` — kernel-verifiable sequences of moves
      (organ #18611: data inductive + Bool verifiers + soundness into
      `ReidemeisterEquiv`)
    - `Knots.Invariant` — polynomial invariants (Alexander, Jones),
      tricolourability, genus
    - `Knots.Conway` — Conway notations and conventions
    - `Knots.Slice` — slice knots, Piccirillo and Freedman theorems,
      smooth/topological dichotomy (extracted from Conway, #18397)
    - `Knots.Jones` — Kauffman bracket on PD codes (state sum,
      trefoil / figure eight / unknot evaluations)
    - `Knots.FigureEight` — invariants of the figure-eight knot on its
      planar PD code (signed Alexander classical up to a unit, determinant
      5, non-tricolorability, 4 crossings — provisional definition)
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
import Knots.Mutation_en
import Knots.ConwayPD_en
import Knots.Conway_en
import Knots.Slice_en
import Knots.ReidemeisterInvariance_en
import Knots.ReidemeisterMoves_en
import Knots.Jones_en
import Knots.FigureEight_en
import Knots.Lidman_en
import Knots.MathlibPrerequisites_en
