/-
  Stable Marriage Theory Library
  ===============================

  Lean 4 formalization of the Gale-Shapley Stable Marriage Theorem.

  The Stable Marriage Problem: given n men and n women, each with a strict
  preference ordering over the opposite set, find a perfect matching where
  no unmatched pair (m, w) would both prefer each other to their current
  partners (no "blocking pair").

  Main result: Gale-Shapley (1962) algorithm always produces a stable matching.
  The "proposing side" gets their best achievable partner (optimal for proposers).

  Definitions.lean: types for men/women, preference profiles, matchings, stability
  GaleShapley.lean: algorithm and stability proof (scaffold)

  Reference: Gale & Shapley, "College Admissions and the Stability of Marriage"
  (American Mathematical Monthly, 1962)

  Reference port: https://github.com/mmaaz-git/stable-marriage-lean
-/

import StableMarriage.Definitions
import StableMarriage.GaleShapley
import StableMarriage.Lemmas
import StableMarriage.Lattice
