/-
  Definitions core — Approval core (Becker-Greger-Peters 2026)
  ============================================================

  This file lays out the basic structures and functions for the formalisation
  of the approval core, following the result by Becker, Greger and Peters
  (2026), arXiv 2609.11912.

  Tranche 1 of the execution plan for issue #17988 :
  - `ApprovalBallot`     — subset of approved candidates per voter
  - `ApprovalProfile`    — collection of ballots indexed by voters + committee size
  - `Committee`          — subset of candidates of fixed cardinality `k`
  - `Happiness`          — additive utility (cardinal of approval × committee intersection)
  - `PaymentFunction`    — payment vector to voters, zero sum
  - `ApprovalAggregateUtility` — weighted sum of individual happinesses (no logarithm)

  The `Core` definitions (Tranche 2) and the main theorem (Tranche 3) live
  in separate files `ApprovalCore.lean` (Tranche 2) and `ApprovalBGP2026.lean`
  (Tranche 3).

  i18n convention #4980: this file carries the namespace `ApprovalDefs_en`
  (EN). The sibling `ApprovalDefs.lean` carries `ApprovalDefs` (FR).
  Byte-identity preserved except docstrings — verified by
  `scripts/lean/check_i18n_siblings.py`.
-/

import SocialChoice.Profile
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice

namespace ApprovalDefs_en

/-- An approval ballot: subset of candidates approved by a voter. -/
structure ApprovalBallot (A : Type) [Fintype A] where
  approved : Finset A

/-- An approval profile: collection of ballots indexed by voters, with
    a target committee size. -/
structure ApprovalProfile (V A : Type) [Fintype V] [Fintype A] where
  ballots : V → ApprovalBallot A
  committeeSize : ℕ

/-- A committee: subset of candidates of fixed cardinality `k`. -/
def Committee (A : Type) [Fintype A] (k : ℕ) : Type :=
  { S : Finset A // S.card = k }

/-- Happiness of a voter `v` under a committee `S`: the number of candidates
    approved by `v` that lie in `S`. -/
def Happiness {V A : Type} [instV : Fintype V] [instA : Fintype A] [DecidableEq A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (v : V) : ℕ :=
  ((P.ballots v).approved).filter (fun x => x ∈ S.val) |>.card

/-- Payment function: vector of payments to voters, constrained to zero sum
    (payments transfer money to voters, financed by a total zero budget). -/
structure PaymentFunction (V : Type) [Fintype V] where
  payments : V → ℚ
  zero_sum : (∑ v, payments v) = 0

/-- Aggregate approval utility: weighted sum of individual happinesses,
    where each voter's coefficient is `1 / (1 + p.v)` (interpretation: a
    positive payment reduces the voter's weight, a negative payment raises
    it — the **base** of the BGP 2026 objective function without the
    logarithm).

    This definition serves as a **proxy** for `HarmonicEntropy` (which will
    introduce the logarithm via `Mathlib.Analysis.SpecialFunctions.Log` in
    Tranche 3). The proxy is sufficient to express the technical lemmas of
    Tranche 2 (monotonicity in committee composition) that do not depend on
    the log itself.

    No concavity is claimed in the payment dimension: for two voters with
    equal happiness and `p = (a, -a)`, the aggregate equals
    `1/(1+a) + 1/(1-a)`, i.e. 2 at `a = 0` and 8/3 at `a = ±1/2` — convex,
    not concave (counter-example measured in exact arithmetic, see review
    c.5969321192).

    The weights are strictly positive whenever `p.v > -1`. The `zero_sum`
    constraint alone does not imply it (`p = (-2, 2)` sums to zero);
    Tranche 2 will state `p.v > -1` as an explicit assumption. -/
def ApprovalAggregateUtility {V A : Type} [instV : Fintype V] [instA : Fintype A] [DecidableEq A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (p : PaymentFunction V) : ℚ :=
  ∑ v, (1 : ℚ) / (1 + p.payments v) * (Happiness P S v : ℚ)

end ApprovalDefs_en