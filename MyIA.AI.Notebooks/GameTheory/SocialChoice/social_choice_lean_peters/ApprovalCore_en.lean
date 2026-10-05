/-
  Approval core — definition and identity lemmas
  ==============================================

  Tranche 2 of the execution plan for issue #17988, on top of the Tranche 1
  foundation (`ApprovalDefs.lean`). Reference result: Becker, Greger and
  Peters (2026), arXiv 2609.11912.

  The retained definition is the **standard** one for committee-election
  cores: a committee is in the core if no **non-empty** coalition of voters
  can strictly improve the outcome of **all** its members through another
  committee of the same size.

  Two points of the definition deserve reading, because they are the
  corrections applied to the initial framing sketch (NanoClaw review cid
  5327843625, cf. `docs/lean/approval-core-bgp2026-design.md` §7bis):

  1. **Non-empty coalition.** Without the `T.Nonempty` constraint, the core
     would be empty as soon as two distinct committees exist: the empty
     coalition then "improves" vacuously. The lemma
     `empty_coalition_strictlyImproves` below gives that counter-example, and
     it is the witness that the constraint is not decorative.
  2. **No payment in the blocking condition.** The `PaymentFunction`
     structure from Tranche 1 is a component of the **objective** of the
     proof (`HarmonicEntropy`, Tranche 3), not of the **definition** of the
     core. Here, "improves" is read directly off `Happiness`.

  The main theorem (the core is non-empty) and its constructive proof live in
  `ApprovalBGP2026.lean` (Tranche 3). This file only sets the definition and
  the identity lemmas — **no `sorry`**.

  Import choice: the proof requires neither a Mathlib tactic import nor any
  classical machinery. Lemmas are stated in their intuitionistically valid
  direction, and the pair
  `not_exists_improving_of_inCore` / `inCore_of_not_exists_improving` carries
  the content of the equivalence without invoking `push_neg` or `by_contra`.

  i18n convention #4980: this file carries the namespace `ApprovalCore_en`
  (EN). The sibling `ApprovalCore.lean` carries `ApprovalCore` (FR).
  Byte-identity preserved except docstrings — verified by
  `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs_en
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace ApprovalCore_en

open ApprovalDefs_en

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- A coalition `T` **strictly improves** on committee `S` when there exists
    another committee `S'` of the same size that makes **every** member of `T`
    strictly happier. -/
def StrictlyImproves (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (T : Finset V) : Prop :=
  ∃ S' : Committee A P.committeeSize, S' ≠ S ∧
    ∀ v ∈ T, Happiness P S' v > Happiness P S v

/-- A committee `S` is in the **core** when no **non-empty** coalition of
    voters can strictly improve on it. -/
def InCore (P : ApprovalProfile V A) (S : Committee A P.committeeSize) : Prop :=
  ∀ T : Finset V, T.Nonempty → ¬ StrictlyImproves P S T

/-- Identity, forward direction: a committee in the core rules out every
    improving coalition. -/
lemma not_exists_improving_of_inCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (h : InCore P S) :
    ¬ ∃ T : Finset V, T.Nonempty ∧ StrictlyImproves P S T := by
  rintro ⟨T, hT, hs⟩
  exact h T hT hs

/-- Identity, converse direction: the absence of an improving coalition is
    exactly core membership. Together with the previous lemma, both readings
    of the definition are covered without invoking classical logic. -/
lemma inCore_of_not_exists_improving (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ¬ ∃ T : Finset V, T.Nonempty ∧ StrictlyImproves P S T) : InCore P S := by
  intro T hT hs
  exact h ⟨T, hT, hs⟩

/-- An improving coalition stays improving on any sub-coalition: since strict
    improvement is required for **all** members, removing members can only
    make the condition easier. This is the monotonicity that makes the core a
    property of coalitions rather than of isolated voters. -/
lemma strictlyImproves_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {T T' : Finset V} (hsub : T ⊆ T')
    (h : StrictlyImproves P S T') : StrictlyImproves P S T := by
  obtain ⟨S', hne, himp⟩ := h
  exact ⟨S', hne, fun v hv => himp v (hsub hv)⟩

/-- The **empty** coalition "strictly improves" as soon as a committee
    distinct from `S` exists. This is the witness of correction 1 in the
    framing: without the `T.Nonempty` constraint in `InCore`, that coalition
    alone would empty the core of every committee as soon as the committee
    space has at least two elements. -/
lemma empty_coalition_strictlyImproves (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (S' : Committee A P.committeeSize)
    (hne : S' ≠ S) : StrictlyImproves P S ∅ :=
  ⟨S', hne, fun v hv => absurd hv (Finset.notMem_empty v)⟩

/-- Sufficient condition: if no committee of the same size makes a voter
    strictly happier, the committee is in the core. The statement is
    deliberately weak — it is the "unanimously maximal" case, useful as a
    non-emptiness test of the definition, and not the Becker-Greger-Peters
    result (Tranche 3). -/
lemma inCore_of_no_strict_improvement (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ (S' : Committee A P.committeeSize) (v : V),
      Happiness P S' v ≤ Happiness P S v) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  exact absurd (himp v hv) (not_lt.mpr (h S' v))

end ApprovalCore_en
