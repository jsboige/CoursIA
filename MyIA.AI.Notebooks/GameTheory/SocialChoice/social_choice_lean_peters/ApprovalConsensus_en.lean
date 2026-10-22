/-
  Approval core — non-vacuity on consensus profiles
  =================================================

  Residue of issue #17988 raised by the coordinator on 2026-10-13: "the
  minimal proof of point 3 — characterisation by payment systems (theorem 3.3
  of the paper) OR a bounded explicit case — not delivered".

  This file delivers the second branch of that alternative, and delivers it
  more broadly than a single case: a **family** of profiles on which the core
  is non-empty, proved without `sorry`.

  ## What is proved, and what is not

  **Proved.** Two sufficient conditions, symmetric to each other:

  - if every voter approves a subset of the committee `S`, then `S` is in the
    core (`inCore_of_ballots_subset`): every voter reaches the cardinal of
    their ballot, their maximum possible value;
  - if the committee `S` is contained in every voter's ballot, then `S` is in
    the core (`inCore_of_committee_subset_ballots`): every voter gets `k`, and
    `k` is the maximum reachable by any committee of size `k`
    (`happiness_le_committeeSize`, which holds without any hypothesis).

  In both cases no coalition — not even a non-empty one — can block. The
  corollary `exists_inCore_of_common_approval` deduces core non-vacuity for
  any **consensus** profile (all voters share the same approval set `U`) as
  soon as the committee size does not exceed that of `U`.

  **Not proved, and named as such.** The existence theorem of Becker, Greger
  and Peters (2026) holds for **every** approval profile, without any
  consensus hypothesis; its constructive proof goes through a local optimum
  of a harmonic entropy over the space (committee, payment system) — Tranche
  3, out of reach for this cycle. The characterisation by payment systems
  (theorem 3.3 of the paper) is not formalised here either. This file
  therefore does **not** claim to close point 3: it supplies the bounded
  explicit case the issue allows, widened to a class of profiles.

  ## Why the case is not degenerate

  The temptation would be to take `k = |A|`, where the committee is the whole
  universe and the result holds without any hypothesis. The concrete instance
  below takes `|A| = 3` and `k = 2`: two distinct committees exist, so a
  coalition could in principle block, and it is precisely the approval
  condition contained in the committee that prevents it.

  No `sorry`, no `native_decide`.

  i18n convention #4980: this file carries the namespace `ApprovalConsensus_en`
  (EN). The sibling `ApprovalConsensus.lean` carries `ApprovalConsensus` (FR).
  Byte-identity preserved except docstrings — verified by
  `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs_en
import ApprovalCore_en
import Mathlib.Data.Finset.Card

namespace ApprovalConsensus_en

open ApprovalDefs_en ApprovalCore_en

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- A voter's happiness is bounded by the cardinal of their ballot: a
    committee cannot grant them more candidates than they approve. -/
lemma happiness_le_approved_card (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V) :
    Happiness P S v ≤ ((P.ballots v).approved).card :=
  Finset.card_filter_le _ _

/-- A voter's happiness is also bounded by the committee size: a committee
    cannot grant them more candidates than it contains. This bound holds
    **without any hypothesis**, and it is what yields the second non-vacuity
    criterion. -/
lemma happiness_le_committeeSize (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V) :
    Happiness P S v ≤ P.committeeSize := by
  have hsub : ((P.ballots v).approved.filter (fun x => x ∈ S.val)) ⊆ S.val :=
    fun x hx => (Finset.mem_filter.mp hx).2
  calc Happiness P S v
      = ((P.ballots v).approved.filter (fun x => x ∈ S.val)).card := rfl
    _ ≤ S.val.card := Finset.card_le_card hsub
    _ = P.committeeSize := S.property

/-- If the committee is contained in a voter's ballot, their happiness
    reaches the committee size: the voter approves every committee member. -/
lemma happiness_eq_committeeSize_of_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V)
    (h : S.val ⊆ (P.ballots v).approved) :
    Happiness P S v = P.committeeSize := by
  have hle : Happiness P S v ≤ P.committeeSize := happiness_le_committeeSize P S v
  have hge : P.committeeSize ≤ Happiness P S v := by
    have hsub : S.val ⊆ (P.ballots v).approved.filter (fun x => x ∈ S.val) :=
      fun x hx => Finset.mem_filter.mpr ⟨h hx, hx⟩
    calc P.committeeSize = S.val.card := S.property.symm
      _ ≤ _ := Finset.card_le_card hsub
  exact le_antisymm hle hge

/-- If a voter's ballot is contained in the committee, their happiness
    reaches the cardinal of that ballot: the filter removes nothing. -/
lemma happiness_eq_card_of_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V)
    (h : ((P.ballots v).approved) ⊆ S.val) :
    Happiness P S v = ((P.ballots v).approved).card := by
  unfold Happiness
  rw [Finset.filter_true_of_mem (fun x hx => h hx)]

/-- Sufficient condition for non-vacuity: if every voter approves a subset of
    the committee `S`, then `S` is in the core. No non-empty coalition can
    block it, since every voter already sits at the maximum happiness they can
    reach. -/
theorem inCore_of_ballots_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ v : V, ((P.ballots v).approved) ⊆ S.val) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  have hle : Happiness P S' v ≤ ((P.ballots v).approved).card :=
    happiness_le_approved_card P S' v
  have heq : Happiness P S v = ((P.ballots v).approved).card :=
    happiness_eq_card_of_subset P S v (h v)
  exact absurd (himp v hv) (not_lt.mpr (by rw [heq]; exact hle))

/-- Second non-vacuity criterion: if the committee is contained in **every**
    voter's ballot, then `S` is in the core. Every voter gets the committee
    size, which is the maximum reachable by any committee of that size
    (`happiness_le_committeeSize`). -/
theorem inCore_of_committee_subset_ballots (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ v : V, S.val ⊆ (P.ballots v).approved) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  have hle : Happiness P S' v ≤ P.committeeSize :=
    happiness_le_committeeSize P S' v
  have heq : Happiness P S v = P.committeeSize :=
    happiness_eq_committeeSize_of_subset P S v (h v)
  exact absurd (himp v hv) (not_lt.mpr (by rw [heq]; exact hle))

/-- On a **consensus** profile — all voters share the same approval set `U` —
    every committee `S` contained in `U` is in the core. -/
theorem inCore_of_common_approval (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {U : Finset A}
    (hballot : ∀ v : V, (P.ballots v).approved = U) (hsub : S.val ⊆ U) :
    InCore P S :=
  inCore_of_committee_subset_ballots P S (fun v => by rw [hballot v]; exact hsub)

/-- Core non-vacuity on a consensus profile: as soon as the committee size
    does not exceed that of the common approved set, some committee lies in
    the core. -/
theorem exists_inCore_of_common_approval (P : ApprovalProfile V A) {U : Finset A}
    (hballot : ∀ v : V, (P.ballots v).approved = U)
    (hk : P.committeeSize ≤ U.card) :
    ∃ S : Committee A P.committeeSize, InCore P S := by
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hk
  exact ⟨⟨S, hcard⟩, inCore_of_common_approval P ⟨S, hcard⟩ hballot hsub⟩

/-- Bounded explicit case: two voters, three candidates, a committee of size
    two, and both voters approve exactly `{0, 1}`. The only size-two committee
    contained in the approved set is `{0, 1}` itself; the core is therefore
    non-empty, and the consensus hypothesis is not vacuous in content since a
    second committee (`{0, 2}` or `{1, 2}`) exists and would yield strictly
    lower happiness. -/
def twoVotersThreeCandidates : ApprovalProfile (Fin 2) (Fin 3) where
  ballots := fun _ => ⟨{0, 1}⟩
  committeeSize := 2

/-- The core of the `twoVotersThreeCandidates` profile is non-empty. -/
example : ∃ S : Committee (Fin 3) 2, InCore twoVotersThreeCandidates S :=
  exists_inCore_of_common_approval (U := ({0, 1} : Finset (Fin 3)))
    twoVotersThreeCandidates (by decide) (by decide)

end ApprovalConsensus_en
