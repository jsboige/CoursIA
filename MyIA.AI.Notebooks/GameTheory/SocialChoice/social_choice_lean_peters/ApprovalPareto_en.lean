/-
  Approval core — Pareto optimality
  =================================

  **Intermediate** result of Tranche 3 of the execution plan for issue #17988,
  on top of `ApprovalCore.lean` (Tranche 2). Reference result: Becker, Greger
  and Peters (2026), arXiv 2609.11912.

  The **non-vacuity** theorem for the core (the BGP 2026 one) stays in
  `ApprovalBGP2026.lean`. This file proves the **necessary condition** that
  bounds it from below, and that is demonstrable without any extra axiom:

      belonging to the core  =>  not being Pareto-dominated.

  The **mechanism** is the interesting content, and it fits in one line: a
  Pareto domination is always **witnessed by a single-voter coalition**. Let
  `v` be the voter whose outcome strictly improves; the coalition `{v}` is
  non-empty, and the strict-improvement condition holds there by construction.
  Since the core is defined against **every** non-empty coalition, it is in
  particular defined against that one.

  What the result says, and what it does not say. It says the core is contained
  in the Pareto set — a bracketing, not a characterisation, and it says
  **nothing** about non-vacuity: the statement is compatible with an empty
  core, which is precisely the case Tranche 3 must rule out. The converse is
  false in general (a Pareto-optimal committee can be blocked by a coalition
  that does not improve *everyone*'s lot), and it is not claimed here.

  Import choice: like `ApprovalCore.lean`, this file imports no Mathlib tactic
  and invokes neither `push_neg` nor `by_contra`. Statements are given in their
  intuitionistically valid direction.

  i18n convention #4980: this file carries namespace `ApprovalPareto` (FR).
  The sibling `ApprovalPareto_en.lean` carries namespace `ApprovalPareto_en`
  (EN). Byte-identity preservation outside docstrings — verified by
  `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs_en
import ApprovalCore_en
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace ApprovalPareto_en

open ApprovalDefs_en ApprovalCore_en

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- A committee `S'` **Pareto-dominates** committee `S` when `S'` does at least
    as well for **every** voter, and strictly better for at least one. Domination
    requires both: weakness alone (everyone at least as well off) is not a
    domination, it is mere equivalence — which is what
    `not_paretoDominates_self` checks. -/
def ParetoDominates (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (S' : Committee A P.committeeSize) : Prop :=
  (∀ v : V, Happiness P S v ≤ Happiness P S' v) ∧
    ∃ v : V, Happiness P S v < Happiness P S' v

/-- A committee does not dominate itself: the second component of the
    definition is a **strict** inequality, hence irreflexive. This is the
    witness that the "strictly better for at least one" clause is not
    decorative — without it the relation would be reflexive and the whole
    hierarchy would collapse (every committee would dominate all those with
    equal happiness). -/
lemma not_paretoDominates_self (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) : ¬ ParetoDominates P S S := by
  rintro ⟨_hweak, v, hv⟩
  exact absurd hv (lt_irrefl _)

/-- **The mechanism of this tranche.** A Pareto domination is always witnessed
    by a coalition of a **single** voter: the voter whose outcome strictly
    improves. The coalition `{v}` is non-empty, and strict improvement holds
    there by construction — the other members do not exist, so the universal
    quantification over `{v}` is the only point to check.

    This is what makes blocking effective: the core does not defend itself
    against large coalitions, it already defends itself against coalitions
    reduced to one voter. -/
lemma exists_singleton_strictlyImproves_of_paretoDominates
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    {S' : Committee A P.committeeSize} (h : ParetoDominates P S S') :
    ∃ v : V, StrictlyImproves P S ({v} : Finset V) := by
  obtain ⟨_hweak, v, hv⟩ := h
  have hne : S' ≠ S := fun hEq => by
    rw [hEq] at hv
    exact absurd hv (lt_irrefl _)
  exact ⟨v, S', hne, fun w hw => by
    obtain rfl := Finset.mem_singleton.mp hw
    exact hv⟩

/-- **Main result.** A committee in the core is not Pareto-dominated by any
    committee of the same size.

    A bracketing, not a characterisation: the converse is false in general (a
    Pareto-optimal committee can be blocked by a coalition that does not improve
    all its members), and the statement is silent on the core's non-vacuity — it
    is compatible with an empty core, a case Tranche 3 rules out. -/
theorem not_paretoDominated_of_inCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (h : InCore P S) :
    ¬ ∃ S' : Committee A P.committeeSize, ParetoDominates P S S' := by
  rintro ⟨S', hpd⟩
  obtain ⟨v, hv⟩ := exists_singleton_strictlyImproves_of_paretoDominates P S hpd
  exact h ({v} : Finset V) ⟨v, Finset.mem_singleton.mpr rfl⟩ hv

/-- Contrapositive form, the one used to **exclude** a committee from the core:
    exhibiting a single Pareto domination suffices. This is the form usable on
    the application side — one never has to enumerate all coalitions to show a
    committee is not in the core, one domination suffices. -/
theorem not_inCore_of_paretoDominates (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {S' : Committee A P.committeeSize}
    (h : ParetoDominates P S S') : ¬ InCore P S :=
  fun hc => not_paretoDominated_of_inCore P S hc ⟨S', h⟩

end ApprovalPareto_en
