import Mathlib

/-!
# Planning.Strips — the STRIPS model: fluents, states, actions, transitions

**STRIPS** (STanford Research Institute Problem Solver) is the canonical formalism of
classical planning. We model:

- a **fluent** (atomic fact) `F` as an arbitrary type (with decidable equality,
  for set-theoretic operations);
- a **state** `s : Finset F` as the set of currently-true fluents;
- a STRIPS **action** `a = (pre, add, del)`:
  - `pre a`: preconditions (required fluents),
  - `add a`: add effects (fluents becoming true),
  - `del a`: delete effects (fluents becoming false).

An action `a` is **applicable** in state `s` when `pre a ⊆ s`. The **real
transition** applies both add and del: `step a s = (s \ del a) ∪ add a`. The
**relaxed transition** (delete-free, the heart of h⁺) ignores deletions:
`stepR a s = s ∪ add a`.

This relaxation makes reachability **monotone**: the relaxed state only grows,
which makes computing the relaxed plan polynomial and guarantees the
**admissibility** h⁺ ≤ h* (proved in `Admissibility.lean`). See issue #4053.
-/

namespace PlanningLean_en

/-- A STRIPS **state** = the set of fluents currently true. -/
abbrev State (F : Type) := Finset F

/-- A STRIPS **action**: preconditions, add effects, delete effects. -/
structure Action (F : Type) where
  /-- Preconditions: fluents required for the action to be applicable. -/
  pre : Finset F
  /-- Add effects: fluents becoming true after the action. -/
  add : Finset F
  /-- Delete effects: fluents becoming false after the action (ignored by the relaxation). -/
  del : Finset F

variable {F : Type} [DecidableEq F]

/-- An action is **applicable** in `s` when its preconditions are satisfied. -/
def applicable (a : Action F) (s : State F) : Prop := a.pre ⊆ s

/-- The **real transition**: remove the deletions then add the adds.
    `step a s = (s \ a.del) ∪ a.add`. -/
def step (a : Action F) (s : State F) : State F := (s \ a.del) ∪ a.add

/-- The **relaxed transition** (delete-free): ignore the deletions.
    `stepR a s = s ∪ a.add`. This is the heart of the h⁺ relaxation. -/
def stepR (a : Action F) (s : State F) : State F := s ∪ a.add

/-- The goal `g` is **satisfied** by state `s` when every goal fluent is present. -/
def goalSatisfied (g s : State F) : Prop := g ⊆ s

/-- Key lemma: the real transition is included in the relaxed transition.
    `step a s ⊆ stepR a s` because `s \ a.del ⊆ s`. -/
lemma step_subset_stepR (a : Action F) (s : State F) : step a s ⊆ stepR a s := by
  rw [Finset.subset_iff]
  intro x hx
  unfold step at hx
  unfold stepR
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h

/-- The real transition is **monotone** in the state: `s ⊆ s'` entails `step a s ⊆ step a s'`. -/
lemma step_mono (a : Action F) {s s' : State F} (h : s ⊆ s') : step a s ⊆ step a s' := by
  rw [Finset.subset_iff]
  intro x hx
  unfold step at hx ⊢
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  rcases hx with hs | ha
  · exact Or.inl ⟨h hs.1, hs.2⟩
  · exact Or.inr ha

/-- The relaxed transition is **monotone** in the state: `s ⊆ s'` entails `stepR a s ⊆ stepR a s'`. -/
lemma stepR_mono (a : Action F) {s s' : State F} (h : s ⊆ s') : stepR a s ⊆ stepR a s' := by
  rw [Finset.subset_iff]
  intro x hx
  unfold stepR at hx ⊢
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with hs | ha
  · exact Or.inl (h hs)
  · exact Or.inr ha

end PlanningLean_en
