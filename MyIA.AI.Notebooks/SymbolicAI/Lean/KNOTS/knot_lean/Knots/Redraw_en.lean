/-
  English mirror of `Redraw.lean` (FR canonical, header mono-lingual EN).
  Convention EPIC #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n) :
  statements are byte-identical to the FR file, only docstrings and comments
  are translated; the `_en` namespace suffix prevents name collisions.
-/
import Knots.Basic_en
import Knots.Reidemeister_en

/-!
# PD code redraw (link 6, EPIC #2874)

A PD code is a presentation: the ORDER of the crossing list and the NAMES of
the edge labels carry no drawing information. Two diagrams differing only by
these two choices depict the same planar drawing. This module formalizes
that relation (`Redraws`) as the building block of link 6: connecting the
redraw certificate of link 5 (`conway_sphereMutate_redraws_kinoshitaTerasaka`,
Conway.lean) to the equivalence required by `AreMutants` (Mutation.lean).

The `Knot` docstring (Basic.lean) names the target equivalence — "modulo
Reidemeister moves AND planar isotopy" — and notes the latter is not yet
connected. `Redraws` is its combinatorial building block. See the FR
canonical file for the full design note (three closing routes).
-/

open Knots_en

namespace Knots_en

/-- Relabel a crossing by a function on edge labels.
Per-crossing version of `relabelCrossings` (Conway.lean, link 5). -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Redraw: `d₂` is obtained from `d₁` by a bijective relabeling of the edge
labels that exchanges the `edges` windows (hence `numEdges`), and a
permutation of the crossing list — the list of `d₂` is a permutation of the
relabeled list of `d₁`. This is the direction of the link 5 certificate:
`relabelCrossings f (ktRedrawOrder d₁.crossings) = d₂.crossings`. -/
def Redraws (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.numEdges = d₂.numEdges ∧
  ∃ e : Nat ≃ Nat,
    (∀ k ∈ d₁.edges, e k ∈ d₂.edges) ∧
    (∀ k ∈ d₂.edges, e.symm k ∈ d₁.edges) ∧
    d₂.crossings.Perm (d₁.crossings.map (PDCrossing.relabel e))

/-! ### Auxiliary lemmas: relabeling and list structure. -/

/-- Relabeling by the identity is the identity, per crossing. -/
theorem relabel_equiv_refl (c : PDCrossing) :
    PDCrossing.relabel (Equiv.refl Nat) c = c := rfl

/-- Relabeling by the identity is the identity, per list. -/
theorem map_relabel_equiv_refl (cs : List PDCrossing) :
    cs.map (PDCrossing.relabel (Equiv.refl Nat)) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => rw [List.map_cons, ih, relabel_equiv_refl]

/-- Relabeling composes like functions: `relabel g ∘ relabel f =
relabel (g ∘ f)`. This is what makes transitivity of redraw immediate. -/
theorem relabel_comp_apply (g f : Nat → Nat) (c : PDCrossing) :
    PDCrossing.relabel g (PDCrossing.relabel f c) = PDCrossing.relabel (g ∘ f) c := rfl

/-- Relabeling by the inverse bijection cancels the direct relabeling,
per crossing. -/
theorem relabel_symm_apply (e : Nat ≃ Nat) (c : PDCrossing) :
    PDCrossing.relabel e.symm (PDCrossing.relabel e c) = c := by
  simp [PDCrossing.relabel, Equiv.symm_apply_apply]

/-- The composed relabeling is written with `Equiv.trans`: `relabel e₂ ∘
relabel e₁ = relabel (e₁.trans e₂)` (the `Equiv.trans` convention applies
`e₁` then `e₂`). -/
theorem relabel_trans_eq (e₁ e₂ : Nat ≃ Nat) :
    (PDCrossing.relabel e₂) ∘ (PDCrossing.relabel e₁) = PDCrossing.relabel (e₁.trans e₂) := by
  funext c
  simp [PDCrossing.relabel, Equiv.trans_apply]

/-! ### Structure: `Redraws` is an equivalence. -/

/-- Reflexivity of redraw: identity bijection, identity permutation. -/
theorem Redraws.refl (d : KnotDiagram) : Redraws d d := by
  refine ⟨rfl, Equiv.refl Nat, fun _ hk => hk, fun _ hk => hk, ?_⟩
  rw [map_relabel_equiv_refl]

/-- Symmetry of redraw: the inverse bijection `e.symm` exchanges the
windows the other way, and the cancellation `e.symm ∘ e = id` brings the
relabeled list back to the starting list. -/
theorem Redraws.symm {d₁ d₂ : KnotDiagram} (h : Redraws d₁ d₂) : Redraws d₂ d₁ := by
  obtain ⟨hne, e, hw₁, hw₂, hperm⟩ := h
  refine ⟨hne.symm, e.symm, fun k hk => hw₂ k hk, fun k hk => hw₁ k hk, ?_⟩
  -- From hperm : d₂ ~ d₁.map (relabel e), map by (relabel e.symm):
  -- d₂.map (relabel e.symm) ~ (d₁.map (relabel e)).map (relabel e.symm)
  --   = d₁.map (relabel e.symm ∘ relabel e) = d₁.map id = d₁,
  -- then symmetry of the permutation.
  have hmap := List.Perm.map (PDCrossing.relabel e.symm) hperm
  rw [List.map_map] at hmap
  have hfn : (PDCrossing.relabel e.symm) ∘ (PDCrossing.relabel e) = id := by
    funext c
    simpa using relabel_symm_apply e c
  rw [hfn, List.map_id] at hmap
  exact hmap.symm

/-- Transitivity of redraw: the bijections compose by `Equiv.trans` (the
convention applies `e₁` then `e₂`, which is exactly the composition order
of the relabelings), and the permutations chain. -/
theorem Redraws.trans {d₁ d₂ d₃ : KnotDiagram} (h₁ : Redraws d₁ d₂) (h₂ : Redraws d₂ d₃) :
    Redraws d₁ d₃ := by
  obtain ⟨hne₁, e₁, hw₁₁, hw₁₂, hp₁⟩ := h₁
  obtain ⟨hne₂, e₂, hw₂₁, hw₂₂, hp₂⟩ := h₂
  refine ⟨hne₁.trans hne₂, e₁.trans e₂, ?_, ?_, ?_⟩
  · intro k hk
    rw [Equiv.trans_apply]
    exact hw₂₁ (e₁ k) (hw₁₁ k hk)
  · intro k hk
    rw [Equiv.symm_trans_apply]
    exact hw₁₂ (e₂.symm k) (hw₂₂ k hk)
  · -- d₃ ~ d₂.map (relabel e₂) [hp₂] and
    -- d₂.map (relabel e₂) ~ d₁.map (relabel (e₁.trans e₂)) [mapping hp₁].
    have hmap := List.Perm.map (PDCrossing.relabel e₂) hp₁
    rw [List.map_map, relabel_trans_eq] at hmap
    exact hp₂.trans hmap

end Knots_en
