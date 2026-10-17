/-
  English mirror of `Redraw.lean` (FR canonical, header mono-lingual EN).
  Convention EPIC #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n) :
  statements are byte-identical to the FR file, only docstrings and comments
  are translated; the `_en` namespace suffix prevents name collisions.
-/
import Knots.Basic_en
import Knots.Reidemeister_en
import Knots.Conway_en
import Mathlib.Logic.Relation

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
connected. `Redraws` is its combinatorial building block, and `SameKnot`
(transitive closure of a redraw or Reidemeister step — route 3, the one
retained by the coordinator arbitration) composes both into the link 6
assembly. See the FR canonical file for the full design note.
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
labels that exchanges the `edges` windows (hence `numEdges`), preserves the
label window `[1, numEdges]` in both directions, and a permutation of the
crossing list. This is the direction of the link 5 certificate:
`relabelCrossings f (ktRedrawOrder d₁.crossings) = d₂.crossings`.

Slice 4: the two window clauses `1 ≤ k ≤ numEdges → 1 ≤ e k ≤ numEdges` (and
the symmetric one) are required for the `wf` transfer — without them it is
false (counterexample: `d₁` a single well-formed crossing, `e = swap(2,5)`,
`d₂ = [⟨1,5,1,5⟩]`: the four v2 clauses hold, `d₂.wf = false`). -/
def Redraws (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.numEdges = d₂.numEdges ∧
  ∃ e : Nat ≃ Nat,
    (∀ k ∈ d₁.edges, e k ∈ d₂.edges) ∧
    (∀ k ∈ d₂.edges, e.symm k ∈ d₁.edges) ∧
    (∀ k, 1 ≤ k → k ≤ d₁.numEdges → 1 ≤ e k ∧ e k ≤ d₂.numEdges) ∧
    (∀ k, 1 ≤ k → k ≤ d₂.numEdges → 1 ≤ e.symm k ∧ e.symm k ≤ d₁.numEdges) ∧
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
  refine ⟨rfl, Equiv.refl Nat, fun _ hk => hk, fun _ hk => hk,
    fun _ h1 h2 => ⟨h1, h2⟩, fun _ h1 h2 => ⟨h1, h2⟩, ?_⟩
  rw [map_relabel_equiv_refl]

/-- Symmetry of redraw: the inverse bijection `e.symm` exchanges the
windows the other way, and the cancellation `e.symm ∘ e = id` brings the
relabeled list back to the starting list. -/
theorem Redraws.symm {d₁ d₂ : KnotDiagram} (h : Redraws d₁ d₂) : Redraws d₂ d₁ := by
  obtain ⟨hne, e, hw₁, hw₂, hw₃, hw₄, hperm⟩ := h
  refine ⟨hne.symm, e.symm, fun k hk => hw₂ k hk, fun k hk => hw₁ k hk,
    fun k h1 h2 => hw₄ k h1 h2, fun k h1 h2 => hw₃ k h1 h2, ?_⟩
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
  obtain ⟨hne₁, e₁, hw₁₁, hw₁₂, hw₃₁, hw₄₁, hp₁⟩ := h₁
  obtain ⟨hne₂, e₂, hw₂₁, hw₂₂, hw₃₂, hw₄₂, hp₂⟩ := h₂
  refine ⟨hne₁.trans hne₂, e₁.trans e₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Equiv.trans_apply]
    exact hw₂₁ (e₁ k) (hw₁₁ k hk)
  · intro k hk
    rw [Equiv.symm_trans_apply]
    exact hw₁₂ (e₂.symm k) (hw₂₂ k hk)
  · intro k h1 h2
    rw [Equiv.trans_apply]
    obtain ⟨ha, hb⟩ := hw₃₁ k h1 h2
    exact hw₃₂ (e₁ k) ha hb
  · intro k h1 h2
    rw [Equiv.symm_trans_apply]
    obtain ⟨ha, hb⟩ := hw₄₂ k h1 h2
    exact hw₄₁ (e₂.symm k) ha hb
  · -- d₃ ~ d₂.map (relabel e₂) [hp₂] and
    -- d₂.map (relabel e₂) ~ d₁.map (relabel (e₁.trans e₂)) [mapping hp₁].
    have hmap := List.Perm.map (PDCrossing.relabel e₂) hp₁
    rw [List.map_map, relabel_trans_eq] at hmap
    exact hp₂.trans hmap

/-! ### Bridge from the link-5 certificate (Conway mutant → KT census). -/

/-- The link-5 relabeling is the identity outside the window `[0, 22)`:
the ten permuted labels (9↔10, 14↔21, 15↔20, 16↔19, 17↔18) all live
there. -/
theorem ktRedrawRelabel_eq_self {n : Nat} (h : 22 ≤ n) : ktRedrawRelabel n = n := by
  simp only [ktRedrawRelabel]
  rw [if_neg (by omega : ¬ (n = 9)), if_neg (by omega : ¬ (n = 10)),
      if_neg (by omega : ¬ (n = 14)), if_neg (by omega : ¬ (n = 21)),
      if_neg (by omega : ¬ (n = 15)), if_neg (by omega : ¬ (n = 20)),
      if_neg (by omega : ¬ (n = 16)), if_neg (by omega : ¬ (n = 19)),
      if_neg (by omega : ¬ (n = 17)), if_neg (by omega : ¬ (n = 18))]

/-- Five label transpositions: the link-5 relabeling is an involution of
`Nat`. -/
theorem ktRedrawRelabel_involutive (n : Nat) :
    ktRedrawRelabel (ktRedrawRelabel n) = n := by
  by_cases h : n < 22
  · interval_cases n
    all_goals decide
  · have h1 : ktRedrawRelabel n = n := ktRedrawRelabel_eq_self (by omega)
    rw [h1, h1]

/-- The link-5 relabeling preserves the label window `[1, 22]`. -/
theorem ktRedrawRelabel_window {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 22) :
    1 ≤ ktRedrawRelabel k ∧ ktRedrawRelabel k ≤ 22 := by
  interval_cases k
  all_goals decide

/-- The link-5 involution, viewed as an equivalence of `Nat`: this is the
relabeling witness of the `Redraws` bridge. The involution serves as both
forward and backward map (`Equiv.ofInvolutive` does not exist in Mathlib
4.33: the two components are given explicitly). -/
def ktRedrawEquiv : Nat ≃ Nat where
  toFun := ktRedrawRelabel
  invFun := ktRedrawRelabel
  left_inv := ktRedrawRelabel_involutive
  right_inv := ktRedrawRelabel_involutive

/-- The equivalence applies as the link-5 function. -/
theorem ktRedrawEquiv_apply (n : Nat) : ktRedrawEquiv n = ktRedrawRelabel n := rfl

/-- So does its symmetric (it is an involution). -/
theorem ktRedrawEquiv_symm_apply (n : Nat) : ktRedrawEquiv.symm n = ktRedrawRelabel n := rfl

/-- Relabeling by the link-5 equivalence is the link-5 relabeling, per
crossing — the two functions are definitionally equal. -/
theorem relabel_ktRedrawEquiv (c : PDCrossing) :
    PDCrossing.relabel (⇑ktRedrawEquiv) c = PDCrossing.relabel ktRedrawRelabel c := rfl

/-- List version of the previous lemma: aligns the coercion `⇑ktRedrawEquiv`
with the link-5 function inside a `map`. -/
theorem map_relabel_ktRedrawEquiv (cs : List PDCrossing) :
    cs.map (PDCrossing.relabel ⇑ktRedrawEquiv)
      = cs.map (PDCrossing.relabel ktRedrawRelabel) := by
  induction cs with
  | nil => rfl
  | cons c rest ih => rw [List.map_cons, List.map_cons, ih, relabel_ktRedrawEquiv]

/-- `relabelCrossings` (link 5, Conway.lean) is the `map` of the
per-crossing relabeling of this module. -/
theorem relabelCrossings_eq (f : Nat → Nat) (cs : List PDCrossing) :
    relabelCrossings f cs = cs.map (PDCrossing.relabel f) := rfl

/-- The link-5 reordering is a permutation: two position transpositions
(5↔7) and (8↔10) on the eleven-crossing list, identity elsewhere. Lists of
length ≤ 10 or ≥ 12 fall back to the identity clause of the reordering
(definitional reduction by shape discrimination), hence the mechanical
`refl` branches. -/
theorem ktRedrawOrder_perm : ∀ cs : List PDCrossing, (ktRedrawOrder cs).Perm cs
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] => by
      have hA : ([c7, c6, c5] : List PDCrossing).Perm [c5, c6, c7] := by
        simpa using List.reverse_perm [c5, c6, c7]
      have hB : ([c10, c9, c8] : List PDCrossing).Perm [c8, c9, c10] := by
        simpa using List.reverse_perm [c8, c9, c10]
      show ([c0, c1, c2, c3, c4] ++ [c7, c6, c5] ++ [c10, c9, c8] : List PDCrossing).Perm
          ([c0, c1, c2, c3, c4] ++ [c5, c6, c7] ++ [c8, c9, c10])
      exact ((hA.append_right [c10, c9, c8]).trans
        (hB.append_left [c5, c6, c7])).append_left [c0, c1, c2, c3, c4]
  | [] => List.Perm.refl []
  | [_] => List.Perm.refl _
  | [_, _] => List.Perm.refl _
  | [_, _, _] => List.Perm.refl _
  | [_, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _, _, _, _, _] => List.Perm.refl _
  | [_, _, _, _, _, _, _, _, _, _] => List.Perm.refl _
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => List.Perm.refl _

/-- The label window follows the relabeling: the image of a label used by
a crossing of `cs` is used by the relabeled crossing. -/
theorem mem_edges_map_relabel {cs : List PDCrossing} {f : Nat → Nat} {k : Nat}
    (hk : k ∈ cs.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])) :
    f k ∈ (cs.map (PDCrossing.relabel f)).flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]) := by
  obtain ⟨c, hc, hke⟩ := List.mem_flatMap.mp hk
  refine List.mem_flatMap.mpr ⟨PDCrossing.relabel f c,
    List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hke
  rcases hke with h | h | h | h <;> simp [PDCrossing.relabel, h]

/-- The `edges` list of `d₂` is a permutation of the `map e` of that of `d₁`. -/
theorem edges_perm_map {d₁ d₂ : KnotDiagram} {e : Nat ≃ Nat}
    (hperm : d₂.crossings.Perm (d₁.crossings.map (PDCrossing.relabel e))) :
    d₂.edges.Perm (d₁.edges.map e) := by
  have h1 : d₂.edges.Perm ((d₁.crossings.map (PDCrossing.relabel e)).flatMap
      (fun c => [c.e1, c.e2, c.e3, c.e4])) :=
    hperm.flatMap_right _
  have h2 : (d₁.crossings.map (PDCrossing.relabel e)).flatMap
      (fun c => [c.e1, c.e2, c.e3, c.e4]) =
      (d₁.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])).map e := by
    induction d₁.crossings with
    | nil => rfl
    | cons c rest ih =>
        simp only [List.map_cons, List.flatMap_cons, List.map_append,
          PDCrossing.relabel]
        exact congrArg (List.append _) ih
  simp only [KnotDiagram.edges] at h1 ⊢
  rw [← h2]
  exact h1

/-- Counting after a bijective relabeling: the count of `a` in `map e l` is
the count of `e.symm a` in `l`. -/
theorem count_map_equiv {l : List Nat} {e : Nat ≃ Nat} {a : Nat} :
    (l.map e).count a = l.count (e.symm a) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : e x = a
      · subst h
        rw [Equiv.symm_apply_apply e x] at ih ⊢
        simp only [List.map_cons, List.count_cons]
        rw [if_pos (beq_self_eq_true (e x)), if_pos (beq_self_eq_true x)]
        omega
      · have hs : e.symm a ≠ x := by
          intro hxa
          apply h
          rw [← hxa, Equiv.apply_symm_apply]
        have h1 : ¬ ((e x == a) = true) := fun he => h (beq_iff_eq.mp he)
        have h2 : ¬ ((x == e.symm a) = true) := fun he => hs (beq_iff_eq.mp he).symm
        simp only [List.map_cons, List.count_cons]
        rw [if_neg h1, if_neg h2]
        omega

/-- **Bridge link 5 → link 6**: the KT census redraw certificate — the
Conway mutant is reordered (`ktRedrawOrder`) then relabeled
(`ktRedrawRelabel`) into the Kinoshita-Terasaka census — yields a `Redraws`
witness. The relation of this module captures exactly the gesture of the
certificate committed at link 5; the final assembly (closing `AreMutants`)
awaits the route choice. -/
theorem conwayMutant_redraws_kt :
    Redraws conwayMutantDiagram kinoshitaTerasakaDiagram := by
  have hcross : kinoshitaTerasakaDiagram.crossings =
      (ktRedrawOrder conwayMutantDiagram.crossings).map
        (PDCrossing.relabel ktRedrawRelabel) :=
    (conwayMutant_redraws_kinoshitaTerasaka).symm.trans (relabelCrossings_eq _ _)
  refine ⟨rfl, ktRedrawEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [KnotDiagram.edges, ktRedrawEquiv_apply] at hk ⊢
    rw [hcross]
    exact mem_edges_map_relabel
      (((ktRedrawOrder_perm _).flatMap_right _).symm.mem_iff.mpr hk)
  · intro k hk
    simp only [KnotDiagram.edges, ktRedrawEquiv_symm_apply] at hk ⊢
    rw [hcross] at hk
    obtain ⟨c', hc', hke⟩ := List.mem_flatMap.mp hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hke
    rcases hke with h | h | h | h <;> subst h <;>
      simp only [PDCrossing.relabel] <;> rw [ktRedrawRelabel_involutive] <;>
      exact List.mem_flatMap.mpr ⟨c, (ktRedrawOrder_perm _).mem_iff.mp hc, by simp⟩
  · intro k h1 h2
    exact ktRedrawRelabel_window h1 h2
  · intro k h1 h2
    exact ktRedrawRelabel_window h1 h2
  · rw [hcross, map_relabel_ktRedrawEquiv]
    exact List.Perm.map _ (ktRedrawOrder_perm _)

/-- Redraw preserves well-formedness: the label windows of the definition
transport clause (a) of the `wf` predicate (every used label lies in
`[1, numEdges]`), bijectivity transports the parity clause (b) (every label
of `[1, numEdges]` occurs exactly twice). -/
theorem Redraws.wf {d₁ d₂ : KnotDiagram} (h : Redraws d₁ d₂) (hwf : d₁.wf = true) :
    d₂.wf = true := by
  obtain ⟨hne, e, hw₁, hw₂, hw₃, hw₄, hperm⟩ := h
  have hedges := edges_perm_map hperm
  by_cases hnil : d₂.crossings = []
  · simp only [KnotDiagram.wf, if_pos hnil]
    have h1nil : d₁.crossings = [] := by
      have hlen := hperm.length_eq
      rw [hnil] at hlen
      simp at hlen
      exact List.length_eq_zero_iff.mp hlen.symm
    simp only [KnotDiagram.wf, if_pos h1nil] at hwf
    rw [hne] at hwf
    exact hwf
  · simp only [KnotDiagram.wf, if_neg hnil]
    have hd₁ : d₁.crossings ≠ [] := by
      intro hc
      rw [hc, List.map_nil] at hperm
      exact hnil (List.Perm.eq_nil hperm)
    simp only [KnotDiagram.wf, if_neg hd₁] at hwf
    rw [Bool.and_eq_true] at hwf ⊢
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro l hl
      have hl' : l ∈ d₁.edges.map e := hedges.mem_iff.mp hl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl'
      have hka := (List.all_eq_true.mp hwf.1) k hk
      rw [decide_eq_true_iff] at hka
      exact decide_eq_true_iff.mpr (hw₃ k hka.1 hka.2)
    · rw [List.all_eq_true]
      intro i himem
      have hi : i < d₂.numEdges := List.mem_range.mp himem
      have hc : d₂.edges.count (i + 1) = d₁.edges.count (e.symm (i + 1)) := by
        rw [hedges.count_eq, count_map_equiv]
      have hw := hw₄ (i + 1) (by omega) (by omega)
      have hb := (List.all_eq_true.mp hwf.2) (e.symm (i + 1) - 1)
        (List.mem_range.mpr (by omega))
      rw [show (e.symm (i + 1) - 1) + 1 = e.symm (i + 1) from by omega] at hb
      rw [decide_eq_true_iff] at hb
      rw [hc]
      exact decide_eq_true_iff.mpr hb

/-! ### Composed equivalence: `SameKnot` (route 3, arbitration recorded) -/

/-- Two diagrams depict the same knot when they connect through a chain of
`Redraws` or `ReidemeisterEquiv` steps: the transitive closure of the
composed step. This is the formal incarnation of the `Knot` docstring's
"modulo Reidemeister moves AND planar isotopy" (Basic.lean) — the redraw is
its combinatorial building block, Reidemeister moves its surgery.

Retained form (route 3, ai-01 arbitration 2026-10-16): `Relation.EqvGen` over the
step `Redraws ∨ ReidemeisterEquiv`. The short form
`∃ m₁ m₂, Redraws d₁ m₁ ∧ Redraws d₂ m₂ ∧ ReidemeisterEquiv m₁ m₂` (initial
sketch of the design note) is reflexive and symmetric but NOT transitive —
each application consumes one `ReidemeisterEquiv` segment, and gluing two
segments would require `Redraws → ReidemeisterEquiv` (route 1). The
transitive closure is the faithful implementation of a "composed
equivalence"; the constructor `SameKnot.of_redraws_reidemeister` embeds the
short form as a sufficient certificate. -/
def SameKnot (d₁ d₂ : KnotDiagram) : Prop :=
  Relation.EqvGen (fun a b => Redraws a b ∨ ReidemeisterEquiv a b) d₁ d₂

theorem SameKnot.refl (d : KnotDiagram) : SameKnot d d :=
  Relation.EqvGen.refl d

theorem SameKnot.symm {d₁ d₂ : KnotDiagram} (h : SameKnot d₁ d₂) : SameKnot d₂ d₁ :=
  Relation.EqvGen.symm d₁ d₂ h

theorem SameKnot.trans {d₁ d₂ d₃ : KnotDiagram} (h₁ : SameKnot d₁ d₂)
    (h₂ : SameKnot d₂ d₃) : SameKnot d₁ d₃ :=
  Relation.EqvGen.trans d₁ d₂ d₃ h₁ h₂

/-- `SameKnot` is an equivalence relation (packaging of the `Relation.EqvGen`
constructors). -/
theorem sameKnot_equivalence : Equivalence SameKnot where
  refl := SameKnot.refl
  symm := SameKnot.symm
  trans := SameKnot.trans

/-- A redraw fixes the same knot: it is a one-step move of the closure. -/
theorem Redraws.sameKnot {d₁ d₂ : KnotDiagram} (h : Redraws d₁ d₂) : SameKnot d₁ d₂ :=
  Relation.EqvGen.rel d₁ d₂ (Or.inl h)

/-- A Reidemeister equivalence fixes the same knot: it is a one-step move
of the closure. -/
theorem ReidemeisterEquiv.sameKnot {d₁ d₂ : KnotDiagram} (h : ReidemeisterEquiv d₁ d₂) :
    SameKnot d₁ d₂ :=
  Relation.EqvGen.rel d₁ d₂ (Or.inr h)

/-- The short form of the design note as a sufficient certificate:
redraw-accessible representatives on each side, linked by
`ReidemeisterEquiv`. -/
theorem SameKnot.of_redraws_reidemeister {d₁ d₂ m₁ m₂ : KnotDiagram}
    (hr₁ : Redraws d₁ m₁) (hr₂ : Redraws d₂ m₂) (hre : ReidemeisterEquiv m₁ m₂) :
    SameKnot d₁ d₂ :=
  Relation.EqvGen.trans d₁ m₁ d₂ (Relation.EqvGen.rel d₁ m₁ (Or.inl hr₁))
    (Relation.EqvGen.trans m₁ m₂ d₂ (Relation.EqvGen.rel m₁ m₂ (Or.inr hre))
      (Relation.EqvGen.symm d₂ m₂ (Relation.EqvGen.rel d₂ m₂ (Or.inl hr₂))))

/-- **Link 6 assembly (route 3)**: the Conway sphere mutant and the
Kinoshita-Terasaka census depict the same knot in the composed sense. The
link 5 bridge (`conwayMutant_redraws_kt`, the link 5 `rfl` certificate
reinterpreted) is a one-step move of the closure. `AreMutants`
(Mutation.lean) is left untouched: closing
`AreMutants conwayKnot kinoshitaTerasakaKnot` in the strict sense remains
to be pursued through the route 1 congruence. -/
theorem conwayMutant_sameKnot_kt :
    SameKnot conwayMutantDiagram kinoshitaTerasakaDiagram :=
  conwayMutant_redraws_kt.sameKnot

end Knots_en
