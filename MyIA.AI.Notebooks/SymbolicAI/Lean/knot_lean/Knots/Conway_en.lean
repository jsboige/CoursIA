/-
  Knots.Conway — Nœud de Conway, Kinoshita-Terasaka, et preuve de Piccirillo
  =======================================================================

  Le nœud de Conway (11n34) est nommé d'après John Conway qui l'a découvert
  via sa notation pour les nœuds. Il a 11 croisements et un polynôme
  d'Alexander trivial.

  Résultats clés :
  1. Conway (11n34) et Kinoshita-Terasaka (11n42) partagent le même
     polynôme d'Alexander (trivial) — les invariants de mutation coïncident.
  2. Le nœud de Kinoshita-Terasaka EST slice.
  3. Le nœud de Conway N'EST PAS smoothly slice (Piccirillo 2018/2020).
  4. Avec le théorème de Freedman (Conway est topologiquement slice),
     ceci donne la première dichotomie smooth/topologique explicite.

  EPIC #2874, Phase 1 (scaffolding uniquement — sorry permanent pour l'instant).

  Prérequis Mathlib nécessaires (TRÈS LOINTAIN) :
  - Polynôme d'Alexander (nécessite la représentation de Burau, pas dans Mathlib)
  - Définition de nœud slice (nécessite la théorie des 4-variétés lisses)
  - s-invariant de Rasmussen (nécessite l'homologie de Khovanov)
  - Construction du trace companion (nécessite le calcul de Kirby)
  - Chirurgie topologique de Freedman (nécessite un appareil topologique énorme)
-/

/-
  English mirror of `Conway.lean` (FR canonical, header mono-lingual EN).
  Convention EPIC #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n) :
  distinct FR + EN sibling files — no inline bilingual block in a single file
  (Option B rejected). The module docstring above is the FR translation of the
  EN canonical docstring; the body signatures, proofs, sorry markers, and tactics
  remain byte-identical between the two files (anti-§D byte-identity invariant).
-/

import Knots.Basic_en
import Knots.Invariant_en

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Knots_en

namespace Knots_en

/-! ## 1. Conway mutation

A Conway mutation takes a knot K with a Conway sphere (meets K in 4 points),
cuts along the sphere, rotates 180°, and reglues. Mutation preserves:
- Alexander polynomial
- Jones polynomial
- Knot genus

The Conway knot and Kinoshita-Terasaka knot are related by mutation.
-/

/-- A Conway sphere: an S² meeting the knot transversely in 4 points. -/
structure ConwaySphere where
  -- The 4 intersection points on the knot
  points : Fin 4 → Nat
  -- TODO: proper geometric definition

/-! ### Combinatorial translation of mutation at the PD level

Mutation is geometric (cut along a Conway sphere, rotate 180°, reglue), but
PL topology — gluing manifolds with boundary — is out of reach of Mathlib.
The retained combinatorial translation: a 180° rotation of a 2-strand tangle
acts on its 4 boundary points as an element of the Klein group
{id, (12)(34), (13)(24), (14)(23)} — the three half-turns and the identity.
At the PD-code level, mutating a window of crossings = permuting the label
positions within each crossing of the window.

Mutation preserves the crossing count (lemma `mutateWindow_length`) — this
is what makes the negative control below decidable.
-/

/-- 180° rotations of a 2-strand tangle: the Klein group on the four
boundary points {id, (12)(34), (13)(24), (14)(23)}. Every element is its
own inverse. -/
inductive KleinRot where
  | id : KleinRot
  | r12 : KleinRot
  | r13 : KleinRot
  | r14 : KleinRot

/-- Action of a Klein rotation on a PD crossing: the labels (values) are
preserved, their positions are permuted. -/
def KleinRot.apply (ρ : KleinRot) (c : PDCrossing) : PDCrossing :=
  match ρ with
  | .id => c
  | .r12 => ⟨c.e2, c.e1, c.e4, c.e3⟩
  | .r13 => ⟨c.e3, c.e4, c.e1, c.e2⟩
  | .r14 => ⟨c.e4, c.e3, c.e2, c.e1⟩

theorem KleinRot.apply_involutive (ρ : KleinRot) (c : PDCrossing) :
    ρ.apply (ρ.apply c) = c := by
  cases ρ <;> cases c <;> rfl

/-- Mutation of a window [i, j) of the crossing list: crossings outside the
window are unchanged, those inside are rotated by ρ. Empty window (j ≤ i):
identity. Full window: the whole diagram. -/
def mutateWindow : List PDCrossing → Nat → Nat → KleinRot → List PDCrossing
  | [], _, _, _ => []
  | c :: cs', 0, 0, _ => c :: cs'
  | c :: cs', 0, j+1, ρ => ρ.apply c :: mutateWindow cs' 0 j ρ
  | c :: cs', _+1, 0, _ => c :: cs'
  | c :: cs', i+1, j+1, ρ => c :: mutateWindow cs' i j ρ

/-- Mutation preserves the crossing count. -/
theorem mutateWindow_length (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    (mutateWindow cs i j ρ).length = cs.length := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, _+1 => simp [mutateWindow, ih]
    | _+1, 0 => rfl
    | _+1, _+1 => simp [mutateWindow, ih]

/-- Mutation is involutive: mutating the same window twice with the same
rotation returns the initial list (every Klein element is its own inverse). -/
theorem mutateWindow_involutive (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    mutateWindow (mutateWindow cs i j ρ) i j ρ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [mutateWindow]
      rw [ih 0 j, KleinRot.apply_involutive]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [mutateWindow, ih _ _]

/-- Two diagrams are mutants if there exist a window and a Klein rotation
mapping the crossing list of one onto the other. -/
def AreMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot), mutateWindow d₁.crossings i j ρ = d₂.crossings

/-- Two knots are mutants if they admit representative diagrams (in the
Reidemeister sense) that are mutants. The existential quantifier over
representatives is essential: mutation does not necessarily apply to the
designated diagrams, but to diagrams of the same isotopy classes. -/
def AreMutants (k₁ k₂ : Knot) : Prop :=
  ∃ (d₁ d₂ : KnotDiagram),
    ReidemeisterEquiv k₁.diagram d₁ ∧
    ReidemeisterEquiv k₂.diagram d₂ ∧
    AreMutantDiagrams d₁ d₂

/-! ### Elementary theory: reflexivity and symmetry

Reflexivity: empty window. Symmetry: involutivity of `mutateWindow` (every
Klein rotation is its own inverse). Transitivity is false in general for
mutation (composing two mutations on different windows is not a one-shot
mutation) — this is NOT an equivalence relation, and that is correct.
-/
/- NOTE: no transitivity claimed — mutation composes rotations over
potentially different windows, which is not a one-shot rotation. -/

/-- Empty window: mutation is the identity there, for any list. -/
theorem mutateWindow_zero_window (cs : List PDCrossing) (ρ : KleinRot) :
    mutateWindow cs 0 0 ρ = cs := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem AreMutantDiagrams.refl (d : KnotDiagram) : AreMutantDiagrams d d :=
  ⟨0, 0, .id, mutateWindow_zero_window d.crossings .id⟩

theorem AreMutantDiagrams.symm {d₁ d₂ : KnotDiagram} (h : AreMutantDiagrams d₁ d₂) :
    AreMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, hmut⟩ := h
  refine ⟨i, j, ρ, ?_⟩
  rw [← hmut]
  exact mutateWindow_involutive d₁.crossings i j ρ

theorem AreMutants.refl (k : Knot) : AreMutants k k :=
  ⟨k.diagram, k.diagram, ReidemeisterEquiv.refl k.diagram,
    ReidemeisterEquiv.refl k.diagram, AreMutantDiagrams.refl k.diagram⟩

theorem AreMutants.symm {k₁ k₂ : Knot} (h : AreMutants k₁ k₂) : AreMutants k₂ k₁ := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hmut⟩ := h
  exact ⟨d₂, d₁, hd₂, hd₁, AreMutantDiagrams.symm hmut⟩

/-! ### Controls: the definition discriminates

A definition catching neither a mutant pair nor a counterexample would be a
disguised `True` and removing the `sorry` would be cosmetic. Two controls:

- NEGATIVE (`not_areMutantDiagrams_trefoil_unknot`): mutation preserves the
  crossing count, so the trefoil (3 crossings) and the unknot (0) are not
  mutants — at the designated-diagram level.
- POSITIVE (`areMutants_trefoil_mutant`): a non-trivial mutation (full
  window, r12 rotation) is captured by the definition.

NOTE (limit of the canonical witness): the designated diagrams
`conwayKnotDiagram` and `kinoshitaTerasakaDiagram` (corrected census PD
codes, cf. §2) share their first five crossings and differ at crossings 6
to 11 — no one-shot map superposes them.
`AreMutants conwayKnot kinoshitaTerasakaKnot` will require an intermediate
diagram (Reidemeister isotopy) — later sub-grain.
-/

/-- Negative control: trefoil and unknot are not mutants (mutation preserves
the crossing count). -/
theorem not_areMutantDiagrams_trefoil_unknot :
    ¬ AreMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, hmut⟩
  have hlen := mutateWindow_length trefoilDiagram.crossings i j ρ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- The trefoil mutant by r12 over the full window. -/
def trefoilMutantDiagram : KnotDiagram where
  crossings := mutateWindow trefoilDiagram.crossings 0 3 KleinRot.r12
  numEdges := 6

def trefoilMutant : Knot where
  diagram := trefoilMutantDiagram

/-- Positive control: the definition catches a non-trivial mutation (full
window, non-identity rotation). -/
theorem areMutantDiagrams_trefoil_mutant :
    AreMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, rfl⟩

theorem areMutants_trefoil_mutant : AreMutants trefoil trefoilMutant :=
  ⟨trefoilDiagram, trefoilMutantDiagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_trefoil_mutant⟩

/-! ## 2. The Conway knot (11n34)

11 crossings in the Rolfsen table. Discovered by Conway (1970).
Trivial Alexander polynomial. Topologically slice (Freedman).
Not smoothly slice (Piccirillo 2018).

PD-code from the KnotInfo census (generated by spherogram 2.4.1),
**corrected**: the code committed by #12892 was not connected — its
crossing 11 `⟨21, 22, 22, 21⟩` used only edges {21, 22}, a component
isolated from the rest of the diagram, and edge 19 appeared twice within
its own crossing `⟨19, 14, 20, 19⟩`. The `wf` control (labels in [1, 22],
each exactly twice) does not see connectivity: the defect passed.
Measured consequence: the crossing-11 row was entirely zero in the
designated minor → determinant 0, and the original
`conway_trivial_alexander` statement (`= 1`) was false under the designated
normalization. The tuples below are the (t₁, t₂, t₃, t₀) rotation of the
census tuples, so that the over-strand sits at positions (e2, e4) of this
file's convention. Verified designated target (Python probe faithful to the
construction, validated on 3₁/4₁/5₁): minor = −t⁶, a unit — Δ = 1
classically.
-/

def conwayKnotDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨16, 9, 15, 8⟩,
    ⟨9, 21, 10, 20⟩,
    ⟨17, 11, 18, 10⟩,
    ⟨13, 19, 14, 18⟩,
    ⟨19, 15, 20, 14⟩,
    ⟨22, 17, 21, 16⟩
  ]
  numEdges := 22

/-- Control: the corrected code is well-formed in the `wf` sense (each label
of [1, 22] exactly twice). The previous disconnected code also passed this
control — the arc control is what distinguishes. -/
theorem conway_wf : conwayKnotDiagram.wf = true := by
  decide

/-- Control: the arc partition of the corrected code — stated in §4
(`conway_arcPartition`), after `arcPartition` is defined. -/

def conwayKnot : Knot where
  diagram := conwayKnotDiagram

/-! ## 3. The Kinoshita-Terasaka knot (11n42)

Also 11 crossings. Shares the trivial Alexander polynomial with 11n34.
IS smoothly slice (bounds a disk in B⁴).
Mutant of the Conway knot.

Census PD-code corrected as in §2 (the previous code was connected but
carried intra-crossing repeated edges at crossings 10 and 11 —
`⟨19, 14, 20, 19⟩` and `⟨21, 12, 22, 21⟩` — yielding a non-unit designated
minor of degree 7, false for Δ = 1). Same (t₁, t₂, t₃, t₀) rotation.
Verified designated target: minor = t⁵, a unit.
-/

def kinoshitaTerasakaDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨17, 9, 18, 8⟩,
    ⟨9, 15, 10, 14⟩,
    ⟨20, 11, 19, 10⟩,
    ⟨14, 19, 13, 18⟩,
    ⟨15, 21, 16, 20⟩,
    ⟨21, 17, 22, 16⟩
  ]
  numEdges := 22

/-- `wf` control of the corrected KT code (cf. `conway_wf`). -/
theorem kinoshitaTerasaka_wf : kinoshitaTerasakaDiagram.wf = true := by
  decide

/-- Control: arc partition of the corrected KT code — stated in §4
(`kinoshitaTerasaka_arcPartition`). -/

def kinoshitaTerasakaKnot : Knot where
  diagram := kinoshitaTerasakaDiagram

/-! ## 4. Same Alexander polynomial

Both 11n34 and 11n42 have trivial Alexander polynomial Δ(t) = 1.
This is why sliceness was so hard to determine — the Alexander
polynomial cannot distinguish them from the unknot.
-/

/-! ### Alexander matrix from the PD code (Dehn presentation, 1928)

Retained combinatorial translation — same method as for mutation (§1):
Alexander's construction reads **directly off the PD code**, with no Seifert
surface and no Burau representation. The **arcs** of the diagram are the
classes of edge labels for the relation "e2 ~ e4 at each crossing" (the
over-strand runs through the crossing: its two half-edges belong to the same
arc; the under-strand is cut there). At each crossing, the Alexander
relation (Fox derivative of the Wirtinger relation, crossing treated with
the positive convention) gives the row: `+t` on the incoming under-arc,
`−1` on the outgoing under-arc, `1−t` on the over-arc — every row sums
to zero.

The classical theorem (Alexander 1928) guarantees that for a knot, every
(n−1)×(n−1) minor of the n×n matrix equals Δ(t) up to a unit ±t^k. The
retained **designated normalization** fixes a concrete representative per
diagram: the minor without the first row and without the last column.
-/

/-- Merges the classes containing x and y of a label partition. -/
def mergePair (P : List (List Nat)) (x y : Nat) : List (List Nat) :=
  let keep := P.filter (fun C => !C.contains x && !C.contains y)
  let hit := P.filter (fun C => C.contains x || C.contains y)
  keep ++ [hit.flatten.eraseDups]

/-- The arcs of a diagram: partition of the edge labels by the closure of
the over-passage pairs (e2 ~ e4 at each crossing). -/
def arcPartition (d : KnotDiagram) : List (List Nat) :=
  let singles := (List.range d.numEdges).map (fun i => [i + 1])
  let pairs := d.crossings.map (fun c => (c.e2, c.e4))
  pairs.foldl (fun P p => mergePair P p.1 p.2) singles

/-! #### The Fox fact: the over-strand pair shares one arc class

The docstring of `alexanderEntry` claims that "every row sums to zero".
That is not a property of the row alone: it follows from a structural fact
about `arcPartition` — at every crossing, the two over-strand labels `e2`
and `e4` belong to one and the same class. `mergePair` merges precisely
that pair, and the fold afterwards only ever unites classes, never splits
one: this is the combinatorial translation of the Wirtinger relation. The
lemmas below establish it for every diagram whose edge labels live in the
range `1..numEdges` (cf `EdgesInRange`).
-/

/-- Two edge labels share one class of the partition `P`. -/
def SameClass (P : List (List Nat)) (x y : Nat) : Prop :=
  ∃ C ∈ P, x ∈ C ∧ y ∈ C

/-- The label `z` is carried by at least one class of `P`. -/
def Covered (P : List (List Nat)) (z : Nat) : Prop := ∃ C ∈ P, z ∈ C

/-- One step of the `arcPartition` fold: merge the over-strand pair. -/
def mergeStep (P : List (List Nat)) (p : Nat × Nat) : List (List Nat) :=
  mergePair P p.1 p.2

/-- Unfolded form of `mergePair`: the untouched classes, then the merged
class. -/
lemma mergePair_eq (P : List (List Nat)) (x y : Nat) :
    mergePair P x y =
      (P.filter (fun C => !C.contains x && !C.contains y)) ++
      [(P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups] := rfl

/-- The merged class carries every label of a class of the `hit` filter. -/
lemma mem_merged {P : List (List Nat)} {C : List Nat} {z x y : Nat}
    (hC : C ∈ P) (hz : z ∈ C) (hxy : (C.contains x || C.contains y) = true) :
    z ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  rw [List.mem_eraseDups, List.mem_flatten]
  exact ⟨C, List.mem_filter.mpr ⟨hC, hxy⟩, hz⟩

/-- A class carrying neither `x` nor `y` stays untouched in `keep`. -/
lemma keep_filter {P : List (List Nat)} {C : List Nat} {x y : Nat}
    (hC : C ∈ P) (hmem : ¬(C.contains x || C.contains y) = true) :
    C ∈ (P.filter (fun C => !C.contains x && !C.contains y)) := by
  refine List.mem_filter.mpr ⟨hC, ?_⟩
  simpa using hmem

/-- `mergePair` never drops an already covered label. -/
lemma covered_mergePair {P : List (List Nat)} {x y z : Nat} (h : Covered P z) :
    Covered (mergePair P x y) z := by
  obtain ⟨C, hC, hz⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC hz hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, hz⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` splits no class: two labels that shared a class still do. -/
lemma sameClass_mergePair {P : List (List Nat)} {x y a b : Nat}
    (h : SameClass P a b) : SameClass (mergePair P x y) a b := by
  obtain ⟨C, hC, ha, hb⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC ha hmem, mem_merged hC hb hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, ha, hb⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` effectively gathers `x` and `y` into one class, as soon as
both are covered (the `hit` filter is then nonempty and the merged class
carries them both). -/
lemma sameClass_mergePair_self {P : List (List Nat)} {x y : Nat}
    (hx : Covered P x) (hy : Covered P y) : SameClass (mergePair P x y) x y := by
  obtain ⟨Cx, hCx, hx'⟩ := hx
  obtain ⟨Cy, hCy, hy'⟩ := hy
  have hmx : (Cx.contains x || Cx.contains y) = true := by
    rw [Bool.or_eq_true]; left; exact List.contains_iff_mem.mpr hx'
  have hmy : (Cy.contains x || Cy.contains y) = true := by
    rw [Bool.or_eq_true]; right; exact List.contains_iff_mem.mpr hy'
  refine ⟨_, ?_, mem_merged hCx hx' hmx, mem_merged hCy hy' hmy⟩
  rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl

/-- The fold preserves shared membership. -/
lemma sameClass_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {a b : Nat}
    (h : SameClass P a b) : SameClass (pairs.foldl mergeStep P) a b := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (sameClass_mergePair h)

/-- Every pair met during the fold ends up in one class. -/
lemma sameClass_foldl_of_mem {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hcover : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ∀ q ∈ pairs, SameClass (pairs.foldl mergeStep P) q.1 q.2 := by
  induction pairs generalizing P with
  | nil => intro q hq; simp at hq
  | cons p ps ih =>
      intro q hq
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hq with rfl | hqs
      · exact sameClass_foldl (sameClass_mergePair_self
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).1
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).2)
      · exact ih (P := mergeStep P p)
          (fun r hr => ⟨covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).1,
                        covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).2⟩)
          q hqs

/-- Every label of the range `1..n` is covered by the initial singletons. -/
lemma covered_singles {n z : Nat} (h1 : 1 ≤ z) (h2 : z ≤ n) :
    Covered ((List.range n).map (fun i => [i + 1])) z := by
  refine ⟨[z], ?_, by simp⟩
  rw [List.mem_map]
  exact ⟨z - 1, by rw [List.mem_range]; omega, by simp only [Nat.sub_add_cancel h1]⟩

/-- The four edge labels of every crossing live in the diagram's range
`1..numEdges`. -/
def EdgesInRange (d : KnotDiagram) : Prop :=
  ∀ c ∈ d.crossings, 1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
    1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
    1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧
    1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges

/-- The `arcPartition` fold in `foldl` form over `mergeStep`. -/
lemma arcPartition_eq (d : KnotDiagram) :
    arcPartition d = (d.crossings.map (fun c => (c.e2, c.e4))).foldl mergeStep
      ((List.range d.numEdges).map (fun i => [i + 1])) := rfl

/-- **The Fox fact**: at every crossing of a diagram with labels in range,
the two over-strand labels belong to one and the same class of the arc
partition. It is this fact — not the mere cardinal guard of
`alexanderPolynomialAux` — that carries the zero row sum of the Alexander
matrix (cf `alexanderEntry_sum_zero` below). -/
theorem arcPartition_sameClass_overStrand (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    SameClass (arcPartition d) c.e2 c.e4 := by
  rw [arcPartition_eq]
  have hcover : ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨c', hc', rfl⟩ := hq
    obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
    exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩
  exact sameClass_foldl_of_mem hcover (c.e2, c.e4) (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Control: the arc partition of the corrected Conway code — 11 arcs
covering the 22 edges (non-degeneracy condition of the Alexander minor:
the guard `arcs'.length = rest.length + 1` of `alexanderPolynomialAux`
passes). The previous disconnected code produced an isolated {21, 22} arc
absorbed by the eliminated column of the designated minor → determinant 0.
-/
theorem conway_arcPartition :
    arcPartition conwayKnotDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21], [10, 11, 12],
       [18, 19], [14, 15], [16, 17]] := by
  decide

/-- Control: arc partition of the corrected KT code — 11 arcs, structure
shared with Conway on crossings 1-5, divergent beyond. -/
theorem kinoshitaTerasaka_arcPartition :
    arcPartition kinoshitaTerasakaDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12],
       [18, 19], [20, 21], [16, 17]] := by
  decide

/-- Alexander matrix entry: row of crossing `c`, column of arc `C`.
Positive convention (Fox of the Wirtinger relation): `+t` (incoming
under-arc), `−1` (outgoing under-arc), `1−t` (over-arc) — every row sums
to zero, the condition guaranteeing that two (n−1)×(n−1) minors differ by
a unit ±t^k. The PD code does not encode crossing chirality, and the two
conventions differ by a unit factor — the present one is designated. -/
noncomputable def alexanderEntry (c : PDCrossing) (C : List Nat) : Polynomial ℤ :=
  (if C.contains c.e1 then Polynomial.X else 0)
    + (if C.contains c.e3 then -(1 : Polynomial ℤ) else 0)
    + (if C.contains c.e2 || C.contains c.e4 then 1 - Polynomial.X else 0)

/-! #### The Alexander rows sum to zero

Under the uniqueness hypotheses — each under-strand label carried by exactly
one class, the over-strand pair meeting exactly one class — every row of the
Alexander matrix sums to zero: `t − 1 + (1 − t) = 0`. It is this fact that
makes the (n−1)×(n−1) minor independent, up to a sign, of the choice of the
struck column: the normative claim in the docstring of `alexanderEntry`
becomes a theorem here. `arcPartition_sameClass_overStrand` provides the
combinatorial half (the over-strand pair shares one class); the verification
that `arcPartition` satisfies the uniqueness hypotheses (`countP` = 1 per
label) is established in the next section (`arcPartition_countP_label`).
-/

/-- Sum of an indicator map: `w` is counted once per carrying class. -/
lemma sum_map_indicator (P : List (List Nat)) (p : List Nat → Bool) (w : Polynomial ℤ) :
    (P.map (fun C => if p C then w else 0)).sum = w * (P.countP p : Polynomial ℤ) := by
  induction P with
  | nil => simp
  | cons D Ps ih =>
      by_cases hD : p D = true
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, if_true]
        push_cast
        ring
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, Bool.false_eq_true,
          if_false]
        push_cast
        ring

/-- The sum of a three-term map distributes over the three sums. -/
lemma sum_map_three (P : List (List Nat)) (f g h : List Nat → Polynomial ℤ) :
    (P.map (fun C => f C + g C + h C)).sum =
      (P.map f).sum + (P.map g).sum + (P.map h).sum := by
  induction P with
  | nil => simp
  | cons D Ps ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- **Zero row sum**: if each under-strand label is carried by exactly one
class and the over-strand pair meets exactly one class, then the
`alexanderEntry` row sums to zero. This is the Fox fact that makes the
(n−1)×(n−1) minor independent, up to a sign, of the choice of the struck
column — the foundation requested by See #14962 before any normalization
fix. -/
theorem alexanderEntry_sum_zero (P : List (List Nat)) (c : PDCrossing)
    (h1 : P.countP (fun C => C.contains c.e1) = 1)
    (h3 : P.countP (fun C => C.contains c.e3) = 1)
    (h24 : P.countP (fun C => C.contains c.e2 || C.contains c.e4) = 1) :
    (P.map (alexanderEntry c)).sum = 0 := by
  have hmap : (P.map (alexanderEntry c)) = P.map (fun C : List Nat =>
      ((if C.contains c.e1 then (Polynomial.X : Polynomial ℤ) else 0)
        + (if C.contains c.e3 then (-(1 : Polynomial ℤ)) else 0)
        + (if C.contains c.e2 || C.contains c.e4 then (1 : Polynomial ℤ) - Polynomial.X
           else 0))) := by
    congr 1
  rw [hmap, sum_map_three, sum_map_indicator, h1, sum_map_indicator, h3, sum_map_indicator, h24]
  push_cast
  ring

/-! #### `arcPartition` is a partition: `countP` = 1 uniqueness

The previous section rested on uniqueness hypotheses (`countP` = 1). This
section establishes them for the actual `arcPartition`: classes are pairwise
disjoint (an invariant `mergePair` preserves), duplicate-free, and cover the
whole range `1..numEdges`. It follows that every row of the Alexander matrix
sums to zero with no additional hypothesis — the residual named on
See #14962 is discharged. -/

/-- Two distinct classes of `P` are disjoint. -/
def ClassesDisjoint (P : List (List Nat)) : Prop :=
  ∀ C ∈ P, ∀ D ∈ P, C ≠ D → ∀ z, z ∈ C → z ∉ D

/-- The initial singletons are pairwise disjoint. -/
lemma classesDisjoint_singles {n : Nat} :
    ClassesDisjoint ((List.range n).map (fun i => [i + 1])) := by
  intro C hC D hD hne z hzC hzD
  rw [List.mem_map] at hC hD
  obtain ⟨i, hi, rfl⟩ := hC
  obtain ⟨j, hj, rfl⟩ := hD
  simp only [List.mem_singleton] at hzC hzD
  exact hne (by congr 1; omega)

/-- The `keep` filter (classes carrying neither `x` nor `y`) never meets the
merged block: a `z` of an untouched class lies in no touched class. -/
lemma not_mem_merged_of_keep {P : List (List Nat)} {C : List Nat} {x y z : Nat}
    (hP : ClassesDisjoint P)
    (hC : C ∈ P) (hkeep : (C.contains x || C.contains y) ≠ true) :
    z ∈ C → z ∉ (P.filter (fun D => D.contains x || D.contains y)).flatten.eraseDups := by
  intro hz hmem
  rw [List.mem_eraseDups, List.mem_flatten] at hmem
  obtain ⟨D, hD, hzD⟩ := hmem
  rw [List.mem_filter] at hD
  obtain ⟨hDP, hDhit⟩ := hD
  have hne : C ≠ D := by
    intro heq; subst heq; exact hkeep hDhit
  exact hP C hC D hDP hne z hz hzD

/-- `mergePair` preserves disjointness of classes. -/
lemma classesDisjoint_mergePair {P : List (List Nat)} {x y : Nat}
    (hP : ClassesDisjoint P) : ClassesDisjoint (mergePair P x y) := by
  intro C hC D hD hne z hzC hzD
  rw [mergePair_eq, List.mem_append] at hC hD
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · rw [List.mem_filter] at hC hD
    exact hP C hC.1 D hD.1 hne z hzC hzD
  · rw [List.mem_filter] at hC
    rw [List.mem_singleton] at hD
    subst hD
    refine not_mem_merged_of_keep hP hC.1 ?_ hzC hzD
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  · rw [List.mem_filter] at hD
    rw [List.mem_singleton] at hC
    subst hC
    refine not_mem_merged_of_keep hP hD.1 ?_ hzD hzC
    cases hA : D.contains x <;> cases hB : D.contains y <;> simp_all
  · rw [List.mem_singleton] at hC hD
    exact hne (hC.trans hD.symm)

/-- Class disjointness survives the full fold. -/
lemma classesDisjoint_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (h : ClassesDisjoint P) : ClassesDisjoint (pairs.foldl mergeStep P) := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (classesDisjoint_mergePair h)

/-- The initial singletons are pairwise distinct. -/
lemma pairwise_singles {n : Nat} :
    ((List.range n).map (fun i => [i + 1])).Pairwise (fun C D => C ≠ D) :=
  List.Pairwise.map (fun i => [i + 1])
    (fun a b h heq => by
      injection heq with h1
      exact h (by omega))
    List.nodup_range

/-- A covered label stays in the merged block. -/
lemma mem_merged_of_covered {P : List (List Nat)} {x y : Nat} (hx : Covered P x) :
    x ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  obtain ⟨C, hCP, hx'⟩ := hx
  refine List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨C, ?_, hx'⟩)
  refine List.mem_filter.mpr ⟨hCP, ?_⟩
  rw [Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr hx')

/-- `mergePair` preserves duplicate-freeness: the merged block, which carries
`x`, cannot be an untouched class, which does not carry `x`. -/
lemma pairwise_mergePair {P : List (List Nat)} {x y : Nat}
    (hnd : P.Pairwise (fun C D => C ≠ D)) (hx : Covered P x) :
    (mergePair P x y).Pairwise (fun C D => C ≠ D) := by
  rw [mergePair_eq, List.pairwise_append]
  have hkeep : (P.filter (fun C => !C.contains x && !C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  refine ⟨hkeep, List.pairwise_singleton _ _, ?_⟩
  intro C hC D hDm
  rw [List.mem_filter] at hC
  obtain ⟨hCP, hcond⟩ := hC
  have hfx : C.contains x = false := by
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  rw [List.mem_singleton] at hDm
  intro heq
  subst heq
  subst hDm
  have h1 : ((P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups).contains x = true :=
    List.contains_iff_mem.mpr (mem_merged_of_covered hx)
  rw [h1] at hfx
  exact Bool.noConfusion hfx

/-- The two partition invariants traverse the full fold. -/
lemma foldl_partition_inv {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D))
    (hcov : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ClassesDisjoint (pairs.foldl mergeStep P) ∧
      (pairs.foldl mergeStep P).Pairwise (fun C D => C ≠ D) := by
  induction pairs generalizing P with
  | nil => exact ⟨hd, hnd⟩
  | cons p ps ih =>
      rw [List.foldl_cons]
      refine ih (classesDisjoint_mergePair hd)
        (pairwise_mergePair hnd (hcov p (List.mem_cons_self ..)).1) ?_
      intro q hq
      have hc := hcov q (List.mem_cons_of_mem _ hq)
      exact ⟨covered_mergePair hc.1, covered_mergePair hc.2⟩

/-- Coverage of a label survives the full fold. -/
lemma covered_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {z : Nat}
    (h : Covered P z) : Covered (pairs.foldl mergeStep P) z := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (covered_mergePair h)

/-- A pairwise-distinct list all of whose elements equal `a` has length at
most one. -/
lemma pairwise_all_eq_length_le_one {α : Type} {l : List α} {a : α}
    (hnd : l.Pairwise (fun x y => x ≠ y)) (hall : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons b t =>
      cases t with
      | nil => simp
      | cons c t' =>
          exfalso
          have hbc : b = c := (hall b (by simp)).trans (hall c (by simp)).symm
          cases hnd with
          | cons hhead _ => exact absurd hbc (hhead c (by simp))

/-- Self-contained `countP`/`filter` bridge. -/
lemma countP_length_filter {α : Type} {p : α → Bool} (l : List α) :
    l.countP p = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases h : p a = true
      · simp [h, ih]
      · simp [h, ih]

/-- **Under-strand uniqueness**: in a duplicate-free partition, a covered label
belongs to exactly one class. -/
lemma countP_contains_eq_one {P : List (List Nat)} {z : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hcov : Covered P z) :
    P.countP (fun C => C.contains z) = 1 := by
  obtain ⟨C₀, hC₀P, hz₀⟩ := hcov
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains z) :=
    List.mem_filter.mpr ⟨hC₀P, List.contains_iff_mem.mpr hz₀⟩
  have hall : ∀ D ∈ P.filter (fun C => C.contains z), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, hzD⟩ := hD
    rw [List.contains_iff_mem] at hzD
    by_contra hne
    exact hd C₀ hC₀P D hDP (Ne.symm hne) z hz₀ hzD
  have hndf : (P.filter (fun C => C.contains z)).Pairwise (fun C D => C ≠ D) :=
    List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains z)).length := List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains z)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- **Over-strand uniqueness**: if `x` and `y` share one class of a
duplicate-free partition, exactly one class carries `x` or `y`. -/
lemma countP_over_eq_one {P : List (List Nat)} {x y : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hsc : SameClass P x y) :
    P.countP (fun C => C.contains x || C.contains y) = 1 := by
  obtain ⟨C₀, hC₀P, hx₀, hy₀⟩ := hsc
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains x || C.contains y) := by
    refine List.mem_filter.mpr ⟨hC₀P, ?_⟩
    rw [Bool.or_eq_true]
    exact Or.inl (List.contains_iff_mem.mpr hx₀)
  have hall : ∀ D ∈ P.filter (fun C => C.contains x || C.contains y), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, horD⟩ := hD
    rw [Bool.or_eq_true] at horD
    rcases horD with hxD | hyD
    · rw [List.contains_iff_mem] at hxD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) x hx₀ hxD
    · rw [List.contains_iff_mem] at hyD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) y hy₀ hyD
  have hndf : (P.filter (fun C => C.contains x || C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains x || C.contains y)).length :=
    List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains x || C.contains y)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- Every pair of the fold is covered by the initial singletons. -/
lemma crossings_covered_singles {d : KnotDiagram} (h : EdgesInRange d) :
    ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨c', hc', rfl⟩ := hq
  obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
  exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩

/-- Every label of the range `1..numEdges` is covered by the partition. -/
lemma arcPartition_covered {d : KnotDiagram} {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    Covered (arcPartition d) z := by
  rw [arcPartition_eq]
  exact covered_foldl (covered_singles hz1 hz2)

/-- **`arcPartition` is a partition**: disjoint classes, no duplicates. -/
theorem arcPartition_classes (d : KnotDiagram) (h : EdgesInRange d) :
    ClassesDisjoint (arcPartition d) ∧
      (arcPartition d).Pairwise (fun C D => C ≠ D) := by
  rw [arcPartition_eq]
  exact foldl_partition_inv classesDisjoint_singles pairwise_singles
    (crossings_covered_singles h)

/-- **Hypotheses `h1`/`h3` are a theorem**: every label of the range is
carried by exactly one class of `arcPartition`. -/
theorem arcPartition_countP_label (d : KnotDiagram) (h : EdgesInRange d) {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    (arcPartition d).countP (fun C => C.contains z) = 1 := by
  obtain ⟨hd, hnd⟩ := arcPartition_classes d h
  exact countP_contains_eq_one hd hnd (arcPartition_covered hz1 hz2)

/-- **Unconditional row sum**: for any diagram with in-range labels, every
row of the Alexander matrix sums to zero — the loop between the Fox fact
and the zero sum closes, with no uniqueness hypothesis left to the
reader. -/
theorem alexanderRow_sum_zero (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    ((arcPartition d).map (alexanderEntry c)).sum = 0 := by
  obtain ⟨h1lo, h1hi, _, _, h3lo, h3hi, _, _⟩ := h c hc
  exact alexanderEntry_sum_zero (arcPartition d) c
    (arcPartition_countP_label d h h1lo h1hi)
    (arcPartition_countP_label d h h3lo h3hi)
    (countP_over_eq_one (arcPartition_classes d h).1 (arcPartition_classes d h).2
      (arcPartition_sameClass_overStrand d h hc))

/-- Type of Alexander polynomial values: ℤ[t]. -/
abbrev AlexanderPoly := Polynomial ℤ

/-- Alexander polynomial of a diagram: determinant of the designated minor
(without the first row, without the last column) of the Alexander matrix.
The classical polynomial is only defined up to a unit ±t^k; the designated
normalization fixes the representative below.

Designated cases: crossingless diagram → `1` (empty determinant, the
classical value for the unknot); arc partition of cardinal ≠ number of
crossings → `0` (degenerate diagram; for a well-formed knot diagram, arcs
and crossings are equinumerous — theorem not yet carried in this file).

Invariance under Reidemeister moves is a separate theorem, not carried
here: `alexanderPolynomial` is a function of the designated diagram, like
`mutateWindow` in §1. -/
noncomputable def alexanderPolynomialAux (d : KnotDiagram) : AlexanderPoly :=
  let arcs := arcPartition d
  match d.crossings, arcs with
  | [], _ => 1
  | _ :: rest, arcs' =>
      if arcs'.length = rest.length + 1 then
        (Matrix.of fun (i j : Fin rest.length) =>
          alexanderEntry ((rest[i.1]?).getD ⟨1, 1, 1, 1⟩) ((arcs'[j.1]?).getD [])).det
      else 0

/-- Alexander polynomial of the knot, read off its designated diagram.
Reference: Alexander (1928), Topological invariants of knots and links.

NOTE (normalization vs consumers): the theorems `conway_trivial_alexander`
and `KT_trivial_alexander` below carry the classical content `Δ = 1`.
Under the designated normalization, the minor of the diagram equals a
**unit** `±t^k` (a unit times 1). The arbitration deferred by the original
note is now settled: the computation (Python probe faithful to the
construction, corrected census codes §2-§3) gives −t⁶ for 11n34 and t⁵ for
11n42 — the statements now carry the exact designated value, a unit being
the normalized incarnation of Δ = 1. `conway_trivial_alexander` is proved
below (10×10 kernel determinant over ℤ[t]: deterministic Gauss elimination
plus one composite step at the k=8 corner, the corner not being eliminable
by shears alone — see the body of the proof); only `KT_trivial_alexander`
(t⁵ for 11n42) remains `sorry`. -/
noncomputable def alexanderPolynomial (k : Knot) : AlexanderPoly := alexanderPolynomialAux k.diagram

/-! #### Controls: the definition discriminates

A definition catching neither the unknot nor the trefoil would be a
disguised `True` and removing the `sorry` would be cosmetic (same
discipline as the `AreMutants` controls, §1):

- NEGATIVE (`alexander_unknot`, proved): the unknot, being crossingless,
  yields the classical Δ = 1 — and any nontrivial value at a crossed knot
  distinguishes it from the unknot.
- POSITIVE (`alexander_trefoil`, proved): the trefoil recovers exactly
  the classical value Δ(t) = t² − t + 1 under the designated
  normalization (minor [[−1, 1−t], [t, −1]]).
-/

/-- Negative control: the unknot has trivial Alexander polynomial
(empty matrix, determinant 1). -/
theorem alexander_unknot : alexanderPolynomial unknot = 1 := by
  simp (config := { decide := true })
    [alexanderPolynomial, alexanderPolynomialAux, unknot, unknotDiagram]

/-- Generic 2×2 determinant (special case of the Laplace expansion:
Mathlib v4.32.1 no longer provides `Matrix.det_two`). -/
theorem det_two_aux (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  rw [Matrix.det_succ_column_zero]
  simp [Matrix.det_unique, Fin.sum_univ_two]
  ring

/-- Generic 3×3 determinant (same spirit as `det_two_aux`: Laplace expansion
along the first column, the 2×2 minors being handled by `det_two_aux`). -/
theorem det_three_aux (A : Matrix (Fin 3) (Fin 3) (Polynomial ℤ)) :
    A.det = A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)
          - A 1 0 * (A 0 1 * A 2 2 - A 0 2 * A 2 1)
          + A 2 0 * (A 0 1 * A 1 2 - A 0 2 * A 1 1) := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_two_aux, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- Positive control: the trefoil recovers the classical value t² − t + 1
under the designated normalization (minor without first row nor last
column). -/
theorem alexander_trefoil :
    alexanderPolynomial trefoil = Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hp : arcPartition trefoilDiagram = [[4, 5], [1, 6], [2, 3]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, trefoil, hp]
  simp only [trefoilDiagram]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Discrimination corollary: the Alexander polynomial distinguishes the
trefoil from the unknot — first non-triviality of the development,
obtained by combining the two controls above (this is the property that
sells the invariant: a value that is not constant across knot classes). -/
theorem trefoil_ne_unknot_alexander :
    alexanderPolynomial trefoil ≠ alexanderPolynomial unknot := by
  rw [alexander_trefoil, alexander_unknot]
  intro h
  have h2 := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
  simp [Polynomial.coeff_X] at h2

/-- Invariance under mutation: the mutant of the trefoil (full window, r12)
has the same Alexander polynomial as the trefoil — the Alexander polynomial
is invariant under mutation (Conway 1970), and the trefoil being
amphichiral, its mutant remains a trefoil. -/
theorem alexander_trefoilMutant :
    alexanderPolynomial trefoilMutant = Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hp : arcPartition trefoilMutantDiagram = [[1, 2], [3, 4], [5, 6]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, trefoilMutant, hp]
  dsimp [trefoilMutantDiagram, mutateWindow, KleinRot.apply, trefoilDiagram]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Discrimination control on the figure-eight knot (4_1): under the
designated normalization (minor omitting the first row and the last column),
the function returns −2·t² + 2·t − 1 on the corrected raw wiring.

Honesty note: this value is NOT the classical Alexander polynomial of 4_1
(which is ±t² ∓ 3·t ± 1, i.e. t² − 3·t + 1 up to a unit factor); the
theorem measures the value actually produced by the designated function on
a 4-crossing wiring that forms a single loop. The trefoil (t² − t + 1) and
the determinant |P(−1)| = 5 = det(4_1) are reproduced, but the polynomial
shape diverges from the classical value on the 4-crossing class — anomaly
exhaustively documented (2736 orientation-valid wirings tested, including
the DT [4,6,8,2] wiring) in the follow-up issue opened with this PR.
The divergence is formalized below (`alexander_figureEight_not_classical`:
not a unit) and repaired by the signed variant
(`alexander_figureEight_signed`: the exact classical value).
-/
theorem alexander_figureEight :
    alexanderPolynomial figureEight =
      - (2 : Polynomial ℤ) * Polynomial.X ^ 2 + 2 * Polynomial.X - 1 := by
  have hp : arcPartition figureEightDiagram = [[3, 4], [5, 6], [7, 8], [1, 2]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, figureEight, hp]
  simp only [figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-! #### 4-crossing class divergence — diagnosis and signed variant

Diagnosis of anomaly #14962: the `alexanderEntry` row is the Fox row of a
**positive** crossing (derivative of the Wirtinger relation
`x_o x_i x_o⁻¹ = x_out`, abelianized). Since the PD code does not encode
chirality, the unsigned matrix treats every crossing as positive. On an
all-positive diagram — the `3_1` trefoil of `Basic.lean`, whose three
crossings are documented positive — the matrix IS the Alexander matrix and
the designated minor recovers the classical value. On the figure-eight
knot `4_1` (amphichiral, two crossings of each sign in any minimal
alternating diagram), the matrix is wrong on the negative crossings: the
minor returns `−2t² + 2t − 1`, outside the unit class of the classical
`t² − 3t + 1` (see `alexander_figureEight_not_classical` below) — so the
divergence is NOT a representative artifact (no symmetrization or Conway
normalization `Δ(1) = 1` can repair it), but a chirality artifact. The
determinant survives: `|P(−1)| = 5 = det(4_1)`
(`alexander_figureEight_eval_neg_one`).

The signed variant `alexanderPolynomialSigned` takes chirality as data and
recovers the classical value on the figure-eight: the alternating labeling
`[−, +, −, +]` of the DT-derived diagram returns exactly `t² − 3t + 1`,
its mirror `[+, −, +, −]` returns `t · (t² − 3t + 1)` — same unit class,
as amphichirality demands. -/

/-- Alexander row of a **negative** crossing: Fox derivative of the mirror
Wirtinger relation `x_o⁻¹ x_i x_o = x_out`, multiplied by the unit `t` to
stay polynomial — `+1` on the incoming under-arc, `−t` on the outgoing
under-arc, `t−1` on the over-arc. Each row sums to zero, as for
`alexanderEntry`. -/
noncomputable def alexanderEntryNeg (c : PDCrossing) (C : List Nat) : Polynomial ℤ :=
  (if C.contains c.e1 then 1 else 0)
    + (if C.contains c.e3 then -Polynomial.X else 0)
    + (if C.contains c.e2 || C.contains c.e4 then Polynomial.X - 1 else 0)

/-- Signed Alexander row: `true` (positive crossing) → `alexanderEntry`,
`false` (negative crossing) → `alexanderEntryNeg`. -/
noncomputable def alexanderEntrySigned (c : PDCrossing) (s : Bool)
    (C : List Nat) : Polynomial ℤ :=
  if s then alexanderEntry c C else alexanderEntryNeg c C

/-- Signed Alexander polynomial of a diagram: same designated minor as
`alexanderPolynomialAux`, each crossing carrying its sign (sign list
parallel to the crossings; the first crossing's sign is unused — its row
is eliminated by the minor, `getD true` neutral). -/
noncomputable def alexanderPolynomialSigned (d : KnotDiagram)
    (signs : List Bool) : AlexanderPoly :=
  let arcs := arcPartition d
  match d.crossings, arcs with
  | [], _ => 1
  | _ :: rest, arcs' =>
      if arcs'.length = rest.length + 1 then
        (Matrix.of fun (i j : Fin rest.length) =>
          alexanderEntrySigned ((rest[i.1]?).getD ⟨1, 1, 1, 1⟩)
            ((signs[i.1 + 1]?).getD true) ((arcs'[j.1]?).getD [])).det
      else 0

/-- The divergence is not a unit: the designated value on the figure-eight
equals `ε · t^k · (t² − 3t + 1)` for NO unit `ε = ±1` and no exponent `k`.
Proof by evaluations: at `0` the designated value returns `−1`, forcing
`k = 0` then `ε = −1`; at `2` it returns `−5` while `ε · 2^k · (2² − 3·2 + 1)`
then equals `1`. -/
theorem alexander_figureEight_not_classical :
    ¬ ∃ (k : ℕ) (ε : ℤ), ε * ε = 1 ∧
      alexanderPolynomial figureEight =
        Polynomial.C ε * Polynomial.X ^ k * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  rintro ⟨k, ε, -, h⟩
  rcases k with _ | k
  · have h0 := congrArg (Polynomial.eval 0) h
    have h2 := congrArg (Polynomial.eval 2) h
    rw [alexander_figureEight, pow_zero] at h0 h2
    simp only [Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, pow_two, mul_one,
      mul_zero, add_zero, zero_add, zero_sub] at h0 h2
    norm_num at h0 h2
    omega
  · have h0 := congrArg (Polynomial.eval 0) h
    rw [alexander_figureEight, pow_succ] at h0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, pow_two, mul_assoc, mul_zero, zero_mul,
      mul_one, add_zero, zero_add, zero_sub] at h0
    norm_num at h0

/-- The knot determinant survives the divergence: the designated value at
`−1` equals `−5`, so `|P(−1)| = 5 = det(4_1)` (classical: for a knot,
`det = |Δ(−1)|`; `4_1` is amphichiral). The unsigned minor loses the
polynomial shape but not its value at `−1`. -/
theorem alexander_figureEight_eval_neg_one :
    (alexanderPolynomial figureEight).eval (-1) = -5 := by
  rw [alexander_figureEight]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, pow_two, mul_zero, mul_one, add_zero, zero_add, zero_sub]
  norm_num

/-- The signed variant recovers the classical value on the figure-eight:
the alternating labeling `[−, +, −, +]` of the DT-derived diagram returns
exactly `t² − 3t + 1` under the same designated minor, and its mirror
`[+, −, +, −]` returns `t · (t² − 3t + 1)` — same unit class, as
amphichirality of `4_1` demands. -/
theorem alexander_figureEight_signed :
    alexanderPolynomialSigned figureEightDiagram [false, true, false, true]
      = Polynomial.X ^ 2 - 3 * Polynomial.X + 1 := by
  simp only [alexanderPolynomialSigned, figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-- Mirror of the previous: the opposite alternating labeling `[+, −, +, −]`
returns `t · (t² − 3t + 1)` — same unit class, as amphichirality demands
(the two mirror diagrams represent the same knot). -/
theorem alexander_figureEight_signed_mirror :
    alexanderPolynomialSigned figureEightDiagram [true, false, true, false]
      = Polynomial.X * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 32000000 in
/-- Trivial Alexander polynomial of the Conway knot — classical content
Δ(t) = 1; under the designated normalization, the minor equals the unit
−t⁶ (§4 note arbitration settled: exact designated value). -/
theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = -(Polynomial.X ^ 6) := by
  have hp := conway_arcPartition
  simp only [alexanderPolynomial, alexanderPolynomialAux, conwayKnot, hp]
  simp only [conwayKnotDiagram]
  have hlen : ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]] : List (List Nat)).length =
      ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩] : List PDCrossing).length + 1 := by
    decide
  rw [if_pos hlen]
  show (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]][j.1]?.getD [])).det = -(Polynomial.X ^ 6)
  set A0 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h0
  have hM0 : (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]][j.1]?.getD [])) = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [Matrix.of_apply,
        alexanderEntry, h0] <;>
      first
      | rfl
      | ring
  rw [hM0]
  set A1 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h1
  have e1 : A1 = A0.updateRow 7 (A0 7 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A0 3) := by
    rw [h1, h0]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d1 : A1.det = A0.det := by
    rw [e1, Matrix.det_updateRow_add_smul_self A0 (by decide : ((7 : Fin 10) ≠ 3)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A2 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h2
  have e2 : A2 = A1.updateRow 3 (A1 3 + (1 : Polynomial ℤ) • A1 0) := by
    rw [h2, h1]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d2 : A2.det = A1.det := by
    rw [e2, Matrix.det_updateRow_add_smul_self A1 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A3 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h3
  have e3 : A3 = A2.updateRow 0 (A2 0 + (-1 : Polynomial ℤ) • A2 3) := by
    rw [h3, h2]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d3 : A3.det = A2.det := by
    rw [e3, Matrix.det_updateRow_add_smul_self A2 (by decide : ((0 : Fin 10) ≠ 3)) (-1 : Polynomial ℤ)]
  set A4 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h4
  have e4 : A4 = A3.updateRow 3 (A3 3 + (1 : Polynomial ℤ) • A3 0) := by
    rw [h4, h3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d4 : A4.det = A3.det := by
    rw [e4, Matrix.det_updateRow_add_smul_self A3 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A5 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h5
  have e5 : A5 = A4.updateRow 3 (A4 3 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A4 1) := by
    rw [h5, h4]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d5 : A5.det = A4.det := by
    rw [e5, Matrix.det_updateRow_add_smul_self A4 (by decide : ((3 : Fin 10) ≠ 1)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A6 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h6
  have e6 : A6 = A5.updateCol 3 (fun r => A5 r 3 + (1 : Polynomial ℤ) • A5 r 1) := by
    rw [h6, h5]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d6 : A6.det = A5.det := by
    rw [e6, Matrix.det_updateCol_add_smul_self A5 (by decide : ((3 : Fin 10) ≠ 1)) (1 : Polynomial ℤ)]
  set A7 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h7
  have e7 : A7 = A6.updateCol 1 (fun r => A6 r 1 + (-1 : Polynomial ℤ) • A6 r 3) := by
    rw [h7, h6]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d7 : A7.det = A6.det := by
    rw [e7, Matrix.det_updateCol_add_smul_self A6 (by decide : ((1 : Fin 10) ≠ 3)) (-1 : Polynomial ℤ)]
  set A8 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h8
  have e8 : A8 = A7.updateCol 3 (fun r => A7 r 3 + (1 : Polynomial ℤ) • A7 r 1) := by
    rw [h8, h7]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d8 : A8.det = A7.det := by
    rw [e8, Matrix.det_updateCol_add_smul_self A7 (by decide : ((3 : Fin 10) ≠ 1)) (1 : Polynomial ℤ)]
  set A9 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h9
  have e9 : A9 = A8.updateRow 7 (A8 7 + (-1 : Polynomial ℤ) • A8 4) := by
    rw [h9, h8]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d9 : A9.det = A8.det := by
    rw [e9, Matrix.det_updateRow_add_smul_self A8 (by decide : ((7 : Fin 10) ≠ 4)) (-1 : Polynomial ℤ)]
  set A10 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h10
  have e10 : A10 = A9.updateRow 8 (A9 8 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A9 4) := by
    rw [h10, h9]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d10 : A10.det = A9.det := by
    rw [e10, Matrix.det_updateRow_add_smul_self A9 (by decide : ((8 : Fin 10) ≠ 4)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A11 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h11
  have e11 : A11 = A10.updateRow 4 (A10 4 + (1 : Polynomial ℤ) • A10 2) := by
    rw [h11, h10]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d11 : A11.det = A10.det := by
    rw [e11, Matrix.det_updateRow_add_smul_self A10 (by decide : ((4 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A12 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h12
  have e12 : A12 = A11.updateRow 2 (A11 2 + (-1 : Polynomial ℤ) • A11 4) := by
    rw [h12, h11]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d12 : A12.det = A11.det := by
    rw [e12, Matrix.det_updateRow_add_smul_self A11 (by decide : ((2 : Fin 10) ≠ 4)) (-1 : Polynomial ℤ)]
  set A13 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h13
  have e13 : A13 = A12.updateRow 4 (A12 4 + (1 : Polynomial ℤ) • A12 2) := by
    rw [h13, h12]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d13 : A13.det = A12.det := by
    rw [e13, Matrix.det_updateRow_add_smul_self A12 (by decide : ((4 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A14 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h14
  have e14 : A14 = A13.updateCol 9 (fun r => A13 r 9 + (1 : Polynomial ℤ) • A13 r 2) := by
    rw [h14, h13]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d14 : A14.det = A13.det := by
    rw [e14, Matrix.det_updateCol_add_smul_self A13 (by decide : ((9 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A15 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h15
  have e15 : A15 = A14.updateCol 2 (fun r => A14 r 2 + (-1 : Polynomial ℤ) • A14 r 9) := by
    rw [h15, h14]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d15 : A15.det = A14.det := by
    rw [e15, Matrix.det_updateCol_add_smul_self A14 (by decide : ((2 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A16 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h16
  have e16 : A16 = A15.updateCol 9 (fun r => A15 r 9 + (1 : Polynomial ℤ) • A15 r 2) := by
    rw [h16, h15]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d16 : A16.det = A15.det := by
    rw [e16, Matrix.det_updateCol_add_smul_self A15 (by decide : ((9 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A17 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h17
  have e17 : A17 = A16.updateRow 7 (A16 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A16 6) := by
    rw [h17, h16]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d17 : A17.det = A16.det := by
    rw [e17, Matrix.det_updateRow_add_smul_self A16 (by decide : ((7 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A18 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h18
  have e18 : A18 = A17.updateRow 8 (A17 8 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A17 6) := by
    rw [h18, h17]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d18 : A18.det = A17.det := by
    rw [e18, Matrix.det_updateRow_add_smul_self A17 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A19 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h19
  have e19 : A19 = A18.updateRow 6 (A18 6 + (1 : Polynomial ℤ) • A18 3) := by
    rw [h19, h18]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d19 : A19.det = A18.det := by
    rw [e19, Matrix.det_updateRow_add_smul_self A18 (by decide : ((6 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A20 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h20
  have e20 : A20 = A19.updateRow 3 (A19 3 + (-1 : Polynomial ℤ) • A19 6) := by
    rw [h20, h19]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d20 : A20.det = A19.det := by
    rw [e20, Matrix.det_updateRow_add_smul_self A19 (by decide : ((3 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A21 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h21
  have e21 : A21 = A20.updateRow 6 (A20 6 + (1 : Polynomial ℤ) • A20 3) := by
    rw [h21, h20]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d21 : A21.det = A20.det := by
    rw [e21, Matrix.det_updateRow_add_smul_self A20 (by decide : ((6 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A22 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h22
  have e22 : A22 = A21.updateCol 8 (fun r => A21 r 8 + (1 : Polynomial ℤ) • A21 r 3) := by
    rw [h22, h21]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d22 : A22.det = A21.det := by
    rw [e22, Matrix.det_updateCol_add_smul_self A21 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A23 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h23
  have e23 : A23 = A22.updateCol 3 (fun r => A22 r 3 + (-1 : Polynomial ℤ) • A22 r 8) := by
    rw [h23, h22]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d23 : A23.det = A22.det := by
    rw [e23, Matrix.det_updateCol_add_smul_self A22 (by decide : ((3 : Fin 10) ≠ 8)) (-1 : Polynomial ℤ)]
  set A24 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h24
  have e24 : A24 = A23.updateCol 8 (fun r => A23 r 8 + (1 : Polynomial ℤ) • A23 r 3) := by
    rw [h24, h23]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d24 : A24.det = A23.det := by
    rw [e24, Matrix.det_updateCol_add_smul_self A23 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A25 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h25
  have e25 : A25 = A24.updateRow 5 (A24 5 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A24 9) := by
    rw [h25, h24]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d25 : A25.det = A24.det := by
    rw [e25, Matrix.det_updateRow_add_smul_self A24 (by decide : ((5 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A26 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h26
  have e26 : A26 = A25.updateRow 8 (A25 8 + (-1 : Polynomial ℤ) • A25 9) := by
    rw [h26, h25]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d26 : A26.det = A25.det := by
    rw [e26, Matrix.det_updateRow_add_smul_self A25 (by decide : ((8 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A27 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h27
  have e27 : A27 = A26.updateRow 9 (A26 9 + (1 : Polynomial ℤ) • A26 4) := by
    rw [h27, h26]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d27 : A27.det = A26.det := by
    rw [e27, Matrix.det_updateRow_add_smul_self A26 (by decide : ((9 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A28 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h28
  have e28 : A28 = A27.updateRow 4 (A27 4 + (-1 : Polynomial ℤ) • A27 9) := by
    rw [h28, h27]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d28 : A28.det = A27.det := by
    rw [e28, Matrix.det_updateRow_add_smul_self A27 (by decide : ((4 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A29 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h29
  have e29 : A29 = A28.updateRow 9 (A28 9 + (1 : Polynomial ℤ) • A28 4) := by
    rw [h29, h28]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d29 : A29.det = A28.det := by
    rw [e29, Matrix.det_updateRow_add_smul_self A28 (by decide : ((9 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A30 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h30
  have e30 : A30 = A29.updateCol 6 (fun r => A29 r 6 + (1 : Polynomial ℤ) • A29 r 4) := by
    rw [h30, h29]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d30 : A30.det = A29.det := by
    rw [e30, Matrix.det_updateCol_add_smul_self A29 (by decide : ((6 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A31 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h31
  have e31 : A31 = A30.updateCol 4 (fun r => A30 r 4 + (-1 : Polynomial ℤ) • A30 r 6) := by
    rw [h31, h30]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d31 : A31.det = A30.det := by
    rw [e31, Matrix.det_updateCol_add_smul_self A30 (by decide : ((4 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A32 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h32
  have e32 : A32 = A31.updateCol 6 (fun r => A31 r 6 + (1 : Polynomial ℤ) • A31 r 4) := by
    rw [h32, h31]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d32 : A32.det = A31.det := by
    rw [e32, Matrix.det_updateCol_add_smul_self A31 (by decide : ((6 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A33 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h33
  have e33 : A33 = A32.updateRow 7 (A32 7 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A32 6) := by
    rw [h33, h32]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d33 : A33.det = A32.det := by
    rw [e33, Matrix.det_updateRow_add_smul_self A32 (by decide : ((7 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A34 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h34
  have e34 : A34 = A33.updateRow 9 (A33 9 + (-1 : Polynomial ℤ) • A33 6) := by
    rw [h34, h33]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d34 : A34.det = A33.det := by
    rw [e34, Matrix.det_updateRow_add_smul_self A33 (by decide : ((9 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A35 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h35
  have e35 : A35 = A34.updateRow 6 (A34 6 + (1 : Polynomial ℤ) • A34 5) := by
    rw [h35, h34]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d35 : A35.det = A34.det := by
    rw [e35, Matrix.det_updateRow_add_smul_self A34 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A36 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h36
  have e36 : A36 = A35.updateRow 5 (A35 5 + (-1 : Polynomial ℤ) • A35 6) := by
    rw [h36, h35]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d36 : A36.det = A35.det := by
    rw [e36, Matrix.det_updateRow_add_smul_self A35 (by decide : ((5 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A37 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h37
  have e37 : A37 = A36.updateRow 6 (A36 6 + (1 : Polynomial ℤ) • A36 5) := by
    rw [h37, h36]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d37 : A37.det = A36.det := by
    rw [e37, Matrix.det_updateRow_add_smul_self A36 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A38 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h38
  have e38 : A38 = A37.updateCol 6 (fun r => A37 r 6 + (1 : Polynomial ℤ) • A37 r 5) := by
    rw [h38, h37]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d38 : A38.det = A37.det := by
    rw [e38, Matrix.det_updateCol_add_smul_self A37 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A39 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h39
  have e39 : A39 = A38.updateCol 5 (fun r => A38 r 5 + (-1 : Polynomial ℤ) • A38 r 6) := by
    rw [h39, h38]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d39 : A39.det = A38.det := by
    rw [e39, Matrix.det_updateCol_add_smul_self A38 (by decide : ((5 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A40 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h40
  have e40 : A40 = A39.updateCol 6 (fun r => A39 r 6 + (1 : Polynomial ℤ) • A39 r 5) := by
    rw [h40, h39]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d40 : A40.det = A39.det := by
    rw [e40, Matrix.det_updateCol_add_smul_self A39 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A41 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h41
  have e41 : A41 = A40.updateRow 7 (A40 7 + ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ) • A40 6) := by
    rw [h41, h40]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d41 : A41.det = A40.det := by
    rw [e41, Matrix.det_updateRow_add_smul_self A40 (by decide : ((7 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)]
  set A42 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h42
  have e42 : A42 = A41.updateRow 8 (A41 8 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A41 6) := by
    rw [h42, h41]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d42 : A42.det = A41.det := by
    rw [e42, Matrix.det_updateRow_add_smul_self A41 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A43 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h43
  have e43 : A43 = A42.updateRow 9 (A42 9 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A42 6) := by
    rw [h43, h42]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d43 : A43.det = A42.det := by
    rw [e43, Matrix.det_updateRow_add_smul_self A42 (by decide : ((9 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A44 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h44
  have e44 : A44 = A43.updateCol 7 (fun r => A43 r 7 + (1 : Polynomial ℤ) • A43 r 6) := by
    rw [h44, h43]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d44 : A44.det = A43.det := by
    rw [e44, Matrix.det_updateCol_add_smul_self A43 (by decide : ((7 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A45 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h45
  have e45 : A45 = A44.updateCol 6 (fun r => A44 r 6 + (-1 : Polynomial ℤ) • A44 r 7) := by
    rw [h45, h44]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d45 : A45.det = A44.det := by
    rw [e45, Matrix.det_updateCol_add_smul_self A44 (by decide : ((6 : Fin 10) ≠ 7)) (-1 : Polynomial ℤ)]
  set A46 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h46
  have e46 : A46 = A45.updateCol 7 (fun r => A45 r 7 + (1 : Polynomial ℤ) • A45 r 6) := by
    rw [h46, h45]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d46 : A46.det = A45.det := by
    rw [e46, Matrix.det_updateCol_add_smul_self A45 (by decide : ((7 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A47 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h47
  have e47 : A47 = A46.updateRow 7 (A46 7 + ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A46 9) := by
    rw [h47, h46]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d47 : A47.det = A46.det := by
    rw [e47, Matrix.det_updateRow_add_smul_self A46 (by decide : ((7 : Fin 10) ≠ 9)) ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A48 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h48
  have e48 : A48 = A47.updateRow 9 (A47 9 + (1 : Polynomial ℤ) • A47 7) := by
    rw [h48, h47]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d48 : A48.det = A47.det := by
    rw [e48, Matrix.det_updateRow_add_smul_self A47 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A49 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h49
  have e49 : A49 = A48.updateRow 7 (A48 7 + (-1 : Polynomial ℤ) • A48 9) := by
    rw [h49, h48]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d49 : A49.det = A48.det := by
    rw [e49, Matrix.det_updateRow_add_smul_self A48 (by decide : ((7 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A50 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h50
  have e50 : A50 = A49.updateRow 9 (A49 9 + (1 : Polynomial ℤ) • A49 7) := by
    rw [h50, h49]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d50 : A50.det = A49.det := by
    rw [e50, Matrix.det_updateRow_add_smul_self A49 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A51 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h51
  have e51 : A51 = A50.updateCol 9 (fun r => A50 r 9 + (1 : Polynomial ℤ) • A50 r 7) := by
    rw [h51, h50]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d51 : A51.det = A50.det := by
    rw [e51, Matrix.det_updateCol_add_smul_self A50 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A52 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h52
  have e52 : A52 = A51.updateCol 7 (fun r => A51 r 7 + (-1 : Polynomial ℤ) • A51 r 9) := by
    rw [h52, h51]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d52 : A52.det = A51.det := by
    rw [e52, Matrix.det_updateCol_add_smul_self A51 (by decide : ((7 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A53 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h53
  have e53 : A53 = A52.updateCol 9 (fun r => A52 r 9 + (1 : Polynomial ℤ) • A52 r 7) := by
    rw [h53, h52]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d53 : A53.det = A52.det := by
    rw [e53, Matrix.det_updateCol_add_smul_self A52 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A54 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 3 + 3 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - 7 * Polynomial.X ^ 7 + 4 * Polynomial.X ^ 8 - Polynomial.X ^ 9 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + 7 * Polynomial.X ^ 4 - 10 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - 4 * Polynomial.X ^ 7 + Polynomial.X ^ 8 : Polynomial ℤ)]
  ] with h54
  have e54 : A54 = A53.updateRow 9 (((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A53 9) := by
    rw [h54, h53]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have eself : A53.updateRow 9 (A53 9) = A53 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> simp [Matrix.updateRow_apply]
  have d54 : A54.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A53.det := by
    rw [e54, Matrix.det_updateRow_smul A53 9 ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) (A53 9), eself]
  set A55 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h55
  have e55 : A55 = A54.updateRow 9 (A54 9 + ((0 : Polynomial ℤ) - Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ) • A54 8) := by
    rw [h55, h54]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d55 : A55.det = A54.det := by
    rw [e55, Matrix.det_updateRow_add_smul_self A54 (by decide : ((9 : Fin 10) ≠ 8)) ((0 : Polynomial ℤ) - Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ)]
  have hchain : A55.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A0.det := by
    rw [d55, d54, d53, d52, d51, d50, d49, d48, d47, d46, d45, d44, d43, d42, d41, d40, d39, d38, d37, d36, d35, d34, d33, d32, d31, d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hT : A55.BlockTriangular id := by
    intro i j hij
    rw [h55]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
  have hdiag : (∏ i, A55 i i) = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * ( -(Polynomial.X ^ 6)) := by
    rw [h55]
    simp only [Fin.prod_univ_succ, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    have htail : ∀ g : Fin 0 → Polynomial ℤ, (∏ i, g i) = 1 := fun g =>
      Finset.prod_eq_one (fun x _ => Fin.elim0 x)
    rw [htail _]
    ring
  have ha : ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) ≠ 0 := by
    intro hz
    have c1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hz
    simp [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow] at c1
  have key : ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A0.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * (-(Polynomial.X ^ 6)) := by
    rw [← hchain, Matrix.det_of_upperTriangular hT, hdiag]
  exact mul_left_cancel₀ ha key

set_option maxRecDepth 8000 in
set_option maxHeartbeats 32000000 in
/-- Trivial Alexander polynomial of the Kinoshita-Terasaka knot — classical
content Δ(t) = 1; under the designated normalization, the minor equals the
unit t⁵ (same discipline as `conway_trivial_alexander`: deterministic
Gaussian elimination over ℤ[t] by shears only, determinant invariant at
each step — each `d_k` is `det_updateRow_add_smul_self`). -/
theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = Polynomial.X ^ 5 := by
  have hp := kinoshitaTerasaka_arcPartition
  simp only [alexanderPolynomial, alexanderPolynomialAux, kinoshitaTerasakaKnot, hp]
  simp only [kinoshitaTerasakaDiagram]
  have hlen : ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]] : List (List Nat)).length =
      ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩] : List PDCrossing).length + 1 := by
    decide
  rw [if_pos hlen]
  show (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]][j.1]?.getD [])).det = Polynomial.X ^ 5
  set A0 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h0
  have hM0 : (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]][j.1]?.getD [])) = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [Matrix.of_apply,
        alexanderEntry, h0] <;>
      first
      | rfl
      | ring
  rw [hM0]
  set A1 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h1
  have e1 : A1 = A0.updateRow 0 (A0 0 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A0 3) := by
    rw [h1, h0]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d1 : A1.det = A0.det := by
    rw [e1, Matrix.det_updateRow_add_smul_self A0 (by decide : ((0 : Fin 10) ≠ 3)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A2 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h2
  have e2 : A2 = A1.updateRow 3 (A1 3 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A1 0) := by
    rw [h2, h1]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d2 : A2.det = A1.det := by
    rw [e2, Matrix.det_updateRow_add_smul_self A1 (by decide : ((3 : Fin 10) ≠ 0)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A3 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h3
  have e3 : A3 = A2.updateRow 7 (A2 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A2 0) := by
    rw [h3, h2]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d3 : A3.det = A2.det := by
    rw [e3, Matrix.det_updateRow_add_smul_self A2 (by decide : ((7 : Fin 10) ≠ 0)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A4 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h4
  have e4 : A4 = A3.updateRow 1 (A3 1 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A3 9) := by
    rw [h4, h3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d4 : A4.det = A3.det := by
    rw [e4, Matrix.det_updateRow_add_smul_self A3 (by decide : ((1 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A5 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h5
  have e5 : A5 = A4.updateRow 9 (A4 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A4 1) := by
    rw [h5, h4]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d5 : A5.det = A4.det := by
    rw [e5, Matrix.det_updateRow_add_smul_self A4 (by decide : ((9 : Fin 10) ≠ 1)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A6 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h6
  have e6 : A6 = A5.updateRow 9 (A5 9 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A5 2) := by
    rw [h6, h5]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d6 : A6.det = A5.det := by
    rw [e6, Matrix.det_updateRow_add_smul_self A5 (by decide : ((9 : Fin 10) ≠ 2)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A7 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h7
  have e7 : A7 = A6.updateRow 7 (A6 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A6 3) := by
    rw [h7, h6]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d7 : A7.det = A6.det := by
    rw [e7, Matrix.det_updateRow_add_smul_self A6 (by decide : ((7 : Fin 10) ≠ 3)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A8 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h8
  have e8 : A8 = A7.updateRow 3 (A7 3 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A7 9) := by
    rw [h8, h7]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d8 : A8.det = A7.det := by
    rw [e8, Matrix.det_updateRow_add_smul_self A7 (by decide : ((3 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A9 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h9
  have e9 : A9 = A8.updateRow 3 (A8 3 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A8 9) := by
    rw [h9, h8]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d9 : A9.det = A8.det := by
    rw [e9, Matrix.det_updateRow_add_smul_self A8 (by decide : ((3 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A10 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h10
  have e10 : A10 = A9.updateRow 9 (A9 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A9 3) := by
    rw [h10, h9]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d10 : A10.det = A9.det := by
    rw [e10, Matrix.det_updateRow_add_smul_self A9 (by decide : ((9 : Fin 10) ≠ 3)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A11 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h11
  have e11 : A11 = A10.updateRow 4 (A10 4 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A10 7) := by
    rw [h11, h10]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d11 : A11.det = A10.det := by
    rw [e11, Matrix.det_updateRow_add_smul_self A10 (by decide : ((4 : Fin 10) ≠ 7)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A12 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h12
  have e12 : A12 = A11.updateRow 7 (A11 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A11 4) := by
    rw [h12, h11]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d12 : A12.det = A11.det := by
    rw [e12, Matrix.det_updateRow_add_smul_self A11 (by decide : ((7 : Fin 10) ≠ 4)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A13 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h13
  have e13 : A13 = A12.updateRow 4 (A12 4 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A12 9) := by
    rw [h13, h12]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d13 : A13.det = A12.det := by
    rw [e13, Matrix.det_updateRow_add_smul_self A12 (by decide : ((4 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A14 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h14
  have e14 : A14 = A13.updateRow 9 (A13 9 + ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A13 4) := by
    rw [h14, h13]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d14 : A14.det = A13.det := by
    rw [e14, Matrix.det_updateRow_add_smul_self A13 (by decide : ((9 : Fin 10) ≠ 4)) ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A15 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h15
  have e15 : A15 = A14.updateRow 5 (A14 5 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A14 7) := by
    rw [h15, h14]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d15 : A15.det = A14.det := by
    rw [e15, Matrix.det_updateRow_add_smul_self A14 (by decide : ((5 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A16 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h16
  have e16 : A16 = A15.updateRow 7 (A15 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A15 5) := by
    rw [h16, h15]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d16 : A16.det = A15.det := by
    rw [e16, Matrix.det_updateRow_add_smul_self A15 (by decide : ((7 : Fin 10) ≠ 5)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A17 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h17
  have e17 : A17 = A16.updateRow 9 (A16 9 + ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ) • A16 5) := by
    rw [h17, h16]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d17 : A17.det = A16.det := by
    rw [e17, Matrix.det_updateRow_add_smul_self A16 (by decide : ((9 : Fin 10) ≠ 5)) ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  set A18 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h18
  have e18 : A18 = A17.updateRow 6 (A17 6 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A17 7) := by
    rw [h18, h17]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d18 : A18.det = A17.det := by
    rw [e18, Matrix.det_updateRow_add_smul_self A17 (by decide : ((6 : Fin 10) ≠ 7)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A19 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h19
  have e19 : A19 = A18.updateRow 7 (A18 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A18 6) := by
    rw [h19, h18]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d19 : A19.det = A18.det := by
    rw [e19, Matrix.det_updateRow_add_smul_self A18 (by decide : ((7 : Fin 10) ≠ 6)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A20 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h20
  have e20 : A20 = A19.updateRow 6 (A19 6 + ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A19 8) := by
    rw [h20, h19]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d20 : A20.det = A19.det := by
    rw [e20, Matrix.det_updateRow_add_smul_self A19 (by decide : ((6 : Fin 10) ≠ 8)) ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A21 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h21
  have e21 : A21 = A20.updateRow 8 (A20 8 + ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A20 6) := by
    rw [h21, h20]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d21 : A21.det = A20.det := by
    rw [e21, Matrix.det_updateRow_add_smul_self A20 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A22 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 10 * Polynomial.X + 23 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h22
  have e22 : A22 = A21.updateRow 9 (A21 9 + ((1 : Polynomial ℤ) - 4 * Polynomial.X + 7 * Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A21 6) := by
    rw [h22, h21]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d22 : A22.det = A21.det := by
    rw [e22, Matrix.det_updateRow_add_smul_self A21 (by decide : ((9 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - 4 * Polynomial.X + 7 * Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  set A23 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h23
  have e23 : A23 = A22.updateRow 9 (A22 9 + ((-1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A22 7) := by
    rw [h23, h22]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d23 : A23.det = A22.det := by
    rw [e23, Matrix.det_updateRow_add_smul_self A22 (by decide : ((9 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A24 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 8 * Polynomial.X ^ 2 + 17 * Polynomial.X ^ 3 - 15 * Polynomial.X ^ 4 + 6 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((2 : Polynomial ℤ) - 12 * Polynomial.X + 33 * Polynomial.X ^ 2 - 50 * Polynomial.X ^ 3 + 43 * Polynomial.X ^ 4 - 23 * Polynomial.X ^ 5 + 7 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h24
  have e24 : A24 = A23.updateRow 7 (A23 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A23 9) := by
    rw [h24, h23]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d24 : A24.det = A23.det := by
    rw [e24, Matrix.det_updateRow_add_smul_self A23 (by decide : ((7 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A25 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h25
  have e25 : A25 = A24.updateRow 7 (A24 7 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A24 9) := by
    rw [h25, h24]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d25 : A25.det = A24.det := by
    rw [e25, Matrix.det_updateRow_add_smul_self A24 (by decide : ((7 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A26 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 8 * Polynomial.X ^ 2 - 17 * Polynomial.X ^ 3 + 15 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ), ((-2 : Polynomial ℤ) + 12 * Polynomial.X - 33 * Polynomial.X ^ 2 + 50 * Polynomial.X ^ 3 - 43 * Polynomial.X ^ 4 + 23 * Polynomial.X ^ 5 - 7 * Polynomial.X ^ 6 + Polynomial.X ^ 7 : Polynomial ℤ)]
  ] with h26
  have e26 : A26 = A25.updateRow 9 (A25 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A25 7) := by
    rw [h26, h25]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d26 : A26.det = A25.det := by
    rw [e26, Matrix.det_updateRow_add_smul_self A25 (by decide : ((9 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A27 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h27
  have e27 : A27 = A26.updateRow 9 (A26 9 + ((1 : Polynomial ℤ) - 7 * Polynomial.X + 10 * Polynomial.X ^ 2 - 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A26 8) := by
    rw [h27, h26]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d27 : A27.det = A26.det := by
    rw [e27, Matrix.det_updateRow_add_smul_self A26 (by decide : ((9 : Fin 10) ≠ 8)) ((1 : Polynomial ℤ) - 7 * Polynomial.X + 10 * Polynomial.X ^ 2 - 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  set A28 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h28
  have e28 : A28 = A27.updateRow 8 (A27 8 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A27 9) := by
    rw [h28, h27]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d28 : A28.det = A27.det := by
    rw [e28, Matrix.det_updateRow_add_smul_self A27 (by decide : ((8 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A29 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h29
  have e29 : A29 = A28.updateRow 8 (A28 8 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A28 9) := by
    rw [h29, h28]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d29 : A29.det = A28.det := by
    rw [e29, Matrix.det_updateRow_add_smul_self A28 (by decide : ((8 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A30 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h30
  have e30 : A30 = A29.updateRow 9 (A29 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A29 8) := by
    rw [h30, h29]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d30 : A30.det = A29.det := by
    rw [e30, Matrix.det_updateRow_add_smul_self A29 (by decide : ((9 : Fin 10) ≠ 8)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  have hchain : A30.det = A0.det := by
    rw [d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hT : A30.BlockTriangular id := by
    intro i j hij
    rw [h30]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
  have hdiag : (∏ i, A30 i i) = Polynomial.X ^ 5 := by
    rw [h30]
    simp only [Fin.prod_univ_succ, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    have htail : ∀ g : Fin 0 → Polynomial ℤ, (∏ i, g i) = 1 := fun g =>
      Finset.prod_eq_one (fun x _ => Fin.elim0 x)
    rw [htail _]
    ring
  rw [← hchain, Matrix.det_of_upperTriangular hT, hdiag]


/-! ## 5. Slice knots

A knot K is (smoothly) slice if it bounds a smooth properly embedded
disk D² in the 4-ball B⁴.

A knot is topologically slice if it bounds a locally flat topologically
embedded disk in B⁴.
-/

def IsSmoothlySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ smooth), ∂D = K
  -- Reference: Fox & Milnor (1966), Singularities of 2-spheres in 4-space
  -- Mathlib prerequisites:
  --   1. Smooth manifolds (partial: Mathlib has manifolds, not smooth embeddings D²→B⁴)
  --   2. 4-ball (not in Mathlib)
  --   3. Properly embedded surfaces (not in Mathlib)

def IsTopologicallySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ locally flat), ∂D = K
  -- Mathlib prerequisites: same as smoothly slice + topological manifold theory

/-! ## 6. Piccirillo's theorem (statement only)

The Conway knot is NOT smoothly slice. This was proved by Lisa Piccirillo
in 2018 (published Annals of Mathematics 2020). She was a graduate student
at the time and solved it in under a week.

Strategy (cf. "Getting a handle on the Conway knot", AMS Bulletin 2022):
1. Construct a knot K* that has the same trace as the Conway knot
   (the trace X_K is the 4-manifold obtained by attaching a 2-handle
   to B⁴ along K with 0-framing)
2. Show K* is NOT smoothly slice (via Rasmussen's s-invariant,
   computed from Khovanov homology)
3. By the trace embedding lemma: if Conway is smoothly slice,
   then K* is smoothly slice → contradiction

This is a **magnificent** proof strategy — attacking the problem indirectly
by finding a "companion" knot that shares the same trace.
-/

/-- Piccirillo's theorem: the Conway knot is not smoothly slice. -/
theorem conway_not_smoothly_slice : ¬ IsSmoothlySlice conwayKnot := by
  exact sorry
  -- Reference: Piccirillo (2018), arXiv:1808.02923
  -- Published: Annals of Mathematics 191(2), 2020
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/
  --
  -- Proof infrastructure needed:
  --   1. Trace X_K of a knot (4-manifold from 0-framed 2-handle)
  --   2. Trace embedding lemma (if K slice ↔ ∂D = K → X_K embeds in B⁴)
  --   3. Piccirillo's companion knot K* with same trace as Conway
  --   4. Rasmussen s-invariant of K* ≠ 0 → K* not slice
  --   5. Khovanov homology (computes s-invariant)
  --
  -- Mathlib prerequisites (ALL missing):
  --   - 4-manifolds, handle decompositions, Kirby calculus
  --   - Khovanov homology
  --   - Rasmussen s-invariant
  --   - Smooth vs topological embeddings
  --   - Freedman's surgery theorem (for topological slice)
  --
  -- Estimated difficulty: **decades** away from formalization in Lean.
  -- This sorry is effectively permanent.

/-! ## 7. Freedman's theorem (statement only)

The Conway knot IS topologically slice, because it has trivial
Alexander polynomial. This is a consequence of Freedman's 1982 theorem:
every knot with trivial Alexander polynomial is topologically slice.
-/

theorem conway_topologically_slice : IsTopologicallySlice conwayKnot := by
  exact sorry
  -- Reference: Freedman (1982), The topology of four-dimensional manifolds
  -- Published: Journal of Differential Geometry 17(3)
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_topologically_slice/
  --
  -- Proof infrastructure needed:
  --   1. Freedman's full topological surgery machinery in dimension 4
  --   2. Disk embedding theorem
  --   3. Topological h-cobordism theorem
  --
  -- Mathlib prerequisites: essentially ALL of topological 4-manifold theory
  -- This sorry is effectively permanent.

/-! ## 8. The dichotomy

Together, Piccirillo + Freedman give:
  Conway knot: topologically slice BUT NOT smoothly slice.

This is the first explicit example of the smooth/topological dichotomy
for a named knot. It illustrates that smooth structures in dimension 4
are genuinely more restrictive than topological ones.
-/

/-- The Conway knot exhibits the smooth/topological dichotomy:
it is topologically slice but not smoothly slice. -/
theorem conway_dichotomy :
    IsTopologicallySlice conwayKnot ∧ ¬ IsSmoothlySlice conwayKnot := by
  exact ⟨conway_topologically_slice, conway_not_smoothly_slice⟩

end Knots_en
