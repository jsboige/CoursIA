/-
  Knots.Mutation — Conway mutation
  ================================

  A Conway mutation takes a knot K with a Conway sphere (meeting K in 4 points),
  cuts along the sphere, rotates by 180 degrees, and glues back. The mutation
  preserves the Alexander and Jones polynomials — the foundation of the
  Conway / Kinoshita-Terasaka pair (sections 2-3 of the historical monolith,
  now `Knots.ConwayPD`).

  Extracted from `Knots.Conway` (split #18397 tranche 2; tranche 1 = `Knots.Slice`
  in #18528). Epic #2874.
-/

/-
  English mirror of `Mutation.lean` (FR canonical, header mono-lingual EN).
  Convention EPIC #4980 : distinct FR + EN sibling files; body signatures,
  proofs, sorry markers, and tactics remain byte-identical between the two
  files (anti-§D byte-identity invariant).
-/

import Knots.Basic_en
import Knots.Reidemeister_en

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

/-! ### Sphere mutation: tangle rotation + boundary re-attachment

The bare window (`mutateWindow`) rotates label positions inside each
interior crossing — c130 measurement: not enough to relate the Conway/KT
census codes. The full sphere mutation adds the second half of the
geometric gesture: after the half-turn of the tangle, its **four boundary
points** re-attach to the four outside arcs in a permuted order. At the PD
level: every interior occurrence of a boundary label is rewritten by a
permutation σ of the boundary labels (each boundary label having exactly
one interior and one exterior occurrence, the image remains a twice-labeled
PD code as soon as σ is injective on its support).
-/


/-- Boundary re-attachment: inside window [i, j), every label is rewritten
by σ; outside the window, nothing moves. -/
def reattachWindow : List PDCrossing → Nat → Nat → (Nat → Nat) → List PDCrossing
  | [], _, _, _ => []
  | c :: cs', 0, 0, _ => c :: cs'
  | c :: cs', 0, j+1, σ => ⟨σ c.e1, σ c.e2, σ c.e3, σ c.e4⟩ :: reattachWindow cs' 0 j σ
  | c :: cs', _+1, 0, _ => c :: cs'
  | c :: cs', i+1, j+1, σ => c :: reattachWindow cs' i j σ

/-- Re-attachment preserves the number of crossings. -/
theorem reattachWindow_length (cs : List PDCrossing) (i j : Nat) (σ : Nat → Nat) :
    (reattachWindow cs i j σ).length = cs.length := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, _+1 => simp [reattachWindow, ih]
    | _+1, 0 => rfl
    | _+1, _+1 => simp [reattachWindow, ih]

/-- Empty window: re-attachment is the identity there, for any list. -/
theorem reattachWindow_zero_window (cs : List PDCrossing) (σ : Nat → Nat) :
    reattachWindow cs 0 0 σ = cs := by
  cases cs <;> rfl

/-- Re-attachment by the identity: no label is rewritten. -/
theorem reattachWindow_id (cs : List PDCrossing) (i j : Nat) :
    reattachWindow cs i j id = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 => simp only [reattachWindow, id_eq, ih 0 j]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, ih _ _]

/-- Re-attachment is involutive as soon as σ is (`σ ∘ σ = id` pointwise):
two successive re-attachments by the same involution give back the initial
list. This is the case of a genuine mutation — re-attachment is a half-turn
of the four-punctured sphere, hence a Klein group element. -/
theorem reattachWindow_involutive (cs : List PDCrossing) (i j : Nat) (σ : Nat → Nat)
    (hσ : ∀ x, σ (σ x) = x) :
    reattachWindow (reattachWindow cs i j σ) i j σ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [reattachWindow, hσ c.e1, hσ c.e2, hσ c.e3, hσ c.e4, ih 0 j]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, ih _ _]

/-- Klein rotation after re-attachment: permuting label positions then
rewriting their values = rewriting the values then permuting the positions. -/
theorem KleinRot.apply_reattach (ρ : KleinRot) (σ : Nat → Nat) (c : PDCrossing) :
    ρ.apply ⟨σ c.e1, σ c.e2, σ c.e3, σ c.e4⟩ =
      ⟨σ (ρ.apply c).e1, σ (ρ.apply c).e2, σ (ρ.apply c).e3, σ (ρ.apply c).e4⟩ := by
  cases ρ <;> rfl

/-- Rotation and re-attachment of the same window **commute**: ρ permutes
the label positions, σ rewrites their values. -/
theorem mutateWindow_reattachWindow_comm (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (σ : Nat → Nat) :
    mutateWindow (reattachWindow cs i j σ) i j ρ =
      reattachWindow (mutateWindow cs i j ρ) i j σ := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [reattachWindow, mutateWindow, ih 0 j, KleinRot.apply_reattach]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, mutateWindow, ih _ _]

/-- **Conway sphere mutation at the PD level**: Klein rotation ρ of the
crossings in window [i, j) (the interior tangle), then re-attachment of the
interior occurrences of the boundary labels by σ. Outside the window,
nothing changes. This is the complete combinatorial translation of the
cut / half-turn / reglue gesture. -/
def sphereMutate (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) (σ : Nat → Nat) :
    List PDCrossing :=
  reattachWindow (mutateWindow cs i j ρ) i j σ

/-- Sphere mutation preserves the number of crossings. -/
theorem sphereMutate_length (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (σ : Nat → Nat) :
    (sphereMutate cs i j ρ σ).length = cs.length := by
  rw [sphereMutate, reattachWindow_length, mutateWindow_length]

/-- Sphere mutation is **involutive** as soon as σ is involutive: mutating
twice the same sphere with the same rotation and the same re-attachment gives
back the initial diagram. This is the geometric gesture — two half-turns =
identity — and the reason why the mutation relation is symmetric. -/
theorem sphereMutate_involutive (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (σ : Nat → Nat) (hσ : ∀ x, σ (σ x) = x) :
    sphereMutate (sphereMutate cs i j ρ σ) i j ρ σ = cs := by
  simp only [sphereMutate]
  rw [mutateWindow_reattachWindow_comm, mutateWindow_involutive]
  exact reattachWindow_involutive cs i j σ hσ

/-- Two diagrams are **mutants at the bare-window level**: there exist a
window and a Klein rotation mapping the crossing list of one onto the other,
without re-attachment of the boundary points. This is the "tangle rotation"
half of the Conway gesture — the weaker notion, kept under its own name (it
is refuted at gadget depth ≤ 2 on the Conway/KT pair, cf. NOTE below). -/
def AreWindowMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot), mutateWindow d₁.crossings i j ρ = d₂.crossings

/-- Two diagrams are **mutants** if there exists a Conway sphere mutation —
cut along the sphere, perform a half-turn, reglue — mapping the crossing list
of one onto that of the other. The complete combinatorial translation
(`sphereMutate`): a window [i, j) (the interior tangle), a Klein rotation ρ
(the half-turn of the tangle, an element of the Klein group on the four
boundary points), and re-attachment of the boundary points by σ. The
re-attachment of a half-turn is itself of order ≤ 2 (the three half-turns of
the Klein group are involutions), hence the condition `σ ∘ σ = id` — without
it the relation would not be symmetric and would no longer represent the
Conway gesture. -/
def AreMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot) (σ : Nat → Nat),
    (∀ x, σ (σ x) = x) ∧ sphereMutate d₁.crossings i j ρ σ = d₂.crossings

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

Reflexivity: empty window, σ = id. Symmetry: involutivity of `mutateWindow`,
of the Klein rotation and of the re-attachment σ (`mutateWindow_involutive`,
`reattachWindow_involutive`, `sphereMutate_involutive` — every half-turn is
its own inverse). Transitivity is false in general for mutation (composing
two mutations on different windows is not a one-shot mutation) — this is NOT
an equivalence relation, and that is correct. -/
/- NOTE: no transitivity claimed — mutation composes rotations over
potentially different windows, which is not a one-shot rotation. -/

/-- Empty window: mutation is the identity there, for any list. -/
theorem mutateWindow_zero_window (cs : List PDCrossing) (ρ : KleinRot) :
    mutateWindow cs 0 0 ρ = cs := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem AreWindowMutantDiagrams.refl (d : KnotDiagram) : AreWindowMutantDiagrams d d :=
  ⟨0, 0, .id, mutateWindow_zero_window d.crossings .id⟩

theorem AreWindowMutantDiagrams.symm {d₁ d₂ : KnotDiagram}
    (h : AreWindowMutantDiagrams d₁ d₂) : AreWindowMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, hmut⟩ := h
  refine ⟨i, j, ρ, ?_⟩
  rw [← hmut]
  exact mutateWindow_involutive d₁.crossings i j ρ

theorem AreMutantDiagrams.refl (d : KnotDiagram) : AreMutantDiagrams d d :=
  ⟨0, 0, .id, id, fun _ => rfl, by
    rw [sphereMutate, mutateWindow_zero_window, reattachWindow_zero_window]⟩

theorem AreMutantDiagrams.symm {d₁ d₂ : KnotDiagram} (h : AreMutantDiagrams d₁ d₂) :
    AreMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, σ, hσ, hmut⟩ := h
  exact ⟨i, j, ρ, σ, hσ, by
    rw [← hmut]
    exact sphereMutate_involutive d₁.crossings i j ρ σ hσ⟩

theorem AreMutants.refl (k : Knot) : AreMutants k k :=
  ⟨k.diagram, k.diagram, ReidemeisterEquiv.refl k.diagram,
    ReidemeisterEquiv.refl k.diagram, AreMutantDiagrams.refl k.diagram⟩

theorem AreMutants.symm {k₁ k₂ : Knot} (h : AreMutants k₁ k₂) : AreMutants k₂ k₁ := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hmut⟩ := h
  exact ⟨d₂, d₁, hd₂, hd₁, AreMutantDiagrams.symm hmut⟩

/-! ### Controls: the definition discriminates

A definition catching neither a mutant pair nor a counterexample would be a
disguised `True` and removing the `sorry` would be cosmetic. Two controls:

- NEGATIVE (`not_areWindowMutantDiagrams_trefoil_unknot`,
  `not_areMutantDiagrams_trefoil_unknot`): mutation preserves the crossing
  count, so the trefoil (3 crossings) and the unknot (0) are not mutants —
  at the designated-diagram level.
- POSITIVE (`areWindowMutantDiagrams_trefoil_mutant`,
  `areMutantDiagrams_trefoil_mutant`): a non-trivial mutation (full window,
  r12 rotation) is captured by each definition.

NOTE (limit of the canonical witness): the designated diagrams
`conwayKnotDiagram` and `kinoshitaTerasakaDiagram` (corrected census PD
codes, cf. §2) share their first five crossings and differ at crossings 6
to 11 — no one-shot map superposes them.
NOTE updated (link 5, c165): the intermediate diagram is delivered — the
sphere mutant of the Conway census (`conwayMutantDiagram`) is a **redraw**
of the KT census (explicit reordering + renaming, cf. `Knots.Conway_en`
`conwayMutant_redraws_kinoshitaTerasaka`). The one-shot map remains
impossible on the designated diagrams; what remains is to formally relate
the redraw to `ReidemeisterEquiv` to close
`AreMutants conwayKnot kinoshitaTerasakaKnot` — later sub-grain.
NOTE update 2 (link 7): the obstruction is GRADED and measured (issue #2874,
comment c.6258386829 — exact-decision probes, controlled against the link-5
certificate). The one-shot pair WITHOUT reattachment σ does not exist at
gadget depth ≤ 2 either:
(a) 11 crossings: for every redraw of C (a reordering makes any window = any
subset of crossings realizable, and renaming commutes with slot rotation)
and every rotation ρ, no result is a redraw of K or M — 6 141 candidates, 0;
(b) 12 crossings: one connected R1 kink (`Reidemeister1Connected`, 44 cells
per base) on each side — 0 out of 46 230 pairs;
(c) 14 crossings: R1 then connected R2 (`Reidemeister2Connected` on the
doubled label of the kink) on each side — 0 out of 465 616 pairs.
The direct R2 family is empty to begin with: `Reidemeister2Connected`
requires a double arc (both occurrences of `a` in the same crossing), which
no crossing of C, K or M carries. Reading: a gadget adds crossings without
reconfiguring the boundary arcs of the window — the effect of σ (rewriting
boundary arcs, 8↔11 and 13↔22 in the census) stays out of reach at these
depths.
NOTE update 3 (link 8, 2bis — ai-01 arbitration of 2026-10-19, #2874
c.6261930038): the σ amendment is applied. `AreMutantDiagrams` now quantifies
over the full sphere mutation (`sphereMutate`: window + rotation ρ +
involution re-attachment σ), a form faithful to the cut / half-turn / reglue
gesture; the bare-window notion measured above keeps its own name
(`AreWindowMutantDiagrams`) and all its lemmas. The depth-0 witness (C, M)
under the new definition is `areMutantDiagrams_conway_conwayMutant`
(`Knots.Conway_en`, link 4): the pair requires no gadget at all, the single
sphere mutation of the census (window [5, 11), r13, re-attachment
(8 11)(13 22)) realizes it. What the bare window did not provide,
re-attachment does.
-/

/-- Negative control of the bare window: trefoil and unknot are not mutants
at the window level (rotation preserves the crossing count). -/
theorem not_areWindowMutantDiagrams_trefoil_unknot :
    ¬ AreWindowMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, hmut⟩
  have hlen := mutateWindow_length trefoilDiagram.crossings i j ρ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- Negative control: trefoil and unknot are not mutants (sphere mutation
preserves the crossing count). -/
theorem not_areMutantDiagrams_trefoil_unknot :
    ¬ AreMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, σ, _hσ, hmut⟩
  have hlen := sphereMutate_length trefoilDiagram.crossings i j ρ σ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- The trefoil mutant by r12 over the full window. -/
def trefoilMutantDiagram : KnotDiagram where
  crossings := mutateWindow trefoilDiagram.crossings 0 3 KleinRot.r12
  numEdges := 6

def trefoilMutant : Knot where
  diagram := trefoilMutantDiagram

/-- Positive control of the bare window: a non-trivial mutation (full
window, non-identity rotation) is captured by the definition. -/
theorem areWindowMutantDiagrams_trefoil_mutant :
    AreWindowMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, rfl⟩

/-- Positive control: the mutation definition catches a non-trivial mutation
(full window, r12 rotation, identity re-attachment). -/
theorem areMutantDiagrams_trefoil_mutant :
    AreMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, id, fun _ => rfl, by
    rw [sphereMutate, reattachWindow_id]
    rfl⟩

theorem areMutants_trefoil_mutant : AreMutants trefoil trefoilMutant :=
  ⟨trefoilDiagram, trefoilMutantDiagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_trefoil_mutant⟩


end Knots_en
