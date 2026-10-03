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


end Knots_en
