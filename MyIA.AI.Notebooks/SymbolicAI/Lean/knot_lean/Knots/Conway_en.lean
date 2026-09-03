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
the normalized incarnation of Δ = 1. The proofs (10×10 kernel determinant
over ℤ[t]) remain `sorry`, on statements that are now true. -/
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

/-- Trivial Alexander polynomial of the Conway knot — classical content
Δ(t) = 1; under the designated normalization, the minor equals the unit
−t⁶ (§4 note arbitration settled: exact designated value). -/
theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = -(Polynomial.X ^ 6) := by
  exact sorry
  -- Target verified externally (census PD code spherogram 2.4.1, rotation
  -- (e2,e4)=over-strand; probe validated on 3_1/4_1/5_1): minor = -t^6, a unit.
  -- Proof: kernel determinant of the 10x10 sparse matrix over Z[t] -- follow-up tranche.

/-- Trivial Alexander polynomial of the Kinoshita-Terasaka knot — classical
content Δ(t) = 1; under the designated normalization, the minor equals the
unit t⁵. -/
theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = Polynomial.X ^ 5 := by
  exact sorry
  -- Target verified externally (same probe): minor = t^5, a unit.
  -- Proof: kernel determinant 10x10 -- follow-up tranche.

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
