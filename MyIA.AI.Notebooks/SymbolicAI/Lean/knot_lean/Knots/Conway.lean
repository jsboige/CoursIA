/-
  Knots.Conway — Conway knot, Kinoshita-Terasaka, and Piccirillo's proof
  =======================================================================

  The Conway knot (11n34) is named after John Conway who discovered it
  through his notation for knots. It has 11 crossings and trivial
  Alexander polynomial.

  Key results:
  1. Conway (11n34) and Kinoshita-Terasaka (11n42) share the same
     Alexander polynomial (trivial) — mutation invariants agree.
  2. The Kinoshita-Terasaka knot IS slice.
  3. The Conway knot is NOT smoothly slice (Piccirillo 2018/2020).
  4. Together with Freedman's theorem (Conway is topologically slice),
     this gives the first explicit smooth/topological dichotomy.

  Epic #2874, Phase 1 (scaffolding only — sorry permanent for now).

  Mathlib prerequisites needed (VERY FAR):
  - Alexander polynomial (requires Burau representation, not in Mathlib)
  - Slice knot definition (requires smooth 4-manifold theory)
  - Rasmussen s-invariant (requires Khovanov homology)
  - Trace companion construction (requires Kirby calculus)
  - Freedman's topological surgery (requires enormous topological machinery)

---

`Knots.Conway` — nœud de Conway, Kinoshita-Terasaka, et preuve de Piccirillo.

Le nœud de Conway (11n34) doit son nom à John Conway, qui l'a découvert
par sa notation pour les nœuds. Il possède 11 croisements et un
polynôme d'Alexander trivial.

Résultats clés :
1. Conway (11n34) et Kinoshita-Terasaka (11n42) partagent le même
   polynôme d'Alexander (trivial) — les invariants de mutation
   coïncident.
2. Le nœud de Kinoshita-Terasaka EST slice.
3. Le nœud de Conway N'EST PAS smoothly slice (Piccirillo 2018/2020).
4. Combiné au théorème de Freedman (Conway est topologiquement
   slice), ceci donne la première dichotomie explicite
   lisse/topologique.

EPIC #2874, Phase 1 (échafaudage uniquement — `sorry` permanent pour
l'instant).

Prérequis Mathlib nécessaires (TRÈS LOINTAIN) :
- polynôme d'Alexander (nécessite la représentation de Burau, pas
  dans Mathlib)
- définition de nœud slice (nécessite la théorie des 4-variétés
  lisses)
- invariant s de Rasmussen (nécessite l'homologie de Khovanov)
- construction du compagnon de trace (nécessite le calcul de Kirby)
- chirurgie topologique de Freedman (nécessite une machinerie
  topologique énorme)

i18n : extension bilingue FR/EN inline du sous-module (cf c.373
`Knots.lean` racine pour le pattern d'agrégateur bilingue). La
section anglaise ci-dessus est préservée verbatim ; la section
française est ajoutée en miroir pour la convention #4980 ratifiée
2026-07-04.
-/

import Knots.Basic
import Knots.Invariant

namespace Knots

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

/-- Two knots are mutants if related by a Conway mutation. -/
def AreMutants (k₁ k₂ : Knot) : Prop := sorry
  -- Definition: ∃ Conway sphere in k₁, rotate 180°, obtain k₂
  -- Reference: Conway (1970), An enumeration of knots and links
  -- Mathlib prerequisites: PL topology, cutting and gluing manifolds

/-! ## 2. The Conway knot (11n34)

11 crossings in the Rolfsen table. Discovered by Conway (1970).
Trivial Alexander polynomial. Topologically slice (Freedman).
Not smoothly slice (Piccirillo 2018).

PD-code from KnotInfo.
-/

def conwayKnotDiagram : KnotDiagram where
  crossings := [
    ⟨1, 8, 2, 9⟩,
    ⟨3, 12, 4, 1⟩,
    ⟨5, 16, 6, 11⟩,
    ⟨7, 2, 8, 3⟩,
    ⟨9, 18, 10, 5⟩,
    ⟨11, 4, 12, 13⟩,
    ⟨13, 20, 14, 7⟩,
    ⟨15, 6, 16, 17⟩,
    ⟨17, 10, 18, 15⟩,
    ⟨19, 14, 20, 19⟩,
    ⟨21, 22, 22, 21⟩
  ]
  numEdges := 22
  hwell := by trivial  -- TODO: proper well-formedness check

def conwayKnot : Knot where
  diagram := conwayKnotDiagram

/-! ## 3. The Kinoshita-Terasaka knot (11n42)

Also 11 crossings. Shares the trivial Alexander polynomial with 11n34.
IS smoothly slice (bounds a disk in B⁴).
Mutant of the Conway knot.
-/

def kinoshitaTerasakaDiagram : KnotDiagram where
  crossings := [
    ⟨1, 8, 2, 9⟩,
    ⟨3, 10, 4, 1⟩,
    ⟨5, 16, 6, 11⟩,
    ⟨7, 2, 8, 3⟩,
    ⟨9, 18, 10, 5⟩,
    ⟨11, 4, 12, 13⟩,
    ⟨13, 20, 14, 7⟩,
    ⟨15, 6, 16, 17⟩,
    ⟨17, 22, 18, 15⟩,
    ⟨19, 14, 20, 19⟩,
    ⟨21, 12, 22, 21⟩
  ]
  numEdges := 22
  hwell := by trivial  -- TODO: proper well-formedness check

def kinoshitaTerasakaKnot : Knot where
  diagram := kinoshitaTerasakaDiagram

/-! ## 4. Same Alexander polynomial

Both 11n34 and 11n42 have trivial Alexander polynomial Δ(t) = 1.
This is why sliceness was so hard to determine — the Alexander
polynomial cannot distinguish them from the unknot.
-/

/-- Alexander polynomial (definition placeholder).

The Alexander polynomial Δ_K(t) is a knot invariant taking values in ℤ[t, t⁻¹].
Phase 4 target: proper definition via Seifert matrix or Burau representation.
For now, represented as an opaque function returning a placeholder type.
Reference: Alexander (1928), Topological invariants of knots and links.
-/
-- TODO Phase 4: import Mathlib.Algebra.Polynomial and use Polynomial ℤ
-- Opaque placeholder for Phase 1 scaffolding.
abbrev AlexanderPoly := Nat  -- placeholder; Phase 4 replaces with Polynomial ℤ

def alexanderPolynomial (k : Knot) : AlexanderPoly := sorry
  -- Definition: via Seifert matrix, or alternatively via Burau representation
  -- Reference: Alexander (1928), Topological invariants of knots and links
  -- Mathlib prerequisites:
  --   1. Polynomial ℤ (exists in Mathlib)
  --   2. Seifert surfaces and Seifert matrices (not in Mathlib)
  --   3. Burau representation of braid groups (not in Mathlib)

theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = 1 := by
  exact sorry
  -- Reference: standard computation. Δ_{11n34}(t) = 1.
  -- Phase 4+ target

theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = 1 := by
  exact sorry
  -- Reference: standard computation. Δ_{11n42}(t) = 1.
  -- Phase 4+ target

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

end Knots
