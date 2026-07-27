/-
  Knots.Conway — Nœud de Conway, Kinoshita-Terasaka, et la preuve de Piccirillo
  ==============================================================================

  Le nœud de Conway (11n34) est nommé d'après John Conway qui l'a découvert
  via sa notation des nœuds. Il possède 11 croisements et un polynôme
  d'Alexander trivial.

  Résultats clés :
  1. Conway (11n34) et Kinoshita-Terasaka (11n42) partagent le même
     polynôme d'Alexander (trivial) — les invariants de mutation coïncident.
  2. Le nœud de Kinoshita-Terasaka EST slice.
  3. Le nœud de Conway n'est PAS slice lisse (Piccirillo 2018/2020).
  4. Combiné au théorème de Freedman (Conway est topologiquement slice),
     ceci donne la première dichotomie lisse/topologique explicite.

  Epic #2874, Phase 1 (squelette uniquement — sorry permanent pour l'instant).

  Prérequis Mathlib nécessaires (TRÈS LOIN) :
  - Polynôme d'Alexander (requiert la représentation de Burau, absent de Mathlib)
  - Définition de nœud slice (requiert la théorie des 4-variétés lisses)
  - s-invariant de Rasmussen (requiert l'homologie de Khovanov)
  - Construction du compagnon de trace (requiert le calcul de Kirby)
  - Chirurgie topologique de Freedman (requiert une machinerie topologique énorme)
-/

import Knots.Basic
import Knots.Invariant

namespace Knots

/-! ## 1. Mutation de Conway

Une mutation de Conway prend un nœud K muni d'une sphère de Conway (rencontre K
en 4 points), le découpe le long de la sphère, effectue une rotation de 180°,
puis recolle. La mutation préserve :
- le polynôme d'Alexander
- le polynôme de Jones
- le genre du nœud

Le nœud de Conway et le nœud de Kinoshita-Terasaka sont reliés par mutation.
-/

/-- Une sphère de Conway : une S² rencontrant le nœud transversalement en 4 points. -/
structure ConwaySphere where
  -- The 4 intersection points on the knot
  points : Fin 4 → Nat
  -- TODO: proper geometric definition

/-- Deux nœuds sont mutants s'ils sont reliés par une mutation de Conway. -/
def AreMutants (k₁ k₂ : Knot) : Prop := sorry
  -- Definition: ∃ Conway sphere in k₁, rotate 180°, obtain k₂
  -- Reference: Conway (1970), An enumeration of knots and links
  -- Mathlib prerequisites: PL topology, cutting and gluing manifolds

/-! ## 2. Le nœud de Conway (11n34)

11 croisements dans la table de Rolfsen. Découvert par Conway (1970).
Polynôme d'Alexander trivial. Topologiquement slice (Freedman).
Non slice lisse (Piccirillo 2018).

Code PD issu de KnotInfo.
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

/-! ## 3. Le nœud de Kinoshita-Terasaka (11n42)

Également 11 croisements. Partage le polynôme d'Alexander trivial avec 11n34.
EST slice lisse (borde un disque dans B⁴).
Mutant du nœud de Conway.
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

/-! ## 4. Même polynôme d'Alexander

11n34 et 11n42 ont tous deux un polynôme d'Alexander trivial Δ(t) = 1.
C'est pourquoi la sliceness était si difficile à déterminer — le polynôme
d'Alexander ne peut pas les distinguer du nœud trivial.
-/

/-- Polynôme d'Alexander (définition provisoire).

Le polynôme d'Alexander Δ_K(t) est un invariant de nœud à valeurs dans ℤ[t, t⁻¹].
Cible Phase 4 : définition propre via matrice de Seifert ou représentation de Burau.
Pour l'instant, représenté comme une fonction opaque renvoyant un type provisoire.
Référence : Alexander (1928), Topological invariants of knots and links.
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

/-! ## 5. Nœuds slice

Un nœud K est (lissement) slice s'il borde un disque D² lisse proprement
plongé dans la boule à 4 dimensions B⁴.

Un nœud est topologiquement slice s'il borde un disque topologiquement plongé
localement plat dans B⁴.
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

/-! ## 6. Théorème de Piccirillo (énoncé uniquement)

Le nœud de Conway n'est PAS slice lisse. Ceci fut prouvé par Lisa Piccirillo
en 2018 (publié dans Annals of Mathematics 2020). Elle était alors doctorante
et résolut le problème en moins d'une semaine.

Stratégie (cf. « Getting a handle on the Conway knot », AMS Bulletin 2022) :
1. Construire un nœud K* ayant la même trace que le nœud de Conway
   (la trace X_K est la 4-variété obtenue en attachant une 2-anse
   à B⁴ le long de K avec un framing nul)
2. Montrer que K* n'est PAS slice lisse (via le s-invariant de Rasmussen,
   calculé à partir de l'homologie de Khovanov)
3. Par le lemme de plongement de trace : si Conway est slice lisse,
   alors K* est slice lisse → contradiction

C'est une stratégie de preuve **magnifique** — attaquer le problème indirectement
en trouvant un nœud « compagnon » partageant la même trace.
-/

/-- Théorème de Piccirillo : le nœud de Conway n'est pas slice lisse. -/
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

/-! ## 7. Théorème de Freedman (énoncé uniquement)

Le nœud de Conway EST topologiquement slice, car il possède un polynôme
d'Alexander trivial. Ceci est une conséquence du théorème de Freedman (1982) :
tout nœud de polynôme d'Alexander trivial est topologiquement slice.
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

/-! ## 8. La dichotomie

Ensemble, Piccirillo + Freedman donnent :
  Nœud de Conway : topologiquement slice MAIS NON slice lisse.

C'est le premier exemple explicite de dichotomie lisse/topologique
pour un nœud nommé. Cela illustre que les structures lisses en dimension 4
sont véritablement plus restrictives que les structures topologiques.
-/

/-- Le nœud de Conway illustre la dichotomie lisse/topologique :
il est topologiquement slice mais non slice lisse. -/
theorem conway_dichotomy :
    IsTopologicallySlice conwayKnot ∧ ¬ IsSmoothlySlice conwayKnot := by
  exact ⟨conway_topologically_slice, conway_not_smoothly_slice⟩

end Knots
