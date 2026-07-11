/-
  Knots.MathlibPrerequisites — Index of missing Mathlib infrastructure
  =====================================================================

  This file documents the Mathlib prerequisites needed to resolve each sorry
  in the knot_lean project. It serves as a roadmap for what would need to
  be built (either in Mathlib or as external dependencies) to formalize
  knot theory results.

  Epic #2874, Phase 1.

  Convention: organized by difficulty tier.

---

`Knots.MathlibPrerequisites` — index de l'infrastructure Mathlib manquante.

Ce fichier documente les prérequis Mathlib nécessaires pour résoudre
chaque `sorry` du projet `knot_lean`. Il sert de feuille de route pour
ce qui devrait être construit (soit dans Mathlib, soit comme
dépendances externes) pour formaliser les résultats de théorie des
nœuds.

EPIC #2874, Phase 1.

Convention : organisé par palier de difficulté.

i18n : extension bilingue FR/EN inline du sous-module (cf c.373
`Knots.lean` racine pour le pattern d'agrégateur bilingue). La
section anglaise ci-dessus est préservée verbatim ; la section
française est ajoutée en miroir pour la convention #4980 ratifiée
2026-07-04.
-/

namespace Knots.MathlibPrerequisites

/-! ## Tier 1: Accessible (Phase 2 targets, no deep prerequisites)

These could be proved with current Mathlib once the definitions are
properly set up.
-/

/-- #1: Well-formedness of PD-codes
Each edge appears exactly twice across all crossings.
Mathlib has: List, Finset, Fintype, counting
Needed: proper edge-index extraction from PDCrossing
-/
theorem pd_wellformed_prerequisites : True := trivial

/-- #2: Trefoil is tricolorable
Assign red/blue/green cyclically to 3 strands.
Mathlib has: Fin n → TriColor, decidable equality
Needed: proper edge indexing, crossing→edge mapping
-/
theorem trefoil_tricolorable_prerequisites : True := trivial

/-- #3: Unknot is not tricolorable
0-crossing diagram → only 1 edge → can't use ≥2 colors.
Mathlib has: everything needed
Needed: proper edge indexing
-/
theorem unknot_not_tricolorable_prerequisites : True := trivial

/-- #4: Tricolorability invariant under R1, R2, R3
Check each move case by case.
Mathlib has: propositional logic, Fin types
Needed: formal descriptions of each move's effect on edges
-/
theorem tricolorable_invariant_prerequisites : True := trivial

/-! ## Tier 2: Moderate (Phase 3–4 targets)

These need some infrastructure that doesn't exist yet but is
plausible to build.
-/

/-- #5: Reidemeister moves (formal description)
Need a precise combinatorial description of each move's
effect on PD-codes. Possible but tedious.
Reference: shua/leanknot has a partial formalization.
-/
theorem reidemeister_formal_prerequisites : True := trivial

/-- #6: Alexander polynomial
Via Burau representation or Fox calculus.
Mathlib has: Polynomial ℤ, matrices, free groups (partial)
Needed: Fox free differential calculus, Burau representation
Reference: Alexander (1928), Crowell & Fox (1963)
-/
theorem alexander_polynomial_prerequisites : True := trivial

/-- #7: Jones polynomial via Kauffman bracket
The Kauffman bracket is a state sum model.
Mathlib has: Polynomial, sums over finite types
Needed: Kauffman bracket state model, writhe normalization
Reference: Jones (1985), Kauffman (1987)
-/
theorem jones_polynomial_prerequisites : True := trivial

/-! ## Tier 3: Deep (Phase 5+, effectively permanent sorry)

These require infrastructure that is **far** beyond current Mathlib
and represents major research projects in formalization.
-/

/-- #8: Ambient isotopy ↔ Reidemeister equivalence
THE fundamental theorem of knot theory.
Needs: PL topology, general position, Alexander's theorem
Reference: Reidemeister (1927), Alexander (1928)
Timeline: years to decades
-/
theorem reidemeister_theorem_prerequisites : True := trivial

/-- #9: Piccirillo's theorem (Conway not smoothly slice)
Needs:
  - 4-manifold topology (handle decompositions, Kirby calculus)
  - Khovanov homology
  - Rasmussen s-invariant
  - Trace embedding lemma
Reference: Piccirillo (2018), arXiv:1808.02923
Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/
Timeline: decades
-/
theorem piccirillo_prerequisites : True := trivial

/-- #10: Lidman's theorem (unknotting number of 11n102 = 2)
Needs:
  - Montesinos trick (branched double covers)
  - Seifert fibered spaces
  - Heegaard Floer homology (d-invariants, HFred)
  - Ni-Wu formula for cosmetic surgeries
  - Gainullin's mapping cone formula
Reference: Lidman (2026), arXiv:2606.12431
Timeline: decades
-/
theorem lidman_prerequisites : True := trivial

/-- #11: Freedman's theorem (Conway topologically slice)
Needs:
  - Topological surgery in dimension 4
  - Disk embedding theorem
  - Topological h-cobordism theorem
Reference: Freedman (1982), J. Differential Geom.
Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_topologically_slice/
Timeline: decades
-/
theorem freedman_prerequisites : True := trivial

end Knots.MathlibPrerequisites
