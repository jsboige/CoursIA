/-
  Knots.Slice — Nœuds slice, Piccirillo et la dichotomie lisse/topologique
  =======================================================================

  Extrait du monolithe `Knots/Conway.lean` en module dédié (issue #18397,
  tranche 1 / option B). Ce module est l'aboutissement didactique du lake :
  il consomme `conwayKnot` et le polynôme d'Alexander trivial établis dans
  `Knots.Conway`, et énonce la dichotomie slice lisse / slice topologique.

  Ordre de lecture du cours (cf `Knots.lean`) : Basic → Reidemeister →
  Invariant → Conway → **Slice** (ce fichier).

  Les 4 `sorry` de ce fichier sont des limites connues, pas des dettes :
  la théorie des 4-variétés (calculus de Kirby, homologie de Khovanov,
  s-invariant de Rasmussen, chirurgie de Freedman) est entièrement hors
  Mathlib. Chaque énoncé porte le détail de ses prérequis manquants.

  Epic #2874, Phase 1 (squelette uniquement).
  Convention i18n #4980 : jumeau EN = `Knots/Slice_en.lean`.
-/

import Knots.Conway

namespace Knots

/-! ## 1. Nœuds slice

Pourquoi cette section : la propriété « slice » est la question du côté
4-dimensionnel de la théorie des nœuds — elle ne se lit plus sur le
diagramme (contrairement au tricoloriage ou au polynôme d'Alexander),
mais sur l'existence d'un disque dans B⁴. C'est la notion qu'il faut
pour énoncer la dichotomie finale.

Un nœud K est (lissement) slice s'il borde un disque D² lisse proprement
plongé dans la boule à 4 dimensions B⁴.

Un nœud est topologiquement slice s'il borde un disque topologiquement plongé
localement plat dans B⁴.
-/

/-- Être lissement slice : borner un disque lisse proprement plongé dans B⁴. -/
def IsSmoothlySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ smooth), ∂D = K
  -- Reference: Fox & Milnor (1966), Singularities of 2-spheres in 4-space
  -- Mathlib prerequisites:
  --   1. Smooth manifolds (partial: Mathlib has manifolds, not smooth embeddings D²→B⁴)
  --   2. 4-ball (not in Mathlib)
  --   3. Properly embedded surfaces (not in Mathlib)
  --
  -- Digestion (#18397) : la définition elle-même est un `sorry` car
  -- l'énoncé quantifie sur des objets (plongements lisses D² → B⁴)
  -- que Mathlib ne sait pas encore nommer.

/-- Être topologiquement slice : borner un disque localement plat dans B⁴. -/
def IsTopologicallySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ locally flat), ∂D = K
  -- Mathlib prerequisites: same as smoothly slice + topological manifold theory
  --
  -- Digestion (#18397) : même raison — la notion « localement plat » et la
  -- catégorie TOP des 4-variétés n'existent pas en Mathlib.

/-! ## 2. Théorème de Piccirillo (énoncé uniquement)

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
  -- Ce que la preuve établit (#18397) : l'obstruction au disque lisse ne
  -- vient pas du diagramme de Conway mais de son compagnon de trace K*.
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

/-! ## 3. Théorème de Freedman (énoncé uniquement)

Le nœud de Conway EST topologiquement slice, car il possède un polynôme
d'Alexander trivial. Ceci est une conséquence du théorème de Freedman (1982) :
tout nœud de polynôme d'Alexander trivial est topologiquement slice.

Digestion (#18397) : c'est ici que le travail des sections précédentes
paie — le polynôme d'Alexander trivial de Conway (établi dans
`Knots.Conway`) est exactement l'hypothèse du théorème de Freedman.
-/

theorem conway_topologically_slice : IsTopologicallySlice conwayKnot := by
  -- Ce que la preuve établit (#18397) : Conway satisfait l'hypothèse
  -- « Alexander trivial » de Freedman, donc est slice topologique.
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

/-! ## 4. La dichotomie

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
  -- Seule preuve complète du fichier (#18397) : un recollement des deux
  -- bornes — Freedman fournit la composante de gauche, Piccirillo
  -- la négation de droite. Aucune ingrédient mathématique nouveau.
  exact ⟨conway_topologically_slice, conway_not_smoothly_slice⟩

end Knots
