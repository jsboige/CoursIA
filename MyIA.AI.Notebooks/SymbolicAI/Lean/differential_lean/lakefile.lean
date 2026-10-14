/-
  Enveloppe de visite — qinz1yang/differential-geometry
  =====================================================

  Ce projet declare le depot amont qinz1yang/differential-geometry comme
  dependance Lake, epinglee sur le tag de release v0.1.3
  (commit 7a48598d35109aa99d1cc678e2724c213cdf4ff3).

  Aucune source de l'amont n'est recopiee, aucun fork n'est fait : la surface
  est une dependance, exactement comme GameTheory/social_choice_lean_peters/
  (precedent du depot, meme forme).

  Le lake reste en Lean v4.33.1 alors que le parc CoursIA est en v4.33.0 :
  c'est une exception documentee, comme pour Peters — l'amont declare
  lui-meme `leanprover/lean4:v4.33.1` dans son lean-toolchain.

  Reference : https://github.com/qinz1yang/differential-geometry
  Licence   : Apache-2.0
  Issue     : #18205 (EPIC origami geometrie differentielle, Pli 1)
-/

import Lake
open Lake DSL

package «differential_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require DifferentialGeometry from git
  "https://github.com/qinz1yang/differential-geometry" @ "v0.1.3"

@[default_target]
lean_lib «DifferentialTour» where
  -- globs incluent le sibling EN (i18n #4980) pour que `lake build` l'elabore
  -- aussi : sans cela, DifferentialTour_en.lean n'est jamais compile et un
  -- Lean CI vert est un faux pass (orphan-trap #6749). Meme pattern que
  -- social_choice_lean_peters et sudoku_lean.
  globs := #[`DifferentialTour, `DifferentialTour_en]
