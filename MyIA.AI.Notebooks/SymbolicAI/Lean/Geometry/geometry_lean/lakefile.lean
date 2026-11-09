import Lake
open Lake DSL

package «geometry_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

-- Lake companion de la serie Geometry (SymbolicAI/Lean/Geometry/, EPIC #18601
-- volet B) : chaque notebook Python de concept (01 figure vers equation, 02
-- Groebner, 03 Wu, 03b Ritt) recevra un module qui formalise ce que
-- l'algorithme Python calcule. Le lac ne remplace pas sympy : il en formalise
-- la semantique. Premier theorème : le milieu de l'hypotenuse (fil rouge de la
-- serie Python, position 05 du programme #17544).

@[default_target]
lean_lib «Geometry» where
  -- `.submodules `Geometry` couvre les Geometry.* (modules FR puis leurs
  -- siblings `_en` le jour ou l'audience externe les justifie, pattern #4980).
  globs := #[.submodules `Geometry]
