import Lake
open Lake DSL

-- Pont Tweety <-> Lean (EPIC #15066, Tranche A, issue #15521).
-- Consomme la bibliothèque Formalized Formal Logic en CONSUMER_PINNE (verdict pilote #15520) :
-- aucun module FFL n'est vendu ou adapte dans CoursIA, on importe l'upstream au pin exact.
package «formal_logic_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

require foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation.git" @ "81810b9f22c49fbb32bd89c1e9737059d83a37e6"

@[default_target]
lean_lib «FormalLogic» where
  globs := #[.submodules `FormalLogic]
