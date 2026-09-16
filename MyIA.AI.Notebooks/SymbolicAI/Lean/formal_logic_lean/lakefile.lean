import Lake
open Lake DSL

-- Pont Tweety <-> Lean et logique de prouvabilité (EPIC #15066).
-- Consomme Foundation et ProvabilityLogic en CONSUMER_PINNE (pilotes #15520 et #15916) :
-- aucun module upstream n'est vendu ou adapté dans CoursIA, les imports sont épinglés exactement.
package «formal_logic_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

require «Foundation» from git
  "https://github.com/FormalizedFormalLogic/Foundation.git" @ "81810b9f22c49fbb32bd89c1e9737059d83a37e6"

require «ProvabilityLogic» from git
  "https://github.com/FormalizedFormalLogic/ProvabilityLogic.git" @ "01628c51f618fd11f2f6b10c813f261f1d36c7a6"

@[default_target]
lean_lib «FormalLogic» where
  globs := #[.submodules `FormalLogic]
