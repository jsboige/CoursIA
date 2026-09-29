import Lake
open Lake DSL

-- Pont Tweety <-> Lean et logique de prouvabilité (EPIC #15066).
-- Consomme Foundation et ProvabilityLogic en CONSUMER_PINNE (pilotes #15520 et #15916) :
-- aucun module upstream n'est vendu ou adapté dans CoursIA, les imports sont épinglés exactement.
package «formal_logic_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «Foundation» from git
  "https://github.com/FormalizedFormalLogic/Foundation.git" @ "81810b9f22c49fbb32bd89c1e9737059d83a37e6"

require «ProvabilityLogic» from git
  "https://github.com/FormalizedFormalLogic/ProvabilityLogic.git" @ "01628c51f618fd11f2f6b10c813f261f1d36c7a6"

-- Pilote d'integration ModalLogic (tranche C #15066) : upstream reste en Lean 4.31.0
-- (origin/main mesure au 2026-09-20, aucune branche/PR de compat), notre lake reste en toolchain 4.33.1.
-- Consomme donc le fork MyIntelligenceAgency/ModalLogic = upstream 9c485ca95e35 + 3 commits de
-- compat 4.33.1 (dsimp->simp sur 2 preuves ; restauration des instances HasSubset Set/Finset
-- retirees de mathlib v4.33.1 ; fermeture de setOf_iff apres deprecation de setOf) — aucun
-- changement semantique, diff public sur le fork.
-- NB : `require mathlib` reste en DERNIER (message de `lake exe cache get`) pour que les revs
-- transitives (plausible, batteries, Qq, proofwidgets) soient celles de mathlib v4.33.1 et non
-- celles du manifest 4.31 de ModalLogic.
require «ModalLogic» from git
  "https://github.com/MyIntelligenceAgency/ModalLogic.git" @ "71968137b917a708c700047e1e6d3eb6cc4ed078"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «FormalLogic» where
  globs := #[.submodules `FormalLogic]
