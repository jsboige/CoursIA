import Lake
open Lake DSL

package «social_choice» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- EPIC #4365 Phase-4 (PR #6058, c.357) : SocialChoice a ete absorbe byte-identique
-- dans `game_theory_lean/SocialChoice/`, qui est desormais le home canonique
-- (`@[default_target] lean_lib SocialChoice` dans game_theory_lean/lakefile.lean).
-- L'ancienne declaration `lean_lib «SocialChoice»` ci-dessous est NEUTRALISEE :
-- ses `globs` pointaient vers des modules dont les sources ont ete deplacees,
-- ce qui provoquait une collision de module-path (`SocialChoice: some modules
-- have bad imports`) sur le `lake -R build` de CE lake. Ce lake archive conserve
-- son `package`, son `require mathlib`, ses docs/manifest/NOTICE (coquille archive)
-- mais n'expose PLUS la lib entree en collision. La certification no-sorry
-- (Arrow/Sen/Framework/Basic) et le Lake build sont repris par game_theory_lean
-- via `.github/workflows/lean-social-choice.yml` (repointe, cf. commit).
-- -- @[default_target]
-- -- lean_lib «SocialChoice» where
-- --   globs := #[`SocialChoice.Arrow, `SocialChoice.Arrow_en, ... ]  (archive, voir git history)