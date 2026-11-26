import Lake
open Lake DSL

package «gkdim» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «GKdim» where
  -- `.submodules `GKdim` couvre les sous-modules (FR + siblings _en) ; les
  -- agregateurs RACINES (`GKdim` FR et `GKdim_en` EN) doivent etre globbes
  -- explicitement -- `.submodules` nu ne matche que les sous-modules
  -- (pattern #6585 / #4980). Les DEUX racines sont globbees (memes formes
  -- que formal_groups_lean, #14784).
  globs := #[.submodules `GKdim, `GKdim, `GKdim_en]
