import Lake
open Lake DSL

package «formal_groups_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/- Pin Mathlib aligne sur l'ancrage FLT de #14773 (anthropics/fermats-last-theorem
@ aa2d8b34692b16c70f699536de0d8e75b9a3e9ef) : rev db584cd6d46c92f209a44c0f1c829460d327499d,
dont le lean-toolchain est v4.33.0 (celui de ce lake). Voir #14785. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «FormalGroups» where
  -- Port pedagogique de anthropics/fermats-last-theorem,
  -- Definitions/Def_MvFormalGroup_BasicV2.lean (commit aa2d8b34692b),
  -- Apache-2.0 preservee (voir NOTICE.md). Cible #14773 : Lean v4.33.0.
  -- `.submodules `FormalGroups` couvre les sous-modules (FR + siblings _en) ;
  -- les agregateurs RACINES (`FormalGroups` FR et `FormalGroups_en` EN)
  -- doivent etre globbes explicitement -- `.submodules` nu ne matche que
  -- les sous-modules, pattern #6585 / #4980. Les DEUX racines sont globbees
  -- (memes formes que hecke_lean, #14784).
  globs := #[.submodules `FormalGroups, `FormalGroups, `FormalGroups_en]
