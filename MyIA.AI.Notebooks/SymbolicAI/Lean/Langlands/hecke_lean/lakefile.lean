import Lake
open Lake DSL

package «hecke» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «Hecke» where
  -- Port pédagogique de anthropics/fermats-last-theorem,
  -- Definitions/Def_ModularForm_HeckeOperator.lean (commit aa2d8b34692b),
  -- Apache-2.0 préservée (voir NOTICE.md). Cible #14773 : Lean v4.33.0.
  -- `.submodules `Hecke` couvre les sous-modules (FR + siblings _en) ; les
  -- agrégateurs RACINES (`Hecke` FR et `Hecke_en` EN) doivent être globbés
  -- explicitement — `.submodules` nu ne matche que les sous-modules,
  -- pattern #6585 / #4980. Les DEUX racines sont globbées (plus strict que
  -- sensitivity_lean : la racine FR y reste non-compilée).
  globs := #[.submodules `Hecke, `Hecke, `Hecke_en]
