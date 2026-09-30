import Lake
open Lake DSL

package «serre100» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «Serre100» where
  -- Tour guidé « Serre dans Mathlib » (grain 6, EPIC #16334). Mêmes pins que
  -- hecke_lean (v4.33.0 / mathlib db584cd6d46c) : les `.submodules `Serre100`
  -- couvrent les sous-modules FR + siblings `_en` ; les agrégateurs RACINES
  -- (`Serre100` FR et `Serre100_en` EN) sont globbés explicitement
  -- (pattern #6585 / #4980, cf. hecke_lean).
  globs := #[.submodules `Serre100, `Serre100, `Serre100_en]
