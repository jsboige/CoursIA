import Lake
open Lake DSL

package «conway» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Conway» where
  -- Conway hommage: accessible formalizations of lesser-known results
  -- by John Horton Conway (1937-2020)
  --
  -- Convention i18n EPIC #4980 : `globs := #[`Conway.*]` (Glob.submodules) pour
  -- que `lake build` compile le root, TOUS les sous-modules FR, ET les siblings
  -- `_en` (`Conway.Doomsday_en`, `Conway.Angel_en`, ...). Sans ce glob, le defaut
  -- Lake (`roots.map Glob.one` = umbrella `Conway.lean` + imports transitifs
  -- seulement) laisse chaque `_en` ORPHELIN : l'umbrella FR ne les importe pas,
  -- rien d'autre ne les importe, et le scan sorry du CI reutilisable exclut
  -- `*_en.lean` (lean-build.yml L85, #6429) -> aucune etape ne les compilait.
  -- Green CI etait donc necessaire mais NON suffisant comme preuve de build d'un
  -- sibling (orphan-trap #5319/#5423). Modele verifie in vitro :
  -- game_theory_lean CooperativeGames `globs := #[`CooperativeGames.*]` (#4980,
  -- meme cas : `_en` en sous-modules sous le repertoire du lib).
  globs := #[`Conway.*]
