import Lake
open Lake DSL

package «conway» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Pin explicite v4.31.0-rc1 (harmonisation #4362) : sans `@`, lake resout la
-- require sur `master` par defaut alors que lake-manifest.json est epingle sur
-- v4.31.0-rc1 (rev d568c8c0) -> warning `manifest out of date: git revision of
-- dependency 'mathlib' changed` a CHAQUE lake build (bruit dans les logs du
-- prover BG, et un `lake update` accidentel sauterait sur master).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Conway» where
  -- Conway hommage: accessible formalizations of lesser-known results
  -- by John Horton Conway (1937-2020)
  --
  -- Convention i18n EPIC #4980 : `.submodules `Conway` couvre les sous-modules
  -- FR (`Conway.Doomsday`, `Conway.Angel`, ...) ET leurs jumeaux `_en`
  -- (`Conway.Doomsday_en`, `Conway.Angel_en`, ...). Le jumeau root `Conway_en`
  -- doit etre globbe explicitement (bare `.submodules` ne matche que les
  -- sous-modules, pas les fichiers siblings au niveau du lib), pattern #6585
  -- knot_lean / #4980. Sans cet ajout, lake build laisse `Conway_en.lean`
  -- ORPHELIN : l'umbrella FR ne l'importe pas, `Conway_en.lean` n'est pas dans
  -- un sous-module, et le scan sorry du CI reutilisable exclut `*_en.lean`
  -- (lean-build.yml L85, #6429) -> aucune etape ne le compilait (orphan-trap
  -- #5319/#5423). Modele verifie : knot_lean `Knots_en.lean` PR #6682, meme
  -- pattern sibling root aggregator.
  globs := #[.submodules `Conway, `Conway_en]
