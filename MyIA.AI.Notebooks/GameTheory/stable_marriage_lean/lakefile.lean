import Lake
open Lake DSL

package «stable_marriage» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «StableMarriage» where
  -- Gale-Shapley Stable Marriage Theorem formalization
  --
  -- i18n FR-first (EPIC #4980 ratif 2026-07-04 11:58Z, comment-4881909354) :
  -- Globs precis par tranche (FR canonique + EN sibling verbatim) :
  --   - GaleShapley + GaleShapley_en (tranche 9, MERGED #5325)
  --   - Lattice + Lattice_en (tranche 8, MERGED #5323)
  --   - Definitions + Definitions_en (tranche 13, See #5423)
  --   - GSState + GSState_en (tranche 13, See #5423)
  --   - Lemmas + Lemmas_en (tranche 13, See #5423)
  -- Etendu incrementalement a mesure que les _en siblings sont livres
  -- (cycle c.255 : ajout socle complet tranche 13 sur post-#5423).
  --
  -- Pattern precis plutot que `.submodules \`StableMarriage` broad,
  -- par coherence avec le pattern cooperative_games_lean (c.234 #5441)
  -- ou `.submodules` avait reintroduit un bug dormant `Basic_en.lean`
  -- (PR #5344 commit 24a2da95f, namespace resolution). Pas de bug
  -- equivalent sur main stable_marriage_lean aujourd'hui, mais la
  -- consigne est de garder le pattern precis par securite.
  --
  -- Decoupage : PR combinée c.255 supersede #5423 (3 fichiers tranche-13)
  -- + #5479 (lakefile fix). Lake build REPORTE ai-01 (WDAC po-2026).
  globs := #[
    `StableMarriage.GaleShapley, `StableMarriage.GaleShapley_en,
    `StableMarriage.Lattice, `StableMarriage.Lattice_en,
    `StableMarriage.Definitions, `StableMarriage.Definitions_en,
    `StableMarriage.GSState, `StableMarriage.GSState_en,
    `StableMarriage.Lemmas, `StableMarriage.Lemmas_en
  ]