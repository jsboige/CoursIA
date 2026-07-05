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
  -- active les siblings EN mergés (GaleShapley_en, Lattice_en sur main, plus
  -- Definitions_en / GSState_en / Lemmas_en de PR #5423). Sans cette clause,
  -- Lake ne compile que le module racine (imports intra-lake sur fichiers
  -- FR canoniques) — les 5 fichiers _en sont **orphelins du graphe de build**
  -- (= build-escape, c.230 pattern), CLEAN MERGEABLE en CI mais inactive
  -- dans le build réel (bot Hermes review PR #5423 2026-07-05).
  globs := #[.submodules `StableMarriage] -- active FR canoniques + siblings _en

