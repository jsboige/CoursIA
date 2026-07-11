import Lake
open Lake DSL

package «game_theory_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

-- EPIC #4365 — anti-proliferation GameTheory (6->2) : cible « game_theory_lean »
-- regroupera `social_choice` + `cooperative_games` + `stable_marriage` +
-- `social_choice_lean_peters` en un seul lake multi-module, modele `decision_theory_lean`.
--
-- Skeleton c.299 (po-2026) : structure lake validee SANS deplacer aucun
-- module. Les absorptions de modules suivront en PR dediees (c.300+).
--
-- c.306 (po-2026) : ajout d'un second `lean_lib CooperativeGames` qui suit
-- le pattern `decision_theory_lean` (cf `Probas/decision_theory_lean/lakefile.lean`
-- ou `Gittins`/`Utility`/`Coherence` cohabitent comme libs distinctes du
-- meme package `decision_theory_lean`). Cela valide la structure multi-lib
-- du lake cible sans coupler `StableMarriage` et `CooperativeGames`
-- (chaque lib reste un point d'entree independant vers Mathlib).
--
-- c.357 (po-2023) : absorption `SocialChoice` (Arrow + Sen + Voting + Framework
-- + Basic + MechanismDesign + SortedListCounting, FR+EN i18n EPIC #4980).
-- 16 fichiers (7 modules FR + 7 siblings _en + 1 _SmokeTest + 1 root
-- SocialChoice.lean) deplaces byte-identique depuis `social_choice_lean/`
-- vers `game_theory_lean/SocialChoice/`. Lake source `social_choice_lean/`
-- reste en place (docs + lakefile + manifest archives) pour ne pas casser
-- les refs notebooks existantes ; sera archive en follow-up post-merge.
-- Prochaine absorption prevue : `social_choice_lean_peters` (v4.27 -> v4.31,
-- INTRINSIC documente si port depasse budget cf sota-not-workaround).
--
-- c.371 (po-2023) : absorption `RepeatedGames` (Stage + GrimTrigger + Discounting
-- + Folk, FR+EN i18n EPIC #4980). 9 fichiers (4 modules FR + 4 siblings _en +
-- 1 root RepeatedGames.lean) deplaces byte-identique depuis `repeated_games_lean/`
-- vers `game_theory_lean/RepeatedGames/`. Lake source `repeated_games_lean/`
-- reste en place (docs + lakefile + manifest archives), pattern identique a
-- c.357 pour `social_choice_lean/`. Theoreme-phare `grim_trigger_sustains_iff`
-- (delta >= threshold, 0 sorry) + 1 stretch `folk_theorem_discounted` (5+5 sorry
-- documentes, BG prover stretch tolerate cf #4880).
-- 4ᵉ cohorte `lean_lib` cohabite : StableMarriage + CooperativeGames +
-- SocialChoice + **RepeatedGames** = 4 lean_lib du meme package `game_theory_lean`,
-- modele `decision_theory_lean` (Gittins/Utility/Coherence). Lake build gated
-- par une machine >=16 GB RAM libre (RECOVERABLE-MACHINE documente cf sota-not-workaround).
-- Prochaines absorptions prevues : `conway_cgt_lean` (CGT, separabilite discutable)
-- ou laisser autonome (anti god-lake).
--
-- Convention i18n EPIC #4980 (cf decision_theory_lean precedent) :
-- `globs` (et non `roots`) avec suffixe `.*` pour auto-decouvrir siblings `_en`.
--
-- c.324 (po-2026, #6140) : `StableMarriage.GSState` crashes Windows-native
-- `lean.exe` cold builds with `0xC0000409` = STATUS_STACK_BUFFER_OVERRUN.
-- Symptom: `✖ [8503/8529] Building StableMarriage.GSState (46s) — Lean exited
-- with code 3221226505`. The EN sibling `StableMarriage.GSState_en` builds
-- fine on the same machine, CI/Linux builds pass, and the file is
-- byte-identical between FR/EN on non-docstring content — proving this is a
-- Windows thread-stack flake, NOT a proof regression.
-- Default thread stack on Windows is 1 MiB; bumping to 8 MiB (`--tstack=8192`)
-- absorbs the deep elaboration of the three inline `IsTrans (Fin n)` instances
-- on `gsMenPrefLE` in `gsChooseMax` / `gsChooseMax_mem` / `gsChooseMax_maximal`
-- (file `StableMarriage/GSState.lean`). No file in `StableMarriage/` is
-- modified: this is a build-config fix, anti-régression compliant (no touch
-- to proof). Scope = per-lib override so `CooperativeGames` / `SocialChoice`
-- cold builds remain unaffected. See #6140.
@[default_target]
lean_lib StableMarriage where
  globs := #[`StableMarriage.*]
  moreLeanArgs := #["--tstack=8192"]

@[default_target]
lean_lib CooperativeGames where
  globs := #[`CooperativeGames.*]

@[default_target]
lean_lib SocialChoice where
  globs := #[`SocialChoice.*]

@[default_target]
lean_lib RepeatedGames where
  -- Repeated Games Library for Lean 4
  -- Includes: stage game (Prisoner's Dilemma), discounting, grim trigger
  -- Theorem phare: grim_trigger_sustains_iff (one-shot deviation principle)
  globs := #[`RepeatedGames.*]

@[default_target]
lean_lib RepeatedGames where
  -- Repeated Games Library for Lean 4
  -- Includes: stage game (Prisoner's Dilemma), discounting, grim trigger
  -- Theorem phare: grim_trigger_sustains_iff (one-shot deviation principle)
  globs := #[`RepeatedGames.*]
>>>>>>> ad1ef27c7 (feat(lean,#4365): absorb RepeatedGames (Stage+Discounting+GrimTrigger+Folk FR+EN) into game_theory_lean — anti-proliferation GT 6->2 (c.371))
