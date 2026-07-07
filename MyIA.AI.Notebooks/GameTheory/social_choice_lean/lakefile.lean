import Lake
open Lake DSL

package «social_choice» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SocialChoice» where
  -- Port of asouther4/lean-social-choice to Lean 4
  -- Arrow's Impossibility Theorem and Sen's Theorem
  --
  -- i18n FR-first (EPIC #4980 ratif 2026-07-04 11:58Z, comment-4881909354) :
  -- Globs precis par module (FR canonique + EN sibling verbatim) :
  --   - 7 modules canoniques (Arrow, Basic, Framework, MechanismDesign,
  --     Sen, SortedListCounting, Voting) — deja compiles transitivement
  --     via SocialChoice.lean racine. Globs explicite = preuve in-graph CI.
  --   - 7 EN siblings (Arrow_en, Basic_en, Framework_en, MechanismDesign_en,
  --     Sen_en, SortedListCounting_en, Voting_en) — en cours de finalisation
  --     via PRs #5500/#5502/#5505 + fix namespace.
  --   - _SmokeTest (sanity check nat).
  --
  -- Pattern precis (decision c.255 ai-01 msg msg-20260706T080634-aa4ur6)
  -- au lieu de `.submodules \`SocialChoice` broad qui ne compile QUE
  -- `SocialChoice.lean` racine (= default Lake = `Glob.one` du root
  -- SEUL, voir Lake README "Defaults to a `Glob.one` of each of the
  -- library's `roots`"). Conséquence : 0 module SocialChoice.* listé
  -- dans le log Lake, false-green "Built SocialChoice" = juste la
  -- lib aggregate. Les 7 EN siblings etaient des ORPHELINS silencieux.
  --
  -- Lake build REPORTE ai-01 (WDAC po-2026 bloque Lean local).
  globs := #[
    `SocialChoice.Arrow, `SocialChoice.Arrow_en,
    `SocialChoice.Basic, `SocialChoice.Basic_en,
    `SocialChoice.Framework, `SocialChoice.Framework_en,
    `SocialChoice.MechanismDesign, `SocialChoice.MechanismDesign_en,
    `SocialChoice.Sen, `SocialChoice.Sen_en,
    `SocialChoice.SortedListCounting, `SocialChoice.SortedListCounting_en,
    `SocialChoice.Voting, `SocialChoice.Voting_en,
    `SocialChoice._SmokeTest
  ]