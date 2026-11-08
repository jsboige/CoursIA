import Lake
open Lake DSL

-- social_choice_core_lean : maison canonique du choix social formalise (CoursIA).
-- Descente T3 de #24183 (2026-11-08) : la lib SocialChoice quitte le hub
-- game_theory_lean pour suivre ses carnets consommateurs (doctrine R1,
-- validee par le user le 2026-11-02 : « le site d'un lake suit les carnets
-- qui l'utilisent »). Les carnets de la sous-serie GameTheory/SocialChoice/
-- citent ses chemins (01b, cells 20/29/30/31/36/46).
--
-- Contenu (19 modules FR/EN + umbrella) : Arrow (preuve alternative declaree,
-- port asouther4 -- voir NOTICE.md), Sen, AMD, Groves, MechanismDesign,
-- Voting, SortedListCounting, Framework, Basic. La preuve canonique
-- independante de Arrow vit dans lean_game_defs/SocialChoice.lean ;
-- la comparaison des deux strategies est dans le README et le carnet 01b.
--
-- CERTIFIED : sorry-baseline 0, gate d'axiomes fail-on-sorry (ci_lakes.json).
-- Mathlib au meme pin que le hub d'origine (db584cd6).

package «social_choice_core_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib SocialChoice where
  -- Umbrella SocialChoice.lean + sous-modules SocialChoice.*
  globs := #[`SocialChoice, `SocialChoice.*]
