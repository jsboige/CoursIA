import Lake
open Lake DSL

package «game_theory_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

-- EPIC #4365 — anti-proliferation GameTheory (6->2) : cible « game_theory_lean »
-- regroupera `social_choice` + `cooperative_games` + `stable_marriage` +
-- `social_choice_lean_peters` en un seul lake multi-module, modele `decision_theory_lean`.
--
-- Skeleton c.299 (po-2026) : structure lake validee SANS deplacer aucun
-- module. Les absorptions de modules suivront en PR dediees (c.300+).
--
-- c.306 (po-2026) : ajout d'un second `lean_lib CooperativeGames` qui suit
-- le pattern `decision_theory_lean` (cf `Probas/DecisionTheory/decision_theory_lean/lakefile.lean`
-- ou `Gittins`/`Utility`/`Coherence` cohabitent comme libs distinctes du
-- meme package `decision_theory_lean`). Cela valide la structure multi-lib
-- du lake cible sans coupler `StableMarriage` et `CooperativeGames`
-- (chaque lib reste un point d'entree independant vers Mathlib).
--
-- c.357 (po-2023) : absorption `SocialChoice` (Arrow + Sen + Voting + Framework
-- + Basic + MechanismDesign + SortedListCounting, FR+EN i18n EPIC #4980).
-- 16 fichiers (7 modules FR + 7 siblings _en + 1 _SmokeTest + 1 root
-- SocialChoice.lean) deplaces byte-identique depuis `social_choice_lean/`
-- vers `game_theory_lean/SocialChoice/`. La coquille technique du lake source
-- `social_choice_lean/` (lakefile + toolchain + manifest) a été retirée en
-- follow-up (#4365) : ce dossier n'est plus un lake, seuls ses 3 markdown
-- (README/STATUS/LEAN_PREREQUISITES) subsistent comme tombstone ; la NOTICE
-- vit dans `SocialChoice/social_choice_core_lean/SocialChoice/NOTICE.md` (#24183, T1).
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
  globs := #[`StableMarriage.*, `StableMarriage_en]
  moreLeanArgs := #["--tstack=8192"]

@[default_target]
lean_lib CooperativeGames where
  globs := #[`CooperativeGames.*]

-- T3 #24183 (po-2024, 2026-11-08) : `lean_lib SocialChoice` DESCENDUE vers
-- GameTheory/SocialChoice/social_choice_core_lean (doctrine R1 : le site
-- suit les carnets consommateurs ; sortie du hub validee par le user le
-- 2026-11-02 avec la doctrine des lakes). Le hub ne declare plus cette lib.

@[default_target]
lean_lib RepeatedGames where
  -- Repeated Games Library for Lean 4
  -- Includes: stage game (Prisoner's Dilemma), discounting, grim trigger
  -- Theorem phare: grim_trigger_sustains_iff (one-shot deviation principle)
  globs := #[`RepeatedGames.*, `RepeatedGames_en]

-- c.5383117259 (po-2025) : ajout `lean_lib Swaps` — grain #12222
-- (GameTheory-3c, chemins de swaps). Vérificateur certifié des chemins
-- de générateurs adjacents : certificat d'arrivée (`rfl`), bornes
-- inférieures par énumération décidable, distance exacte Dilemme-Chicken.
-- VOLONTAIREMENT sans Mathlib (calcul fini sur listes littérales) —
-- `lake build Swaps` ne déclenche aucune compilation de dépendance.
@[default_target]
lean_lib Swaps where
  globs := #[`Swaps.*]

-- Ajout `lean_lib Abstraction` — grain #12204 opération 2
-- (GameTheory-19, dette d'abstraction). Contre-exemple certifié au
-- « raffiner une abstraction ne peut qu'améliorer la dette » : sur
-- trois duels d'entiers en stratégies pures, raffiner {{0,1,2}} en
-- {{0},{1,2}} aggrave strictement la dette retransportée (3 → 4),
-- la partition discrète retombe à 0 ; selles de blocs uniques,
-- aggravation indépendante du choix. VOLONTAIREMENT sans Mathlib
-- (pattern `Swaps`) : tout est certifié par `decide`/`rfl` sur des
-- littéraux entiers, aucun théorème concret ne dépend d'un axiome,
-- et `lake build Abstraction` ne déclenche aucune dépendance.
@[default_target]
lean_lib Abstraction where
  globs := #[`Abstraction.*]

-- Grain #15176 (po-2026) : ajout `lean_lib ProgramGames` — EPIC #15062
-- (Math for AI Safety), tranche L1 noyau borné. Équilibre en programmes
-- (Barasz et al. 2014, arXiv:1401.5577 ; Critch 2016, arXiv:1602.04184)
-- LIMITÉ aux agents bornés : `ProgramAgent` = fonction totale des profils
-- de sondes triviales (CoopBot/DefectBot), sémantique `outcome` sans
-- récursion, table de confrontations finie, organes décidables
-- (MutualCooperation, Unexploitable), `ProgramNash` sur famille finie.
-- Réutilise `RepeatedGames.PDAction` / `PrisonersDilemma` / `stagePayoff`
-- (import RepeatedGames.Stage). PAS de Löb (L2/L3 hors scope). 0 sorry.
-- Théorèmes-phare : `outcome_probeBot_probeBot` (rfl, coopération par
-- sondage bornée), `programNash_probeBot_probeBot` (la coopération EST
-- un Nash de la famille : dévier vers DefectBot est puni P < R),
-- `probeBot_unexploitable_in_family`, `probeBot_exploited_by_exploiterBot`
-- (limite exacte du L1 hors famille : exploitable, non insondable).
@[default_target]
lean_lib ProgramGames where
  globs := #[`ProgramGames.*]

-- c.1548 (po-2023, #21221 organe 2/2) : ajout `lean_lib StackelbergBilevel`
-- — Distillation D4 du co-design bilevel morphologie-controle par
-- Stackelberg PPO (Dai et al, ICLR 2026). Module formel du duopole
-- leader/suiveur en demande linéaire et coûts marginaux constants,
-- adossé aux invariants `tests/test_stackelberg*.py`. Forme close
-- (eq. 1 du papier) et best-response follower (invariant central
-- qu'un bug historique avait casse). 0 sorry. Resultats-phare :
-- `cournotSymmetric_eq_is_fixed_point`,
-- `stackelberg_follower_eq_reaction_clamped`,
-- `stackelberg_closed_form_expansion`,
-- `first_mover_advantage_symmetric`,
-- `welfare_above_cournot_symmetric`, plus 6 valeurs-pytest par
-- `norm_num`. VOLONTAIREMENT sans `ProgramGames` (pas de bilevel
-- imbriqué — Stackelberg statique est un cas particulier où le
-- leader connaît l'identité du follower) et sans `RepeatedGames`
-- (pas de temps, pas de jeu repete). 8ᵉ cohorte `lean_lib` du
-- même package — modèle `decision_theory_lean`.
@[default_target]
lean_lib StackelbergBilevel where
  globs := #[`StackelbergBilevel.*]

-- Grain #24423 (po-2023, critere 4 de #21927) : ajout `lean_lib
-- CongestionGames` — borne elementaire 2x du prix de l'anarchie pour
-- l'equilibre minimisant le potentiel de Rosenthal d'un jeu de
-- congestion atomique lineaire, entier sur `Nat` (potentiel double
-- Phi' = sum a_e x_e (x_e+1), chaine C <= Phi' <= 2C via x^2 <= x(x+1)
-- <= 2x^2). Identite d'exactitude `potential_exchange` (le facteur 2
-- vient du potentiel double exact des deviations unilaterales),
-- `minPotential_isNash`, `cost_minPotential_le_two`. Deux temoins par
-- `decide` : ratio exactement 2 (2 joueurs, 3 aretes emboitees) et
-- 15/7 > 2 (3 joueurs — la borne couvre l'equilibre potentiel-minimal,
-- pas tous les equilibres ; le 5/2 affine de Christodoulou-Koutsoupias
-- 2005 est hors scope). Compagnon Lean du carnet
-- GameTheory-04h-Routing-PriceOfAnarchy (Python, non-atomique 4/3).
-- 9ᵉ cohorte `lean_lib` du même package. 0 sorry, 0 axiome ad hoc.
@[default_target]
lean_lib CongestionGames where
  globs := #[`CongestionGames.*]

-- Grain #25686 (po-2024, distillation Lexifina) : ajout `lean_lib
-- LegalLoophole` — modele jouet « regles fiscales comme jeu formel » :
-- 3 comptes (cash, traditionnel ventile pre-tax/basis, Roth), 4 coups
-- (contribution Roth directe interdite aux hauts revenus, contributions
-- deductible et non deductible partageant un budget annuel `maxContrib`,
-- conversion taxee au pro-rata de la part pre-tax). Semantique
-- executable (`step`/`run` sur `Option`, zero dependance hors core —
-- compilable en quelques secondes, pas de Mathlib), deux familles de
-- theoremes : `wealth_conservation` + `cash_floor` -> `roth_ceiling`
-- (a toute profondeur, le Roth final est plafonne par l'etat initial et
-- le budget annuel) et `backdoor_exists` + `backdoor_optimal` (la
-- sequence non-deductible + conversion atteint exactement le plafond
-- sans taxe : le temoin est optimal). Copie pedagogique declaree de
-- l'echelle du modele CC0 lexifina/global-law (reduit, v4.33.0), citee
-- dans le module. Compagnon Lean du carnet
-- GameTheory-23-Loopholes-Fiscaux-Python-Lean. 10e cohorte `lean_lib`
-- du meme package. 0 sorry, 0 axiome ad hoc.
-- c.Hermes-26022 : `@[default_target]` requis comme pour les 9 autres libs --
-- sans lui, `lake -R build` (la jambe CI) ne construit pas la cible et le
-- module peut casser sans faire rougir aucun job.
@[default_target]
lean_lib LegalLoophole where
  globs := #[`LegalLoophole.*]

-- Tranche L2 (po-2025) : `ProgramGames/FairBot.lean` (+ sibling `_en`) —
-- EPIC #15062, FairBot par le théorème de Löb. Interface
-- `ModalProvability box` (D1 nécessitation, D2 distribution, D3
-- introspection positive, + schéma de Löb en CHAMP de structure),
-- point fixe coordonné `loeb_mutual_fixedpoint` (la dérivation de
-- Barasz et al. 2014), `fairBot_fairBot_cooperation` (FairBot × FairBot
-- = (C,C)), inexploitabilité sous fiabilité locale explicite
-- (`fairBot_unexploitable`). AUCUN axiome ad hoc : l'indépendance du
-- schéma vis-à-vis de D1/D2/D3 est mesurée dans le module
-- (`bump_loeb_fails`), et le champ `loeb` reste une hypothèse explicite
-- de l'interface — sa non-vacuité est attestée par le témoin
-- noyau-vérifié `FormalLogic.GLBridge.loeb_schema` (lake voisin
-- `formal_logic_lean` v4.33.1, PR #15923), cité par RÉFÉRENCE et jamais
-- importé ; ce module ne définit aucune instance de `ModalProvability` —
-- conformément au gate L3 de
-- l'EPIC : « sans forcer ces dépendances dans game_theory_lean 4.32.1 »
-- (split toolchain 4.32.1/4.33.1 mesuré). 0 sorry ajouté.
