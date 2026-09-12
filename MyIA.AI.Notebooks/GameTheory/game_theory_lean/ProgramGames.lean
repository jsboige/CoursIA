/-
  Bibliothèque d'Équilibre en Programmes (noyau borné L1)
  ==================================================

  Formalisation Lean 4 du premier niveau (L1) de l'équilibre en
  programmes pour le Dilemme du Prisonnier — EPIC #15062 « Math for AI
  Safety », grain #15176. Les agents bornés consultent uniquement le
  comportement de l'adversaire contre les deux sondes triviales
  (CoopBot, DefectBot) : aucune récursion, aucune recherche non bornée,
  aucun théorème de Löb (niveaux L2/L3 hors scope).

  ## Théorèmes-phare

  `outcome_probeBot_probeBot` : le bot à sonde bornée atteint la
  coopération mutuelle avec lui-même PAR SONDAGE, sans aucun théorème
  de Löb (un `rfl`). `programNash_probeBot_probeBot` : cette
  coopération EST un équilibre de Nash en programmes de la famille —
  dévier vers DefectBot est puni (P < R), l'insight central de Barasz
  et al. 2014. Et la limite exacte du niveau, hors de la famille :
  `probeBot_exploited_by_exploiterBot` — un adversaire borné sur mesure
  exploite la signature de sonde (C, D) de ProbeBot. Cette limite
  motive les niveaux L2/L3 (Barasz et al. 2014, arXiv:1401.5577 ;
  Critch 2016, arXiv:1602.04184).

  ## Structure

  - `ProgramGames.Basic` — `ProgramAgent` (agents bornés totaux),
    sémantique `outcome` (table de confrontations finie), organes
    décidables `MutualCooperation` / `Unexploitable`, `ProgramNash`
    sur famille finie, bots triviaux (CoopBot, DefectBot, ProbeBot),
    invariants PD réutilisés de `RepeatedGames.Stage`. 0 sorry.
  - `ProgramGames.Bounded` — modèle structurel complémentaire où le code
    public et le budget fini sont explicites, avec interprète total et
    certificats calculables sur une famille témoin.

  ## Cohorte de lakes mutualisés

  Toolchain `leanprover/lean4:v4.32.1`, Mathlib rev `520045ab` —
  cohérent avec les lakes mutualisés (cf
  `.claude/rules/lean-merge-discipline.md` + RUNBOOK prover).
  Junction shared cache `.lake/packages` (cf Issue #4363) — zéro
  checkout Mathlib physique neuf.

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier
  root aggregator est **FR canonique** uniquement. Le miroir anglais
  vit dans le sibling `ProgramGames/Basic_en.lean` (namespace
  `ProgramGames_en`), auto-découvert par le
  `globs := #[`ProgramGames.*]` du lakefile (modèle sibling pair
  ratifié par user le 2026-07-04, Option B rejetée : coût double +
  drift FR/EN + biais qualité).
-/

import ProgramGames.Basic
import ProgramGames.Bounded
