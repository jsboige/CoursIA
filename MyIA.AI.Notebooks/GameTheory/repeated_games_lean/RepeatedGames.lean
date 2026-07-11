/-
  Bibliothèque de Jeux Répétés
  =============================

  Formalisation Lean 4 des résultats fondamentaux sur les jeux répétés
  à l'infini avec monitoring imparfait, compagnon formel du notebook
  pédagogique GameTheory-6c (jeux répétés, dilemme du prisonnier).

  ## Théorème-phare

  `grim_trigger_sustains_iff` : la stratégie grim-trigger soutient la
  coopération ssi le facteur d'actualisation vérifie δ ≥ (T−R)/(T−P).

  Cette inégalité caractérise le seuil en-dessous duquel un joueur préfère
  dévier (gagner T aujourd'hui puis endurer P forever) plutôt que coopérer
  perpétuellement (R forever). Le mécanisme est le one-shot deviation
  principle (Lemke–Tarski) : aucune déviation sur deux périodes ou plus
  ne bat la déviation en une seule période, donc regarder uniquement le
  trade-off one-shot suffit.

  ## Structure

  - `RepeatedGames.Stage` — définitions du jeu statique (PD à 4 paramètres
    T > R > P > S, 2R > T + S), actions {C, D}, payoffs.
  - `RepeatedGames.Discounting` — factor d'actualisation, sommes géométriques
    pour les flux R, T + δ·P actualisés. Lemme de réécriture du seuil
    (cible prover BG).
  - `RepeatedGames.GrimTrigger` — stratégie grim (coopère → si déviation
    détectée, défaut éternel), théorème-phare `grim_trigger_sustains_iff`,
    corollaire NE. Ces deux sorries sont les cibles primaires du prover BG.
  - `RepeatedGames.Folk` (STRETCH) — théorème de Folk actualisé (Fudenberg–
    Maskin 1986), `sorry` accepté dans le scope stretch du companion.

  ## Cohorte de lakes mutualisés

  Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `d568c8c0` —
  cohérent avec 18 autres lakes (cf `.claude/rules/lean-merge-discipline.md`
  + `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/RUNBOOK.md`).
  Junction shared cache `.lake/packages/mathlib4` (cf Issue #4363) —
  zéro checkout Mathlib physique neuf.

  Référence : GameTheory-6c notebook (jeux répétés, théorie et numérique).

  ---

  # Repeated Games Library

  Lean 4 formalization of the foundational results on infinitely repeated
  games with imperfect monitoring, companion formel of the pedagogical
  notebook GameTheory-6c (repeated games, prisoner's dilemma).

  ## Headline theorem

  `grim_trigger_sustains_iff`: the grim-trigger strategy sustains
  cooperation iff the discount factor satisfies δ ≥ (T−R)/(T−P).

  This inequality characterizes the threshold below which a player prefers
  to deviate (gain T today then endure P forever) rather than cooperate
  perpetually (R forever). The mechanism is the one-shot deviation
  principle (Lemke–Tarski): no deviation over two periods or more beats
  the deviation in a single period, so looking at the one-shot trade-off
  is sufficient.

  ## Structure

  - `RepeatedGames.Stage` — definitions of the stage game (PD with 4
    parameters T > R > P > S, 2R > T + S), actions {C, D}, payoffs.
  - `RepeatedGames.Discounting` — discount factor, geometric sums for
    the R, T + δ·P discounted flows. Threshold rewrite lemma (prover BG
    target).
  - `RepeatedGames.GrimTrigger` — grim strategy (cooperate → if deviation
    detected, eternal defection), headline theorem `grim_trigger_sustains_iff`,
    NE corollary. These two sorries are the prover BG primary targets.
  - `RepeatedGames.Folk` (STRETCH) — discounted Folk theorem (Fudenberg–
    Maskin 1986), `sorry` accepted within the companion's stretch scope.

  ## Mutualized lake cohort

  Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `d568c8c0` —
  consistent with 18 other lakes (see `.claude/rules/lean-merge-discipline.md`
  + `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/RUNBOOK.md`).
  Shared cache junction `.lake/packages/mathlib4` (see Issue #4363) —
  zero fresh Mathlib physical checkouts.

  Reference: GameTheory-6c notebook (repeated games, theory and numerics).

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
  conformément au pattern canonique `Gittins.lean` du lake voisin
  `decision_theory_lean`. Les modules substantiels (`RepeatedGames.Stage`,
  `RepeatedGames.Discounting`, `RepeatedGames.GrimTrigger`,
  `RepeatedGames.Folk`) vivent dans des fichiers siblings `_en.lean`
  séparés lorsque pertinent (cf. #4980 Phase 0.5, décision user ratifiée
  2026-07-04 sur la paire FR-canonical-first + EN-mirror-second).
-/

import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger
import RepeatedGames.Folk
