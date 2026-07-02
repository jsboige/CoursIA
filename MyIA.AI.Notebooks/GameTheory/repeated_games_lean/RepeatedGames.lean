/-
  Repeated Games Library
  =======================

  Lean 4 formalization of the foundational results on infinitely repeated
  games with imperfect monitoring, companion formel of the pedagogical
  notebook GameTheory-6c (jeux répétés, dilemme du prisonnier).

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
-/

import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger
import RepeatedGames.Folk
