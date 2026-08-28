/-
  Bibliothèque de Jeux Répétés
  =============================

  Formalisation Lean 4 des résultats fondamentaux sur les jeux répétés
  à l'infini avec monitoring imparfait, compagnon formel du notebook
  pédagogique GameTheory-6c (jeux répétés, dilemme du prisonnier).

  ## Théorème-phare

  `grim_trigger_sustains_iff` : la coopération procure au moins autant de
  valeur qu'une déviation en un coup suivie de la punition grim ssi le facteur
  d'actualisation vérifie δ ≥ (T−R)/(T−P).

  Cette équivalence formalise la condition d'incitation algébrique du grim
  trigger. Le module prouve aussi que son état de punition est absorbant. Il
  ne formalise pas encore les historiques et profils de stratégies requis
  pour conclure à un équilibre de Nash parfait en sous-jeux.

  ## Structure

  - `RepeatedGames.Stage` — définitions du jeu statique (PD à 4 paramètres
    T > R > P > S, 2R > T + S), actions {C, D}, payoffs.
  - `RepeatedGames.Discounting` — factor d'actualisation, sommes géométriques
    pour les flux R, T + δ·P actualisés. Lemme de réécriture du seuil
    (cible prover BG).
  - `RepeatedGames.GrimTrigger` — transition grim (la punition est absorbante)
    et condition d'incitation `grim_trigger_sustains_iff` sur les deux flux
    actualisés. Une sémantique complète des stratégies/SPNE reste hors module.
  - `RepeatedGames.Folk` (STRETCH) — théorème de Folk actualisé (Fudenberg–
    Maskin 1986), `sorry` accepté dans le scope stretch du companion.

  ## Cohorte de lakes mutualisés

  Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `d568c8c0` —
  cohérent avec 18 autres lakes (cf `.claude/rules/lean-merge-discipline.md`
  + `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/RUNBOOK.md`).
  Junction shared cache `.lake/packages/mathlib4` (cf Issue #4363) —
  zéro checkout Mathlib physique neuf.

  Référence : GameTheory-6c notebook (jeux répétés, théorie et numérique).

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est **FR canonique** uniquement. Le miroir anglais vit dans le
  sibling `RepeatedGames_en.lean` (namespace `RepeatedGames_en`),
  conformément au **modèle sibling pair** ratifié par user le 2026-07-04
  (cf `code-style.md` §Lean i18n, ligne 35 ; Option B rejetée : coût double
  + drift FR/EN + biais qualité). Les modules substantiels
  (`RepeatedGames.Stage`, `RepeatedGames.Discounting`,
  `RepeatedGames.GrimTrigger`, `RepeatedGames.Folk`) vivent dans des
  fichiers siblings `_en.lean` séparés, auto-découverts par le
  `globs := #[`RepeatedGames.*]` du lakefile.
-/

import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger
import RepeatedGames.Folk