import Gittins.Basic
import Gittins.Discount
import Gittins.GittinsTheorem

/-!
  Indice de Gittins — Vérification Formelle
  ==========================================

  Une bibliothèque Lean 4 formalisant les concepts clés du théorème
  de l'indice de Gittins pour les bandits multi-bras avec escompte
  géométrique.

  ## Contenu
  - `Gittins.Basic` : Types de bras, politique, fonction de valeur
  - `Gittins.Discount` : Identités d'escompte géométrique (prouvées)
  - `Gittins.GittinsTheorem` : Définition et optimalité de l'indice
    de Gittins (sorry)

  ## Statut
  - Lemmes prouvés : convergence géométrique, valeur présente,
    monotonie de l'escompte
  - Énoncés `sorry` : théorème d'optimalité de Gittins, calcul de l'indice

  ## Références
  - J.C. Gittins, « Bandit Processes and Dynamic Allocation Indices »
    (1979)
  - J.C. Gittins et D.M. Jones, « A dynamic allocation index for the
    discounted multiarmed bandit problem » (1974)

  ---

  # Gittins Index — Formal Verification

  This library formalizes key concepts of the Gittins Index theorem
  for multi-armed bandits with geometric discounting.

  ## Contents
  - `Gittins.Basic`: Bandit arm types, policy, value function
  - `Gittins.Discount`: Geometric discount identities (proved)
  - `Gittins.GittinsTheorem`: Gittins Index definition and optimality (sorry)

  ## Status
  - Proved lemmas: geometric convergence, present value, discount monotonicity
  - Sorry statements: Gittins optimality theorem, index computation

  ## References
  - J.C. Gittins, "Bandit Processes and Dynamic Allocation Indices" (1979)
  - J.C. Gittins and D.M. Jones, "A dynamic allocation index for the
    discounted multiarmed bandit problem" (1974)

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est bilingue inline (FR canonique d'abord, EN en miroir).
  Les modules substantiels (`Gittins.Basic`, `Gittins.Discount`,
  `Gittins.GittinsTheorem`) vivent dans des fichiers siblings `_en.lean`
  séparés lorsque pertinent (cf. #4980 Phase 0.5).
-/
