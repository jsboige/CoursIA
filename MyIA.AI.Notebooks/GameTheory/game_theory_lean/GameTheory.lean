/-
  GameTheory — root aggregator (c.299 skeleton, EPIC #4365)
  =========================================================

  Cible de regroupement post-convergence GameTheory (6->2) :
  ce lake absorbera les modules `social_choice` + `cooperative_games`
  + `stable_marriage` (+ `social_choice_lean_peters` quand son rev
  convergera vers v4.31.0-rc1) en un seul lake multi-module,
  modele prouve `decision_theory_lean` (commits 0e257387 /
  37f7eaab / bd11f982).

  Pattern Lake : pour chaque module absorbe, on declare un
  `lean_lib <Nom>` dans `lakefile.lean` ; le fichier
  `<Nom>.lean` au root du lake sert d'agregateur ; les sous-modules
  vivent dans `<Nom>/<SousModule>.lean`.

  Pour c.299, le seul `lean_lib` actif est `StableMarriage` (vide).
  Les autres `lean_lib` (SocialChoice, CooperativeGames) seront
  actives quand les modules correspondants seront absorbes (c.300+).
-/