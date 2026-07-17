/-
  Exemple résolu — Bataille des Sexes en information incomplète
  ============================================================

  L'illustration classique de Harsanyi : le joueur 1 ne sait pas si le
  joueur 2 veut le rencontrer (se coordonner) ou l'éviter. La préférence
  du joueur 2 est son type privé ; le prior donne un poids égal aux deux
  types.

  Actions (les deux joueurs) : 0 = Ballet, 1 = Football.
  Le joueur 1 préfère le Ballet (paiement 2 sur (B,B), 1 sur (F,F), 0 en cas
  de désaccord).
  Le type « rencontrer » du joueur 2 préfère le Football mais veut coordonner.
  Le type « éviter » du joueur 2 veut DÉSaccorder : 2 si (B,F), 1 si (F,B).

  Le BNE pur du manuel — le joueur 1 joue Ballet ; le joueur 2 joue Ballet
  lorsqu'il est du type « rencontrer » et Football lorsqu'il est du type
  « éviter » — est vérifié ci-dessous par `decide`, exerçant la décidabilité
  de `isBNE`.

  Reflète GameTheory-11-BayesianGames.ipynb. Voir #2610.
-/

import Bayesian.BNE

/-- Bataille des Sexes où le désir du joueur 2 de rencontrer ou d'éviter
    le joueur 1 est une information privée (prior uniforme sur les deux types).
    Type 0 du joueur 2 = « rencontrer », type 1 = « éviter ». -/
def bosIncomplete : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 =>
    if a1.val = a2.val then (if a1.val = 0 then 2 else 1) else 0
  u2 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      -- type « rencontrer » : veut coordonner, préfère le Football
      -- "meet" type: wants to coordinate, prefers Football
      if a1.val = a2.val then (if a1.val = 0 then 1 else 2) else 0
    else
      -- type « éviter » : veut DÉSaccorder
      -- "avoid" type: wants to MISmatch
      if a1.val = 0 ∧ a2.val = 1 then 2
      else if a1.val = 1 ∧ a2.val = 0 then 1
      else 0

/-- Le joueur 1 (type unique) joue Ballet. -/
def bosS1 : Strategy1 bosIncomplete := fun _ => ⟨0, by decide⟩

/-- Le joueur 2 joue Ballet lorsqu'il est du type « rencontrer », Football
    lorsqu'il est du type « éviter ». -/
def bosS2 : Strategy2 bosIncomplete := fun t2 =>
  if t2.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

/-- Le profil de stratégies du manuel est un équilibre de Nash bayésien,
    vérifié par calcul. -/
theorem bosIncomplete_bne : isBNE bosIncomplete bosS1 bosS2 := by decide

/-- Vérification de cohérence : sous l'équilibre, l'utilité espérée interimaire
    du joueur 1 issue du Ballet est 2 (il rencontre le type « rencontrer »,
    manque le type « éviter ») contre 1 s'il dévie vers le Football. -/
theorem bosIncomplete_interim_values :
    interimU1 bosIncomplete ⟨0, by decide⟩ ⟨0, by decide⟩ bosS2 = 2 ∧
    interimU1 bosIncomplete ⟨0, by decide⟩ ⟨1, by decide⟩ bosS2 = 1 := by decide

/-- L'équilibre survit à la remise à l'échelle des poids du prior (par ex.
    les poids (3, 3) au lieu de (1, 1) encodent le même prior uniforme). -/
theorem bosIncomplete_bne_scaled : isBNE (scaleW bosIncomplete 3) bosS1 bosS2 :=
  (isBNE_scaleW bosIncomplete 3 (by decide) bosS1 bosS2).mpr bosIncomplete_bne
