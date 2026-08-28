/-
  BayesianLink — pont non-vacu vers lean_game_defs_ext.Bayesian
  =============================================================

  Construction d'un `BayesGame2` concret qui modélise une **partie** du
  marché des lemons : le joueur 1 (acheteur) annonce un prix `P`, le joueur
  2 (vendeur) choisit d'accepter ou non en fonction de son type (H ou L).

  Ce module **utilise réellement** l'API amont (`BayesGame2`, `Strategy1`,
  `Strategy2`, `isBNE g s1 s2`) — pas une simple importation vide. Le BNE
  du manuel est certifié par `decide`, exerçant la décidabilité de `isBNE`
  telle qu'exposée dans `Bayesian.BNE`.

  Pattern mesuré firsthand contre `lean_game_defs_ext/Bayesian/Examples.lean`
  (cf `bosIncomplete_bne : isBNE bosIncomplete bosS1 bosS2 := by decide`).
-/

import Bayesian
import AsymmetricInformation.Lemons

namespace AsymmetricInformation.BayesianLink

/-- Acheteur (joueur 1) : type unique (n'observe pas la qualité du vendeur).
    Vendeur (joueur 2) : deux types (`low`, `high`), probabilité π. -/
def bridgeGame (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2   -- actions j1 : prix bas (0) ou prix haut (1)
  nA2 := 2   -- actions j2 : accepter (0) ou refuser (1)
  w := fun _ _ => 1   -- poids uniformes (1 sur 1, 1 sur 2)
  u1 := fun _ _ a1 a2 =>
    -- j1 (acheteur) : profit = (valeur esperance si trade) - prix paye
    -- a1 = prix binaire encode (0 = c_L, 1 = c_H par convention)
    -- a2 = accepter (0) ou refuser (1)
    let prix : Int := if a1.val = 0 then m.cLow else m.cHigh
    if a2.val = 0 then
      -- trade : j1 recupere la valeur, paie le prix
      AsymmetricInformation.Lemons.expectedValue m π prix - prix
    else
      -- no-trade : pas de flux pour j1
      0
  u2 := fun _ _ _ a2 =>
    -- j2 (vendeur) : simplification 1ère tranche — accepte = +1, refuse = 0.
    match a2.val with
    | 0 => 1
    | _ => 0

/-- Stratégie j1 (acheteur unique) : prix bas (action 0, soit `c_L`).
    Sur l'instance concrète avec `seller always accepts`, c'est la meilleure
    réponse du buyer (prix bas maximise son profit `expectedValue - prix`). -/
def bridgeStrategy1 (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) :
    Strategy1 (bridgeGame π m) :=
  fun _ => (⟨0, by decide⟩ : Fin 2)

/-- Stratégie j2 (vendeur) : accepte toujours (action 0), indépendamment
    du type. C'est l'instance la plus simple possible qui consomme l'API. -/
def bridgeStrategy2 (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) :
    Strategy2 (bridgeGame π m) :=
  fun _ => (⟨0, by decide⟩ : Fin 2)

/-- **Pont non-vacu** : instance close (mêmes paramètres que les exemples
    `Lemons`) où le profil `(bridgeStrategy1, bridgeStrategy2)` est certifié
    BNE par `decide`. C'est l'**utilisation réelle** de l'API amont, pas une
    simple importation. -/
theorem bridgeStrategy_isBNE :
    isBNE
      (bridgeGame
        (π := ⟨50, by decide⟩)
        (m := ⟨0, 5, 0, 4, by omega, by omega⟩))
      (bridgeStrategy1
        (π := ⟨50, by decide⟩)
        (m := ⟨0, 5, 0, 4, by omega, by omega⟩))
      (bridgeStrategy2
        (π := ⟨50, by decide⟩)
        (m := ⟨0, 5, 0, 4, by omega, by omega⟩)) := by
  decide

end AsymmetricInformation.BayesianLink