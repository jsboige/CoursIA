/-
  BayesianLink — non-vacuous bridge to lean_game_defs_ext.Bayesian
  ==================================================================

  Construction of a concrete `BayesGame2` that models a **portion** of
  the lemons market: player 1 (buyer) announces a price `P`, player 2
  (seller) chooses to accept or not based on their type (H or L).

  This module **actually uses** the upstream API (`BayesGame2`,
  `Strategy1`, `Strategy2`, `isBNE g s1 s2`) — not a mere empty import.
  The textbook BNE is certified by `decide`, exercising the decidability
  of `isBNE` as exposed in `Bayesian.BNE`.

  Pattern measured firsthand against
  `lean_game_defs_ext/Bayesian/Examples.lean`
  (cf `bosIncomplete_bne : isBNE bosIncomplete bosS1 bosS2 := by decide`).

  English mirror of `BayesianLink.lean`. Byte-identical except docstrings.
-/

import Bayesian
import AsymmetricInformation.Lemons

namespace AsymmetricInformation.BayesianLink

/-- Buyer (player 1): single type (does not observe seller quality).
    Seller (player 2): two types (`low`, `high`), probability π. -/
def bridgeGame (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2   -- p1 actions: low price (0) or high price (1)
  nA2 := 2   -- p2 actions: accept (0) or refuse (1)
  w := fun _ _ => 1   -- uniform weights (1 on 1, 1 on 2)
  u1 := fun _ _ a1 a2 =>
    -- p1 (buyer): profit = (expected value if trade) - price paid
    -- a1 = binary encoded price (0 = c_L, 1 = c_H by convention)
    -- a2 = accept (0) or refuse (1)
    let prix : Int := if a1.val = 0 then m.cLow else m.cHigh
    if a2.val = 0 then
      -- trade: p1 recovers the value, pays the price
      AsymmetricInformation.Lemons.expectedValue m π prix - prix
    else
      -- no-trade: no flow for p1
      0
  u2 := fun _ _ _ a2 =>
    -- p2 (seller): first-tranche simplification — accept = +1, refuse = 0.
    match a2.val with
    | 0 => 1
    | _ => 0

/-- p1 strategy (single buyer): low price (action 0, i.e. `c_L`).
    On the concrete instance with `seller always accepts`, this is the
    buyer's best response (low price maximizes profit
    `expectedValue - price`). -/
def bridgeStrategy1 (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) :
    Strategy1 (bridgeGame π m) :=
  fun _ => (⟨0, by decide⟩ : Fin 2)

/-- p2 strategy (seller): always accepts (action 0), regardless of type.
    This is the simplest possible instance that consumes the API. -/
def bridgeStrategy2 (π : AsymmetricInformation.Lemons.Prior)
    (m : AsymmetricInformation.Lemons.TwoQualityMarket) :
    Strategy2 (bridgeGame π m) :=
  fun _ => (⟨0, by decide⟩ : Fin 2)

/-- **Non-vacuous bridge**: closed instance (same parameters as the `Lemons`
    examples) where the profile `(bridgeStrategy1, bridgeStrategy2)` is
    certified BNE by `decide`. This is the **actual use** of the upstream
    API, not a mere import. -/
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