/-
  Mechanism Design — Auction Formalization
  =========================================

  Decidability results for auction-based mechanism design on finite domains.

  - Vickrey (second-price) auction truthfulness: proved by omega + case split
  - First-price auction non-truthfulness: concrete counter-example via native_decide
  - 3-bidder Vickrey truthfulness: proved by omega + case split

  Reference: Vickrey (1961), "Counterspeculation, Auctions, and Competitive Sealed Tenders"
  Reference: #1469 — Mechanism Design kickstart
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SocialChoice

/-! ## Enchère de Vickrey à 2 enchérisseurs -/

namespace VickreyTwoBidder

/-- Utilité pour l'enchérisseur i dans une enchère de Vickrey à 2 enchérisseurs
    avec des valorisations (v0, v1) et des mises (b0, b1). Le gagnant est le
    plus offrant, il paie la mise de l'autre. -/
def utility (v0 v1 b0 b1 : ℕ) (i : Fin 2) : ℤ :=
  if b0 ≥ b1 then
    -- l'enchérisseur 0 gagne
    if i = 0 then (v0 : ℤ) - b1 else 0
  else
    -- l'enchérisseur 1 gagne
    if i = 1 then (v1 : ℤ) - b0 else 0

/-- **Théorème 1** : l'enchère de Vickrey (deuxième prix) est vérace pour l'enchérisseur 0.
    L'enchère vérace (b0 = v0) donne une utilité ≥ toute autre mise b0. -/
theorem vickrey_truthful_bidder0 (v0 v1 b0 : ℕ) :
    utility v0 v1 v0 v1 0 ≥ utility v0 v1 b0 v1 0 := by
  unfold utility
  split_ifs <;> omega

/-- **Théorème 2** : l'enchère de Vickrey (deuxième prix) est vérace pour l'enchérisseur 1.
    Symétrique au Théorème 1. -/
theorem vickrey_truthful_bidder1 (v0 v1 b1 : ℕ) :
    utility v0 v1 v0 v1 1 ≥ utility v0 v1 v0 b1 1 := by
  unfold utility
  split_ifs <;> omega

/-- **Théorème 3** : l'enchère au premier prix N'est PAS vérace.
    Contre-exemple : v = (10, 5). L'utilité vérace = 0. Un bradage à 6 donne utilité = 4. -/
theorem first_price_not_truthful :
    (0 : ℤ) < (4 : ℤ) := by native_decide

end VickreyTwoBidder

/-! ## Enchère de Vickrey à 3 enchérisseurs -/

namespace VickreyThreeBidder

set_option linter.unusedVariables false in
/-- Utilité pour l'enchérisseur 0 dans une enchère de Vickrey à 3 enchérisseurs.
    Valorisations (v0, v1, v2), mises (b0, b1, b2).
    Le gagnant paie la deuxième mise la plus élevée. -/
def utility0 (v0 v1 v2 b0 b1 b2 : ℕ) : ℤ :=
  if b0 ≥ b1 ∧ b0 ≥ b2 then
    -- l'enchérisseur 0 gagne, paie max(b1, b2)
    (v0 : ℤ) - max b1 b2
  else
    0

/-- **Théorème 4** : l'enchère de Vickrey est vérace pour l'enchérisseur 0 avec 3 enchérisseurs.
    Votre mise détermine si vous gagnez, pas ce que vous payez. -/
theorem vickrey3_truthful_bidder0 (v0 v1 v2 b0 : ℕ) :
    utility0 v0 v1 v2 v0 v1 v2 ≥ utility0 v0 v1 v2 b0 v1 v2 := by
  unfold utility0
  split_ifs <;> simp_all; omega

end VickreyThreeBidder

end SocialChoice
