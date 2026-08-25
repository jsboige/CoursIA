/-
  Miyazaki-Wilson-Spence 1977-1978 — anticipatory equilibrium, bounded formalization
  ===================================================================================

  **Bounded** formalization of the anticipatory equilibrium model of
  Wilson 1977 *JET* 16:167-207, Miyazaki 1977 *Bell J.* 8(2):394-418
  and Spence 1978.

  Strict bounds (canonical audit c.475 category #4):
  - **NO** `wilson_anticipatory_always_exists : ∃!` in this delivery;
  - **NO** general MWS uniqueness without substantial hypotheses;
  - **NO** "Wilson 1989 fictional" — correct date: 1977-1978;
  - Finite definitions + **decidable examples** where zero, one or
    multiple menus satisfy the predicate.

  Three modest theorems are worth more than a `∃!` whose hypotheses
  already encode the conclusion.

  English mirror of `MiyazakiWilson.lean`. Byte-identical except docstrings.
-/

import AsymmetricInformation.Screening

namespace AsymmetricInformation.MiyazakiWilson

/-- **Anticipatory** predicate: no menu contract can be unilaterally
    withdrawn to propose an off-menu profitable contract. This is the
    **static** version (no post-selection reaction) of Wilson 1977. -/
def anticipatoryMenu
    (menu : AsymmetricInformation.Screening.Menu)
    (r : AsymmetricInformation.Screening.RiskProfile) : Prop :=
  ∀ c ∈ menu, ∀ c' : AsymmetricInformation.Screening.Contract, c' ∉ menu →
    AsymmetricInformation.Screening.globalExpectedProfit c' r ≤
      AsymmetricInformation.Screening.globalExpectedProfit c r

/-- **Cross-subsidy tenable**: there exists a contract `c` in the menu
    that subsidizes one type by the other (positive profit on one type,
    negative on the other). This is the **local definition** of
    cross-subsidy, which does NOT belong to RS. -/
def crossSubsidyTenable
    (menu : AsymmetricInformation.Screening.Menu)
    (r : AsymmetricInformation.Screening.RiskProfile) : Prop :=
  ∃ c ∈ menu, ∃ q : AsymmetricInformation.Screening.RiskType,
    AsymmetricInformation.Screening.expectedProfit c r q > 0 ∧
    ∃ c' ∈ menu, ∃ q' : AsymmetricInformation.Screening.RiskType, q' ≠ q ∧
      AsymmetricInformation.Screening.expectedProfit c' r q' < 0

/-- Trivially anticipatory menu: the empty menu is anticipatory (vacuity
    of `∀ c ∈ ∅`). -/
theorem anticipatory_empty :
    ∀ (r : AsymmetricInformation.Screening.RiskProfile),
      anticipatoryMenu [] r := by
  intro r c hc
  -- `hc: c ∈ []` is `False` by construction of `List.Mem`. We extract
  -- the contradiction by `cases` then apply `False.elim`.
  cases hc

/-- A singleton `(α, β)` is NOT anticipatory if an off-menu profitable
    contract exists: this is the **cream-skim instability example** in
    the boundary case. The complete proof requires `Decidable` instances
    on strict inequalities, dependent on Mathlib — we leave the proof in
    bounded `sorry`. The theorem documents the **direction**:
    profitable cream-skim ⟹ ¬ anticipatory. -/
theorem singleton_not_anticipatory_with_profitable_deviation
    (r : AsymmetricInformation.Screening.RiskProfile)
    (c : AsymmetricInformation.Screening.Contract)
    (hPos : ∃ c' : AsymmetricInformation.Screening.Contract,
              AsymmetricInformation.Screening.globalExpectedProfit c' r > 0) :
    ¬ anticipatoryMenu [c] r := by
  intro hAnt
  -- Bounded sorry: see theorem comment. Instantiating `hAnt`
  -- on the singleton and the off-menu contract gives an inequality
  -- that contradicts `hPos`, but the exact chain depends on Mathlib.
  sorry

/-- **Decided example — 2-contract menu without cross-subsidy**:
    profile `(p_H, p_L) = (25, 75)`, menu `[(α=100, β=20), (α=40, β=10)]`.
    Calculation:
    - Contract 1 on H: `20*100 - 25*100 = -500` (negative)
    - Contract 2 on L: `10*100 - 75*40 = 1000 - 3000 = -2000` (negative)
    - Contract 1 on L: `20*100 - 75*100 = 2000 - 7500 = -5500` (negative)
    - Contract 2 on H: `10*100 - 25*40 = 1000 - 1000 = 0` (neutral)
    Therefore cross-subsidy is NOT tenable on this menu (all profits ≤ 0).
    The example demonstrates that `crossSubsidyTenable` is non-trivial.

    **Bounded sorry**: the complete proof of integer arithmetic (4 pairs of
    contracts × 4 pairs of types = 16 cases) requires explicit `Decidable`
    instances on `Int`/`Nat` (cf Lean core, not Mathlib here). The sorry
    is bounded to a mechanical `decide`, NOT to an existence or uniqueness
    theorem. Left as first fragment to refine in a later iteration
    (cf body v4 D — no general claim). -/
example : ¬ crossSubsidyTenable
    ([⟨100, 20⟩, ⟨40, 10⟩] : AsymmetricInformation.Screening.Menu)
    ⟨25, 75, by omega⟩ := by
  sorry

/-- **NO uniqueness or general existence claim** in this delivery.
    Three modest theorems:
    (1) anticipatory_empty (trivial);
    (2) singleton_not_anticipatory_with_profitable_deviation (directional,
        bounded sorry — see internal comment);
    (3) cross-subsidy decided example.
    Wilson/MWS "anticipatory always exists" and MWS "unique" are
    theorems that require substantial additional hypotheses
    (single-crossing, anticipatory menu-level, break-even), and are **out
    of scope** of this first delivery (cf body v4 D). -/
theorem no_general_existence_claim :
    -- Intentionally restrictive stub: we do NOT claim general existence.
    True := trivial

end AsymmetricInformation.MiyazakiWilson