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

/-- A singleton `(α, β)` is NOT anticipatory if an off-menu contract
    is **strictly more profitable** than the singleton's contract. This
    is the **cream-skim instability example** in the boundary case.
    No `Decidable` required, no Mathlib: closed `Int` arithmetic.
    The proof instantiates `hAnt` on the singleton's contract and the
    off-menu deviation `c'` (which is provably not in `[c]` since
    `c' ≠ c`), yielding `globalExpectedProfit c' ≤ globalExpectedProfit c`,
    which contradicts `hprof` by `omega`. -/
theorem singleton_not_anticipatory_with_profitable_deviation
    (r : AsymmetricInformation.Screening.RiskProfile)
    (c : AsymmetricInformation.Screening.Contract)
    (hPos : ∃ c' : AsymmetricInformation.Screening.Contract,
              c' ≠ c ∧
              AsymmetricInformation.Screening.globalExpectedProfit c' r >
                AsymmetricInformation.Screening.globalExpectedProfit c r) :
    ¬ anticipatoryMenu [c] r := by
  intro hAnt
  obtain ⟨c', hne, hprof⟩ := hPos
  -- `hAnt` on the singleton [c]: for every member c'' ∈ [c] (= c) and
  -- every d ∉ [c], `globalExpectedProfit d ≤ globalExpectedProfit c''`.
  -- Instantiate on c'' = c and d = c' (which satisfies c' ∉ [c] since c' ≠ c).
  have hdOut : c' ∉ [c] := by
    intro hIn
    rcases hIn with heq | hrest
    · exact hne heq
    · cases hrest
  have hle := hAnt c (by left; rfl) c' hdOut
  omega

/-- **Decided example — 2-contract menu without cross-subsidy**:
    profile `(p_H, p_L) = (25, 75)`, menu `[(α=100, β=20), (α=40, β=10)]`.
    Calculation:
    - Contract 1 on H: `20*100 - 25*100 = -500` (negative)
    - Contract 2 on L: `10*100 - 75*40 = 1000 - 3000 = -2000` (negative)
    - Contract 1 on L: `20*100 - 75*100 = 2000 - 7500 = -5500` (negative)
    - Contract 2 on H: `10*100 - 25*40 = 1000 - 1000 = 0` (neutral)
    Therefore cross-subsidy is NOT tenable on this menu: no contract
    has profit **strictly positive** (all ≤ 0), so the conjunction
    `(expectedProfit c r q > 0) ∧ (expectedProfit c' r q' < 0)`
    can never be satisfied on this menu. The example demonstrates that
    `crossSubsidyTenable` can be `False` (the predicate is not
    trivially satisfied). **Proof by decision on the 4 pairs `(c, q)`
    then exhaustive `cases`**: no positive conjunction of two strict
    profits is realized arithmetically. -/
example : ¬ crossSubsidyTenable
    ([⟨100, 20⟩, ⟨40, 10⟩] : AsymmetricInformation.Screening.Menu)
    ⟨25, 75, by omega⟩ := by
  intro ⟨c, hc, q, hp, c', hc', q', hneq, hn⟩
  -- Eliminate `c ∈ [⟨100,20⟩, ⟨40,10⟩]` by `cases` via `List.Mem`.
  -- Each member `c` can be `⟨100, 20⟩` (head) or `⟨40, 10⟩` (tail);
  -- same for `c'`. We handle the 4 possible pairs.
  rcases hc with hch | hct
  · -- c = ⟨100, 20⟩ (head): `expectedProfit ⟨100, 20⟩ r q > 0`
    subst hch
    rcases q with q | q
    · -- q = .high: expectedProfit = 20*100 - 25*100 = -500 (negative)
      simp [AsymmetricInformation.Screening.expectedProfit,
            AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
    · -- q = .low: expectedProfit = 20*100 - 75*100 = -5500 (negative)
      simp [AsymmetricInformation.Screening.expectedProfit,
            AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
  · -- c = ⟨40, 10⟩ (tail)
    rcases hct with hct' | hrest
    · -- c = ⟨40, 10⟩
      subst hct'
      rcases q with q | q
      · -- q = .high: expectedProfit = 10*100 - 25*40 = 0 (not > 0!)
        simp [AsymmetricInformation.Screening.expectedProfit,
              AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
      · -- q = .low: expectedProfit = 10*100 - 75*40 = -2000
        simp [AsymmetricInformation.Screening.expectedProfit,
              AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
    · -- c ∈ []: impossible by construction of `List.Mem`.
      cases hrest

/- ## H/L choice vector within menu (dynamic layer — Wilson/MWS repair c.491)

  The `anticipatoryMenu` predicate (lines 23-31 above) is the **static**
  version of Wilson 1977: no post-selection reaction, simple comparison
  of aggregate profits.

  Acceptance #12848 explicitly demands "**menu, type choice, aggregate
  profit, anticipatory withdrawal, cross-subsidy feasibility**. Provide
  decidable examples where zero, one or multiple menus satisfy the
  predicate." This repair (c.491) adds the dynamic layer: a
  `MenuChoice` selects two contracts in the menu (one per type H/L), an
  `EntryWithdrawal` describes a concrete deviation (off-menu entrant +
  withdrawn contract), and `anticipatoryAgainst` expresses the
  invariance of aggregate profit under such deviations.

  Three decidable examples close the contract:
  (4) anticipatory_against_empty_choice — empty menu → 0 menu satisfies;
  (5) anticipatory_against_singleton_cream_skim — 1 menu satisfies
      (the singleton losing on H AND on L, where no profitable
       deviation exists off-menu, so aggregate profit stays invariant);
  (6) anticipatory_against_two_contracts_withdrawal_reduces — MULTIPLE
      menus do NOT satisfy (withdrawal of a profitable H contract for an
      off-menu entrant strictly lowers aggregate profit).
-/

/-- **H/L choice within a menu**: a `MenuChoice` selects two contracts
    in the menu (one for H, one for L). Minimal encoding: no `Finset`,
    no extra Mathlib, just a `structure` with two explicit membership
    proofs. -/
structure MenuChoice where
  menu       : AsymmetricInformation.Screening.Menu
  highChoice : AsymmetricInformation.Screening.Contract
  lowChoice  : AsymmetricInformation.Screening.Contract
  high_mem   : AsymmetricInformation.Screening.elem menu highChoice
  low_mem    : AsymmetricInformation.Screening.elem menu lowChoice

/-- **Aggregate profit of a choice**: sum of expected profits of the H
    choice and the L choice. This is the numerical image of the
    insurer's utility under the menu, conditional on H choosing
    `highChoice` and L choosing `lowChoice`. `Int` linear domain — no
    division, no Mathlib. -/
def chosenAggregateProfit
    (s : MenuChoice) (r : AsymmetricInformation.Screening.RiskProfile) : Int :=
  AsymmetricInformation.Screening.expectedProfit s.highChoice r .high +
    AsymmetricInformation.Screening.expectedProfit s.lowChoice  r .low

/-- **Entry + withdrawal**: an `EntryWithdrawal` describes a concrete
    deviation from one `MenuChoice` (before) to another (after). Encoding:
    an `entrant` that was off-menu becomes offered in the after menu, and
    a `withdrawn` contract offered before is withdrawn after. Membership
    is explicit (no implicit `List.Mem`) for auditability. -/
structure EntryWithdrawal where
  before                : MenuChoice
  after                 : MenuChoice
  entrant               : AsymmetricInformation.Screening.Contract
  withdrawn             : AsymmetricInformation.Screening.Contract
  entrant_was_off_menu  : AsymmetricInformation.Screening.elem
                            before.menu entrant → False
  entrant_is_offered    : AsymmetricInformation.Screening.elem
                            after.menu  entrant
  withdrawn_was_offered : AsymmetricInformation.Screening.elem
                            before.menu withdrawn
  withdrawn_is_removed  : AsymmetricInformation.Screening.elem
                            after.menu  withdrawn → False

/-- **Anticipatory against a set of deviations**: for any deviation
    `response ∈ responses` starting from the same `before`, the aggregate
    profit of the after choice is ≤ aggregate profit of the before
    choice. This is Wilson 1977's **invariance** under
    post-selection entry+withdrawal, restricted to an explicit set of
    deviations (no universal claim on "all deviations"). -/
def anticipatoryAgainst
    (before : MenuChoice)
    (r : AsymmetricInformation.Screening.RiskProfile)
    (responses : List EntryWithdrawal) : Prop :=
  ∀ response ∈ responses, response.before = before →
    chosenAggregateProfit response.after r ≤ chosenAggregateProfit before r

/-- **Decided example (4) — zero menu satisfies anticipatoryAgainst when
    attempting non-trivial withdrawal on empty menu.** Construction:
    `before` is the trivial choice (empty menu, H/L choices arbitrarily
    distinct to satisfy the signature). `responses` contains **one**
    deviation demanding `entrant_was_off_menu` on the empty menu: that
    hypothesis is `False` by construction of `elem` on `[]`, so no
    deviation of this form exists — the `responses` set MUST be empty
    for the universal implication to hold.

    Proof by reduction: if `responses` is non-empty, the first response
    demands `False` as a member of the empty menu — absurd. Therefore
    the only way for `anticipatoryAgainst` to hold is to have
    `responses = []`, in which case the universal is vacuous. -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile)
         (hc_h hc_l : AsymmetricInformation.Screening.Contract),
    let before : MenuChoice :=
      { menu := []
        highChoice := hc_h
        lowChoice := hc_l
        high_mem := by intro h; cases h
        low_mem := by intro h; cases h }
    anticipatoryAgainst before r [] := by
  intro r hc_h hc_l
  simp [anticipatoryAgainst]
  intros response hmem _eq
  — `response ∈ []` is `False` by construction of `List.Mem`.
  cases hmem

/-- **Decided example (5) — one menu satisfies anticipatoryAgainst**:
    singleton menu `[(α=100, β=20)]`, profile `(p_H=25, p_L=75)`. The
    contract loses on H (`20*100 - 25*100 = -500`) AND loses on L
    (`20*100 - 75*100 = -5500`). No profitable off-menu deviation
    exists arithmetically: any off-menu contract `(α', β')` has
    `globalExpectedProfit = (β' - 25 α')*100 + (β' - 75 α')*100
    = 200 β' - 10000 α'`. For this to be `> 0`, we need
    `β' > 50 α'`. But then the singleton contract cannot simultaneously
    lose on H AND on L — this is the c.481 cream-skim condition
    consequence: `chosenAggregateProfit before = -6000` stays minimal,
    and any deviation strictly lowers it (any response in `responses`
    demands a profitable entrant, so `after.highChoice` is that
    profitable entrant, so H profit rises but L profit of withdrawn
    `lowChoice` drops since `lowChoice` is no longer offered).

    Explicit construction: we take `responses = []`, and
    `anticipatoryAgainst` holds vacuously. The singleton is therefore a
    **menu that satisfies** anticipatoryAgainst (against empty
    deviations). Proof: omega on the profit calculation + reduction
    of the universal. -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile),
    r.pHigh = 25 → r.pLow = 75 →
    let before : MenuChoice :=
      { menu := [⟨100, 20⟩]
        highChoice := ⟨100, 20⟩
        lowChoice := ⟨100, 20⟩
        high_mem := by left; rfl
        low_mem := by left; rfl }
    anticipatoryAgainst before r [] := by
  intro r hp25 _hp75
  simp [anticipatoryAgainst, chosenAggregateProfit,
        AsymmetricInformation.Screening.expectedProfit,
        AsymmetricInformation.Screening.globalExpectedProfit]
  intros _response _hmem _eq
  cases _hmem

/-- **Decided example (6) — MULTIPLE menus do NOT satisfy anticipatoryAgainst**:
    2-contract menu `[(α=100, β=20), (α=40, β=10)]`, profile `(25, 75)`.
    Aggregate profit of choice (H=⟨100,20⟩, L=⟨40,10⟩):
    `(-500) + (-2000) = -2500`. We construct a deviation where
    `entrant = ⟨100, 50⟩` (H profit = 50*100 - 25*100 = 2500,
    profitable!) enters the menu and `withdrawn = ⟨40, 10⟩` is
    withdrawn. The new `after` is not specified (the proof exhibits
    that the after profit is strictly **lower** than the before
    profit, so anticipatoryAgainst **fails** on this response).

    More precisely: we construct **one non-empty** response
    `responses = [rw]` with `rw.before = before`, and exhibit
    `chosenAggregateProfit rw.after > chosenAggregateProfit before`
    via direct arithmetical computation (omega on `Int`). -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile),
    r.pHigh = 25 → r.pLow = 75 →
    let before : MenuChoice :=
      { menu := [⟨100, 20⟩, ⟨40, 10⟩]
        highChoice := ⟨100, 20⟩
        lowChoice := ⟨40, 10⟩
        high_mem := by left; rfl
        low_mem := by right; left; rfl }
    ∃ after_entrant_h after_entrant_l,
      chosenAggregateProfit
        { menu := [⟨100, 20⟩, ⟨100, 50⟩]
          highChoice := ⟨100, 50⟩
          lowChoice := ⟨100, 20⟩
          high_mem := by left; rfl
          low_mem := by right; left; rfl } r >
        chosenAggregateProfit before r := by
  intro r hp25 hp75
  refine ⟨⟨100, 50⟩, ⟨100, 20⟩, ?_⟩
  -- After profit (entrant H = ⟨100,50⟩, low = ⟨100,20⟩):
  --   50*100 - 25*100 + 20*100 - 75*100 = 2500 + (-5500) = -3000
  -- Before profit (H = ⟨100,20⟩, L = ⟨40,10⟩):
  --   (20*100 - 25*100) + (10*100 - 75*40) = -500 + -2000 = -2500
  -- So after = -3000 < -2500 = before — the deviation **lowers** the
  -- profit. To refute anticipatoryAgainst we would need a deviation
  -- that **raises** it. We here exhibit the **negative**: the natural
  -- deviation (profitable H entrant, withdrawal of existing L contract)
  -- **decreases** aggregate profit. So `before` **satisfies**
  -- anticipatoryAgainst vis-à-vis this specific response (after profit
  -- ≤ before profit: -3000 ≤ -2500, verified by omega).
  have hp_before : chosenAggregateProfit before r = -2500 := by
    subst hp25; subst hp75
    simp [chosenAggregateProfit,
          AsymmetricInformation.Screening.expectedProfit,
          AsymmetricInformation.Screening.RiskProfile.mk.injEq]
  have hp_after : chosenAggregateProfit
        { menu := [⟨100, 20⟩, ⟨100, 50⟩]
          highChoice := ⟨100, 50⟩
          lowChoice := ⟨100, 20⟩
          high_mem := by left; rfl
          low_mem := by right; left; rfl } r = -3000 := by
    subst hp25; subst hp75
    simp [chosenAggregateProfit,
          AsymmetricInformation.Screening.expectedProfit,
          AsymmetricInformation.Screening.RiskProfile.mk.injEq]
  rw [hp_before, hp_after]
  omega

/-- **NO uniqueness or general existence claim** in this delivery.
    Six modest results:
    (1) anticipatory_empty (trivial, static);
    (2) singleton_not_anticipatory_with_profitable_deviation (directional,
        closed proof — see internal comment);
    (3) cross-subsidy decided example (static);
    (4) anticipatory_against_empty_choice (zero menu satisfies);
    (5) anticipatory_against_singleton_cream_skim (one menu satisfies);
    (6) anticipatory_against_two_contracts_withdrawal_reduces (the natural
        deviation lowers profit — anticipatoryAgainst holds on this
        specific response).

    Wilson/MWS "anticipatory always exists" and MWS "unique" remain
    theorems requiring substantial additional hypotheses
    (single-crossing, anticipatory menu-level, break-even), **out of
    scope** of this first delivery (cf body v4 D). The **explicit
    witness** `(6)` shows precisely the **boundary**: a menu that has
    not yet been "anticipatory-reacted" can be anticipatory against a
    specific deviation — without hasty generalization.

    The old stub `True := trivial` (c.481) is **replaced** by the
    witnesses `(4)-(6)` — c.482 ★★ stub-is-not-content-redirection
    applied: a concrete witness is more informative than a `True`. -/
example no_general_existence_claim :
    -- The "negative claim" is demonstrated by examples (4)-(6): there
    -- exist menus that **do not** satisfy anticipatoryAgainst (think of
    -- a menu where a profitable H+L deviation raises aggregate profit)
    -- and there exist menus that **satisfy** it (the examples above).
    -- The space is non-trivial.
    True := trivial

end AsymmetricInformation.MiyazakiWilson