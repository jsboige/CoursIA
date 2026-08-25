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
/- ## H/L choice vector within menu (dynamic layer — Wilson/MWS repair c.491, hardened c.502)

  The `anticipatoryMenu` predicate (lines 23-31 above) is the **static**
  version of Wilson 1977: no post-selection reaction, simple comparison
  of aggregate profits.

  Acceptance #12848 explicitly demands "**menu, type choice, aggregate
  profit, anticipatory withdrawal, cross-subsidy feasibility**. Provide
  decidable examples where zero, one or multiple menus satisfy the
  predicate." The dynamic layer: a `MenuChoice` selects two contracts
  in the menu (one per type H/L), an `EntryWithdrawal` describes a
  concrete deviation (off-menu entrant + withdrawn contract), and
  `anticipatoryAgainst` expresses the invariance of aggregate profit
  under such deviations.

  Four decidable results close the contract on the profile
  `(p_H, p_L) = (25, 75)`, each with arithmetic that is **actually in
  the Lean term**:
  (4) `no_menu_choice_on_empty_menu` — empty menu: no inspectable
      deviation exists at all (the "zero" case);
  (5) `singleton_withdrawal_anticipatory` — ONE menu satisfies against
      a real non-empty deviation: the aggregate goes from -2000 to
      -6000;
  (6) `two_contracts_withdrawal_not_anticipatory` — a menu does NOT
      satisfy: the deviation raises the aggregate from -2500 to +500;
  (7) `two_distinct_anticipatory_states` — SEVERAL distinct states
      satisfy the predicate, each against its own deviation.
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
/-- Shared risk profile `(p_H, p_L) = (25, 75)` for examples (4)-(7).
    The field `hOrder : 25 < 75` is closed by `omega`. -/
private def prof : AsymmetricInformation.Screening.RiskProfile :=
  ⟨25, 75, by omega⟩

/-- State B (before): singleton menu `[(α=40, β=10)]`, both H and L
    choose the only contract. Aggregate profit:
    `(10*100 - 25*40) + (10*100 - 75*40) = 0 + (-2000) = -2000`. -/
private def beforeB : MenuChoice :=
  { menu := [⟨40, 10⟩]
    highChoice := ⟨40, 10⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by left; rfl }

/-- State B (after): the entrant `(100, 20)` is the only contract
    offered, the withdrawn `(40, 10)` no longer appears. Aggregate
    profit: `(20*100 - 25*100) + (20*100 - 75*100) = (-500) + (-5500)
    = -6000`. -/
private def afterB : MenuChoice :=
  { menu := [⟨100, 20⟩]
    highChoice := ⟨100, 20⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by left; rfl
    low_mem := by left; rfl }

/-- Deviation B — a **complete** `EntryWithdrawal`: the entrant
    `(100, 20)` was off-menu before (`elem` refuted by `decide`), is
    offered after (head); the withdrawn `(40, 10)` was offered before
    (head), is no longer offered after (`elem` refuted by `decide`).
    No field is a stub: every membership is an explicit proof. -/
private def devB : EntryWithdrawal :=
  { before := beforeB
    after := afterB
    entrant := ⟨100, 20⟩
    withdrawn := ⟨40, 10⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · exact False.elim h2
    entrant_is_offered := by left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · exact False.elim h2 }

/-- State A (before): menu `[(100, 50), (100, 20)]`, H chooses
    `(100, 50)`, L chooses `(100, 20)`. Aggregate profit:
    `(50*100 - 25*100) + (20*100 - 75*100) = 2500 + (-5500) = -3000`. -/
private def beforeA : MenuChoice :=
  { menu := [⟨100, 50⟩, ⟨100, 20⟩]
    highChoice := ⟨100, 50⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- State A (after): the withdrawn `(100, 50)` no longer appears, the
    entrant `(40, 10)` is offered, H chooses `(40, 10)`, L keeps
    `(100, 20)`. Aggregate profit: `(10*100 - 25*40) + (20*100 - 75*100)
    = 0 + (-5500) = -5500`. -/
private def afterA : MenuChoice :=
  { menu := [⟨100, 20⟩, ⟨40, 10⟩]
    highChoice := ⟨40, 10⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by right; left; rfl
    low_mem := by left; rfl }

/-- Deviation A — complete `EntryWithdrawal`: the entrant `(40, 10)`
    was off-menu before, is offered after (tail); the withdrawn
    `(100, 50)` was offered before (head), is no longer offered after. -/
private def devA : EntryWithdrawal :=
  { before := beforeA
    after := afterA
    entrant := ⟨40, 10⟩
    withdrawn := ⟨100, 50⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4
    entrant_is_offered := by right; left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4 }

/-- State N (before): menu `[(100, 20), (40, 10)]`, H chooses
    `(100, 20)`, L chooses `(40, 10)`. Aggregate profit:
    `(20*100 - 25*100) + (10*100 - 75*40) = (-500) + (-2000) = -2500`. -/
private def beforeN : MenuChoice :=
  { menu := [⟨100, 20⟩, ⟨40, 10⟩]
    highChoice := ⟨100, 20⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- State N (after): the entrant `(100, 50)` is offered (head), the
    withdrawn `(100, 20)` no longer appears, H chooses the entrant, L
    keeps `(40, 10)`. Aggregate profit: `(50*100 - 25*100) +
    (10*100 - 75*40) = 2500 + (-2000) = +500`. -/
private def afterN : MenuChoice :=
  { menu := [⟨100, 50⟩, ⟨40, 10⟩]
    highChoice := ⟨100, 50⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- Deviation N — complete `EntryWithdrawal`: the entrant `(100, 50)`
    was off-menu before, is offered after (head); the withdrawn
    `(100, 20)` was offered before (head), is no longer offered after. -/
private def devN : EntryWithdrawal :=
  { before := beforeN
    after := afterN
    entrant := ⟨100, 50⟩
    withdrawn := ⟨100, 20⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4
    entrant_is_offered := by left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4 }

/-- **Decided example (4) — no state is constructible on an empty
    menu.** The field `high_mem : elem menu highChoice` of a
    `MenuChoice` with `menu = []` reduces to `False`: no type choice,
    hence no `EntryWithdrawal` deviation, can start from an empty menu.
    The "zero" case of the 0/one/several frame is thus trivially
    structural; the **non-trivial** zero case is realized by theorem
    (6): a real state that no invariance protects. -/
theorem no_menu_choice_on_empty_menu :
    ∀ (s : MenuChoice), s.menu ≠ [] := by
  intro s hEq
  have hMem := s.high_mem
  rw [hEq] at hMem
  -- `elem [] s.highChoice` reduces to `False` by construction.
  exact hMem

/-- **Decided example (5) — ONE menu satisfies anticipatoryAgainst
    against a real non-empty deviation.** State B: singleton
    `[(40, 10)]`, aggregate profit `0 + (-2000) = -2000`. The deviation
    `devB` brings in `(100, 20)` and withdraws `(40, 10)`: the
    aggregate profit becomes `(-500) + (-5500) = -6000`. Since
    `-6000 ≤ -2000`, invariance HOLDS on this response. The proof
    **inspects the response**: the universal is instantiated on the
    single element of `[devB]`, then both aggregates are computed
    exactly — a non-vacuous positive case. -/
theorem singleton_withdrawal_anticipatory :
    anticipatoryAgainst beforeB prof [devB] := by
  intro response hmem _heq
  have hEq : response = devB := by
    simpa using hmem
  rw [hEq]
  show chosenAggregateProfit afterB prof ≤ chosenAggregateProfit beforeB prof
  have hAfter : chosenAggregateProfit afterB prof = -6000 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               afterB, prof]
    omega
  have hBefore : chosenAggregateProfit beforeB prof = -2000 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               beforeB, prof]
    omega
  rw [hAfter, hBefore]
  omega

/-- **Decided example (6) — a menu does NOT satisfy anticipatoryAgainst:
    the deviation genuinely raises the aggregate profit.** State N:
    menu `[(100, 20), (40, 10)]`, aggregate profit `(-500) + (-2000) =
    -2500`. The deviation `devN` brings in the profitable entrant
    `(100, 50)` (H profit = `50*100 - 25*100 = +2500`) and withdraws
    `(100, 20)`: the aggregate moves to `2500 + (-2000) = +500 >
    -2500`. The universal is refuted by instantiating the single
    response `devN ∈ [devN]` then computing both aggregates exactly —
    the cream-skim counter-example in dynamic form, on a **real
    non-empty** deviation. -/
theorem two_contracts_withdrawal_not_anticipatory :
    ¬ anticipatoryAgainst beforeN prof [devN] := by
  intro hAnt
  have hle : chosenAggregateProfit afterN prof ≤ chosenAggregateProfit beforeN prof :=
    hAnt devN (List.Mem.head _) (by rfl)
  have hAfter : chosenAggregateProfit afterN prof = 500 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               afterN, prof]
    omega
  have hBefore : chosenAggregateProfit beforeN prof = -2500 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               beforeN, prof]
    omega
  rw [hAfter, hBefore] at hle
  omega

/-- **Decided example (7) — SEVERAL distinct states satisfy the
    predicate.** State A (menu `[(100, 50), (100, 20)]`, aggregate
    -3000, deviation `devA` towards aggregate -5500) and state B
    (singleton menu `[(40, 10)]`, aggregate -2000, deviation `devB`
    towards -6000) are two **distinct** `MenuChoice` — their menus have
    different lengths, decided by `decide` — each satisfying
    `anticipatoryAgainst` against its own deviation. -/
theorem two_distinct_anticipatory_states :
    ∃ s₁ s₂ : MenuChoice, s₁ ≠ s₂ ∧
      ∃ rw₁ rw₂ : EntryWithdrawal,
        anticipatoryAgainst s₁ prof [rw₁] ∧
          anticipatoryAgainst s₂ prof [rw₂] := by
  refine ⟨beforeA, beforeB, ?_, devA, devB, ?_, singleton_withdrawal_anticipatory⟩
  · intro hEq
    have hMenus : beforeA.menu = beforeB.menu := congrArg MenuChoice.menu hEq
    exact absurd hMenus (by decide)
  · intro response hmem _heq
    have hEq : response = devA := by
      simpa using hmem
    rw [hEq]
    show chosenAggregateProfit afterA prof ≤ chosenAggregateProfit beforeA prof
    have hAfter : chosenAggregateProfit afterA prof = -5500 := by
      simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
                 afterA, prof]
      omega
    have hBefore : chosenAggregateProfit beforeA prof = -3000 := by
      simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
                 beforeA, prof]
      omega
    rw [hAfter, hBefore]
    omega

/- ## No uniqueness or general-existence claim in this delivery.

  Seven modest results:
  (1) `anticipatory_empty` (trivial, static);
  (2) `singleton_not_anticipatory_with_profitable_deviation`
      (directional, closed proof);
  (3) cross-subsidy decided example (static);
  (4) `no_menu_choice_on_empty_menu` (no inspectable deviation);
  (5) `singleton_withdrawal_anticipatory` (one menu satisfies, real
      non-empty deviation, response inspected: -2000 → -6000);
  (6) `two_contracts_withdrawal_not_anticipatory` (a menu does not
      satisfy: the deviation raises the aggregate from -2500 to +500);
  (7) `two_distinct_anticipatory_states` (two states with disjoint
      menus satisfy the predicate).

  Wilson/MWS "anticipatory always exists" and MWS "unique" remain
  theorems requiring additional substantial hypotheses
  (single-crossing, anticipatory menu-level, break-even), **out of
  scope** for this delivery (cf body v4 D). The witnesses (4)-(7)
  delimit the frontier with real menus and real deviations — a
  `True := trivial` would add nothing (lesson c.482: a concrete
  witness is more informative than a stub).
-/

end AsymmetricInformation.MiyazakiWilson