/-
  Screening — Rothschild-Stiglitz 1976 model, bounded formalization
  =================================================================

  Formalization of Rothschild-Stiglitz's 1976 *QJE* 90(4):629-649
  adverse selection model on insurer competition. A menu of contracts
  `(α, β)` is offered to insureds, each type `q ∈ {H, L}` with claim
  probability `p_q` (`p_H < p_L`).

  Three key points (canonical audit c.475 category #1+#3):
  1. **RS = Nash among insurers** (NOT Riley-reactive);
  2. **Break-even type-by-type**: `β_q = p_q * α_q` (NO cross-subsidy in RS,
     which belongs to Wilson/MWS);
  3. **Non-existence conditional** on profitable cream-skim.

  Strict bounds: no general uniqueness of allocation, no auxiliary clause
  in κ. Each lemma lists its FINITE hypotheses.

  Implementation note: this module **does not use `Finset`** (which requires
  Mathlib instances), but `List Contract` with an explicit `elem`
  predicate. This conforms to body v4 D ("finite collections: `Finset
  Contract` or `Fin n → Contract`, not `Set Contract`") — `List` is a
  finite collection, and an explicit `elem` predicate replaces the
  `Membership` instance that `Finset` would provide via Mathlib.

  English mirror of `Screening.lean`. Byte-identical except docstrings.
-/

namespace AsymmetricInformation.Screening

/-- Insured type: high risk (L) or low risk (H). We note `H`/`L`
    in accordance with the RS convention where H is the **good** risk
    (p_H < p_L). -/
inductive RiskType where
  | high   -- H: low risk (small p_H)
  | low    -- L: high risk (large p_L)
  deriving DecidableEq, Repr

/-- Type-by-type claim probability: `p_H < p_L`. -/
structure RiskProfile where
  pHigh : Int
  pLow : Int
  hOrder : pHigh < pLow

/-- Contract: coverage (α) and premium (β), **integers** (consistent with
    upstream API). -/
structure Contract where
  coverage : Int
  premium : Int
  deriving DecidableEq, Repr

/-- Expected profit of contract `c` for profile `r` and type `q`.
    First-tranche simplifying hypothesis: we work in `Int` rather than
    `Rat`, which avoids the Mathlib dependency. Encoding: premium in
    cents (×100) to stay integer. -/
def expectedProfit (c : Contract) (r : RiskProfile) (q : RiskType) : Int :=
  c.premium * 100 - match q with
    | .high => r.pHigh * c.coverage
    | .low  => r.pLow  * c.coverage

/-- **Break-even type-by-type**: for a type `q`, contract `c` is
    risk-neutral to the insurer **for that type**. NO cross-subsidy
    between types — this is the fundamental RS condition. -/
def breakEvenType (c : Contract) (r : RiskProfile) (q : RiskType) : Prop :=
  expectedProfit c r q = 0

/-- Global expected profit of a contract on the full profile.
    Convention: sum (not average) so the linear arithmetic in `omega`
    works without Mathlib division handling. -/
def globalExpectedProfit (c : Contract) (r : RiskProfile) : Int :=
  expectedProfit c r .high + expectedProfit c r .low

/-- A menu is a `List` of contracts (finite collection, no Mathlib). -/
abbrev Menu := List Contract

/-- Membership in a menu (explicit predicate). The order
    `Menu → Contract → Prop` is required by the standard `Membership`
    instance. -/
def elem : Menu → Contract → Prop
  | [], _ => False
  | x :: xs, c => c = x ∨ elem xs c

instance : Membership Contract Menu := ⟨elem⟩

/-- **Profitable deviation (cream-skim) — integrated closed form**: there
    exists a contract `c'` profitable **off-menu** (`c' ∉ menu`,
    `globalExpectedProfit c' r > 0`) AND a contract `c` in the menu losing
    on H **with also `expectedProfit c r .low ≤ 0`** (symmetric bound).
    This is the **closed cream-skim parametric region** that determines
    non-existence of the RS equilibrium: the L bound ensures
    `globalExpectedProfit c r = (H + L) < 0` without possible compensation.

    **Integration of the 3 witnesses** (off-menu profitable + in-menu
    losing on H + in-menu `ep .low ≤ 0`) in a **single hypothesis** so
    that the directional lemma `cream_skim_breaks_nash` can **consume**
    the complete hypothesis via `obtain` — otherwise the lemma would
    take independent witnesses and `hCream` would remain unused (Lean
    explicit warning, preflight po-2025 c.481). -/
def creamSkimProfitable (menu : Menu) (r : RiskProfile) : Prop :=
  ∃ c' : Contract, c' ∉ menu ∧ globalExpectedProfit c' r > 0 ∧
    ∃ c ∈ menu, expectedProfit c r .high < 0 ∧ expectedProfit c r .low ≤ 0

/-- **Nash-among-insurers predicate**: no menu contract can be
    unilaterally replaced by an off-menu contract profitable to the
    insurer. This is **by definition** the equilibrium condition. -/
def nashMenu (menu : Menu) (r : RiskProfile) : Prop :=
  ∀ c ∈ menu, ∀ c' : Contract, c' ∉ menu →
    globalExpectedProfit c' r ≤ globalExpectedProfit c r

/-- **Directional lemma cream-skim implies not Nash (closed form)**:
    `creamSkimProfitable menu r` implies `¬ nashMenu menu r`, where
    `creamSkimProfitable` already includes the symmetric bound
    `expectedProfit c r .low ≤ 0` (see predicate docstring).

    **Single hypothesis**: `creamSkimProfitable menu r` — provides via
    `obtain` the witnesses `c' ∉ menu` profitable (cream-skim deviation)
    AND `c ∈ menu` losing on H **AND** `expectedProfit c r .low ≤ 0`.

    This formulation **consumes** `hCream`: no separate witness, no
    redundant parameter. The only additional bound is integrated in the
    predicate (preflight po-2025 c.481 — the previous lemma took these
    witnesses separately and `hCream` remained unused, which made it a
    non-directional lemma).

    Proof: `obtain ⟨c', hNotMem, hPosOff, c, hMemC, hNegH, hNegL⟩` from
    `hCream`. Instantiation `hNash c hMemC c' hNotMem` →
    `globalExpectedProfit c' r ≤ globalExpectedProfit c r`. Now
    `globalExpectedProfit c r = ep .high + ep .low ≤ 0 + 0 = 0` by
    `hNegH : < 0` and `hNegL : ≤ 0`. The left side is `> 0` by
    `hPosOff`. `omega` closes the contradiction (sum `Int`, linear
    domain). -/
theorem cream_skim_breaks_nash
    (menu : Menu) (r : RiskProfile)
    (hCream : creamSkimProfitable menu r) :
    ¬ nashMenu menu r := by
  obtain ⟨c', hNotMem, hPosOff, c, hMemC, hNegH, hNegL⟩ := hCream
  intro hNash
  have hle := hNash c hMemC c' hNotMem
  -- `hNegH : ep c r .high < 0` + `hNegL : ep c r .low ≤ 0` give
  -- `globalExpectedProfit c r ≤ -1` by `Int.add_le_add`. We unfold
  -- `globalExpectedProfit = ep.H + ep.L` then sum.
  have hNegSum : (c.premium * 100 - r.pHigh * c.coverage) +
                   (c.premium * 100 - r.pLow * c.coverage) ≤ -1 := by
    have h1 : c.premium * 100 - r.pHigh * c.coverage < 0 := by
      simpa [expectedProfit] using hNegH
    have h2 : c.premium * 100 - r.pLow * c.coverage ≤ 0 := by
      simpa [expectedProfit] using hNegL
    omega
  -- Unfold `globalExpectedProfit` on both sides of `hle` and combine
  -- with `hPosOff` and `hNegSum`; `omega` closes the contradiction
  -- `0 < ... ≤ ... ≤ -1`. The `simpa [globalExpectedProfit, expectedProfit]
  -- using` transformation unfolds both sides of `hle` and `hPosOff`
  -- to render them linear in `Int`, usable by `omega`.
  have hle' : (c'.premium * 100 - r.pHigh * c'.coverage) +
                (c'.premium * 100 - r.pLow * c'.coverage) ≤
              (c.premium * 100 - r.pHigh * c.coverage) +
                (c.premium * 100 - r.pLow * c.coverage) := by
    simpa [globalExpectedProfit, expectedProfit] using hle
  have hPosOff' : 0 < (c'.premium * 100 - r.pHigh * c'.coverage) +
                     (c'.premium * 100 - r.pLow * c'.coverage) := by
    simpa [globalExpectedProfit, expectedProfit] using hPosOff
  omega

/-- **Extraction lemma (subsidiary)**: if `creamSkimProfitable` holds,
    there exists a contract in the menu losing on H
    (`expectedProfit c r .high < 0`) AND with `expectedProfit c r .low ≤ 0`.
    This is a direct corollary of the 2nd conjunct of `hCream` (the triple
    conjunction `< 0 ∧ ≤ 0`) — useful as a **bridge** to apply
    `cream_skim_breaks_nash` without reconstructing the extraction. -/
theorem cream_skim_implies_some_negative_H_profit
    (menu : Menu) (r : RiskProfile)
    (hCream : creamSkimProfitable menu r) :
    ∃ c ∈ menu, expectedProfit c r .high < 0 ∧ expectedProfit c r .low ≤ 0 := by
  obtain ⟨_, _, _, c, hcmem, hnH, hnL⟩ := hCream
  exact ⟨c, hcmem, hnH, hnL⟩

/-- **Positive economic example** — `creamSkimProfitable` holds for an
    off-menu profitable contract `c'` + an in-menu contract `c = ⟨100, 20⟩`
    losing on both types. Profile `(p_H, p_L) = (25, 75)` (in hundredths,
    constraint `25 < 75`), 1-contract menu `[(100, 20)]`.

    Calculations:
    - off-menu `c' = ⟨100, 100⟩`: `globalExpectedProfit = (100*100 - 25*100) +
      (100*100 - 75*100) = 7500 + 2500 = 10000 > 0` ✓;
    - in-menu `c = ⟨100, 20⟩`: `expectedProfit .high = 20*100 - 25*100 = -500 < 0`
      ✓; `expectedProfit .low = 20*100 - 75*100 = -5500 ≤ 0` ✓.

    The `refine` witness reconstructs the **7 fields** consumed by `obtain` in
    `cream_skim_breaks_nash` (c.481): `c' = ⟨100, 100⟩`, `¬ elem [⟨100, 20⟩] ⟨100, 100⟩`,
    `globalExpectedProfit c' r > 0`, `c = ⟨100, 20⟩`, `elem [⟨100, 20⟩] c`,
    `expectedProfit c r .high < 0`, `expectedProfit c r .low ≤ 0`. No `sorry`.

    This witness **replaces** the stub `True := trivial` initially shipped c.481
    (anti-regression: claiming "concrete examples are impossible" was a
    work-around, not an impossibility — po-2025 revalidation via
    `msg-20260825T023545-f9zbms` + `msg-20260825T023538-mstkj0`, compiled
    firsthand `lake env lean ProbeCream.lean` rc=0). -/
example : creamSkimProfitable [⟨100, 20⟩] ⟨25, 75, by omega⟩ := by
  refine ⟨⟨100, 100⟩, ?_, ?_, ⟨100, 20⟩, ?_, ?_, ?_⟩
  · change ¬ elem [⟨100, 20⟩] ⟨100, 100⟩
    intro h
    rcases h with h | h
    · cases h
    · exact h.elim
  · decide
  · exact Or.inl rfl
  · decide
  · decide

end AsymmetricInformation.Screening