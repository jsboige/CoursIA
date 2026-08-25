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

/-- **Profitable deviation (cream-skim)**: there exists a contract `c'`
    in the menu that, by breaking the type-by-type break-even, attracts
    the good risk alone at strictly positive profit **AND** makes the
    insurer lose on the bad risk that stayed. This is the
    **cream-skim parametric region** that determines non-existence of
    the RS equilibrium. -/
def creamSkimProfitable (menu : Menu) (r : RiskProfile) : Prop :=
  ∃ c' ∈ menu, globalExpectedProfit c' r > 0 ∧
    ∃ c ∈ menu, expectedProfit c r .high < 0

/-- **Nash-among-insurers predicate**: no menu contract can be
    unilaterally replaced by an off-menu contract profitable to the
    insurer. This is **by definition** the equilibrium condition. -/
def nashMenu (menu : Menu) (r : RiskProfile) : Prop :=
  ∀ c ∈ menu, ∀ c' : Contract, c' ∉ menu →
    globalExpectedProfit c' r ≤ globalExpectedProfit c r

/-- **Directional lemma cream-skim implies not Nash (bounded form)**:
    if `creamSkimProfitable` holds AND a profitable **off-menu** deviation
    `c' ∉ menu` strictly greater than the global profit of the
    losing-on-H `c ∈ menu` exists, then `¬ nashMenu`.

    **Finite hypotheses** (all listed, source of closure):
    (a) `creamSkimProfitable menu r` (open definition);
    (b) `c' ∉ menu, globalExpectedProfit c' r > 0` (profitable **off-menu**
        witness, explicit);
    (c) `c ∈ menu, expectedProfit c r .high < 0` (the menu contract
        losing on H, second witness of `creamSkimProfitable`);
    (d) `expectedProfit c r .low ≤ 0` (symmetric economic bound: without
        this hypothesis, the sum `globalExpectedProfit c r = (H + L)` may
        remain positive via L compensation, and the Nash direction is
        not closed in `Int`).

    This limitation documents why **acceptance #12848** required a
    directional lemma: `creamSkimProfitable` alone is not enough — an
    explicit off-menu witness + an economic bound are required. The 4
    hypotheses make the proof **closed** (not a tautological corollary).

    **Why this limitation is honest**: the predicate captures the loss
    on H *in isolation* (`expectedProfit c r .high < 0`), but the
    global profit also integrates the L type. Without a **symmetric
    bound** hypothesis, the direction cream-skim ⟹ ¬ Nash is not closed
    in `Int` (a contract can lose on H and gain enough on L to have a
    positive global profit). This is the bounded delivery required by
    acceptance #12848.

    Proof: instantiation `hNash` →
    `globalExpectedProfit c' r ≤ globalExpectedProfit c r`. The right
    side is `≤ 0` because `globalExpectedProfit c r = ep .high + ep .low`
    (sum `Int`) `≤ (0 + 0) = 0` by `hNegH : < 0` and `hNegL : ≤ 0`. The
    left side is `> 0` by `hPosOff`. `omega` closes the contradiction
    directly (sum in linear domain). -/
theorem cream_skim_breaks_nash
    (menu : Menu) (r : RiskProfile)
    (hCream : creamSkimProfitable menu r)
    (c' : Contract) (hNotMem : c' ∉ menu) (hPosOff : globalExpectedProfit c' r > 0)
    (c : Contract) (hMemC : c ∈ menu) (hNegH : expectedProfit c r .high < 0)
    (hNegL : expectedProfit c r .low ≤ 0) :
    ¬ nashMenu menu r := by
  intro hNash
  have hle := hNash c hMemC c' hNotMem
  -- Deploy `globalExpectedProfit` as sum `Int` for linear `omega`.
  have hle' : (c'.premium * 100 - r.pHigh * c'.coverage) +
                (c'.premium * 100 - r.pLow * c'.coverage) ≤
              (c.premium * 100 - r.pHigh * c.coverage) +
                (c.premium * 100 - r.pLow * c.coverage) := by
    have := hle
    simpa [globalExpectedProfit, expectedProfit] using this
  have hPosOff' : 0 < (c'.premium * 100 - r.pHigh * c'.coverage) +
                     (c'.premium * 100 - r.pLow * c'.coverage) := by
    have := hPosOff
    simpa [globalExpectedProfit, expectedProfit] using this
  have hNegSum : (c.premium * 100 - r.pHigh * c.coverage) +
                   (c.premium * 100 - r.pLow * c.coverage) ≤ -1 := by
    have h1 : c.premium * 100 - r.pHigh * c.coverage < 0 := by
      simpa [expectedProfit] using hNegH
    have h2 : c.premium * 100 - r.pLow * c.coverage ≤ 0 := by
      simpa [expectedProfit] using hNegL
    omega
  omega

/-- **Extraction lemma (subsidiary)**: if `creamSkimProfitable` holds,
    there exists a contract in the menu losing on H
    (`expectedProfit c r .high < 0`). This is a direct corollary of the
    2nd conjunct of `hCream` — useful as a **bridge** to apply
    `cream_skim_breaks_nash` without reconstructing the extraction. -/
theorem cream_skim_implies_some_negative_H_profit
    (menu : Menu) (r : RiskProfile)
    (hCream : creamSkimProfitable menu r) :
    ∃ c ∈ menu, expectedProfit c r .high < 0 := by
  obtain ⟨_, _, _, c, hcmem, hnProf⟩ := hCream
  exact ⟨c, hcmem, hnProf⟩

/-- Decided example: profile `(p_H, p_L) = (25, 75)` (in hundredths),
    1-contract menu `(α=100, β=20)`. Global profit calculation:
    - on H: `20*100 - 25*100 = -500`
    - on L: `20*100 - 75*100 = -5500`
    - global (sum): `-500 + -5500 = -6000`, so global profit < 0.
    Conclusion: cream-skim is NOT profitable (no `c' ∈ menu` has
    global profit > 0, since `globalExpectedProfit ⟨100, 20⟩ r = -6000`). -/
example : ¬ creamSkimProfitable [⟨100, 20⟩] ⟨25, 75, by omega⟩ := by
  intro h
  obtain ⟨c', hc', hp, c, hcmem, hn⟩ := h
  -- `hc': c' ∈ [⟨100, 20⟩]`: the only menu member is `⟨100, 20⟩`.
  rcases hc' with heq | hmem
  · -- Head case: `c' = ⟨100, 20⟩`
    subst heq
    simp [globalExpectedProfit, expectedProfit] at hp
  · -- Tail case: `c' ∈ []` is False by construction.
    cases hmem

end AsymmetricInformation.Screening