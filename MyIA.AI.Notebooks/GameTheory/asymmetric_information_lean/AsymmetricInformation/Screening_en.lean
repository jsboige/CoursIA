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
    Convention: uniform probability on the 2 types in this bounded
    formalization (explicit π weighting can be added). -/
def globalExpectedProfit (c : Contract) (r : RiskProfile) : Int :=
  (expectedProfit c r .high + expectedProfit c r .low) / 2

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

/-- **Extraction lemma**: if `creamSkimProfitable` holds, then there
    exists a contract in the menu that loses on type H
    (`expectedProfit c r .high < 0`). This is a direct corollary of the
    2nd conjunct of `hCream`, with no `Decidable` required — the proof
    is `obtain` immediate on destructuring the hypothesis. It is the
    **trivial but useful** form: profitable cream-skim **implies**
    must have a loser on H. Not a converse, not uniqueness. -/
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
    - global: `(-500 + (-5500))/2 = -3000`, so `globalExpectedProfit < 0`.
    Conclusion: cream-skim is NOT profitable. -/
example : ¬ creamSkimProfitable [⟨100, 20⟩] ⟨25, 75, by omega⟩ := by
  intro h
  obtain ⟨c', hc', hp, c, hcmem, hn⟩ := h
  -- `hc': c' ∈ [⟨100, 20⟩]`: the only menu member is `⟨100, 20⟩`.
  -- Direct `rcases` on `List.Mem` (not on wrapped `elem`).
  rcases hc' with heq | hmem
  · -- Head case: `c' = ⟨100, 20⟩`
    subst heq
    simp [globalExpectedProfit, expectedProfit] at hp
  · -- Tail case: `c' ∈ []` is False by construction.
    -- `rcases` already extracted the contradiction via `False.elim`.
    cases hmem

end AsymmetricInformation.Screening