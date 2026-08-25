/-
  Lemons — Akerlof 1970 model, bounded formalization
  ===================================================

  Lean 4 core (no Mathlib) formalization of Akerlof's founding model of
  the "lemons" market: under information asymmetry between seller
  (informed) and buyer (uninformed), a **fixed point** over the set of
  participants `S(P) = {q | c_q ≤ P}` may close the market for high
  quality.

  Three exclusively parametric regions:
  - `pooling_tenable`: a single price P accepts both types;
  - `lemons_only`: a price P ∈ [c_L, c_H) is compatible with L alone;
  - `no_trade`: no price P ∈ [c_L, c_H] simultaneously satisfies seller
    participation and buyer acceptance.

  Strict bounds (po-2025 canonical audit c.475 + DRINT lesson c.477):
  - NO auxiliary clause in κ — not derived from Akerlof 1970 *QJE* 84(3):488-500 ;
  - NO `∃!` without FINITE hypotheses listed in the signature ;
  - NO single-crossing/menu/signal — Akerlof is strictly price-only ;
  - Multiplicity accepted: if multiple prices satisfy the fixed point,
    they are all returned.

  English mirror of `Lemons.lean`. See i18n sibling-pair convention
  (EPIC #4980, user 2026-07-04). Byte-identical to FR except docstrings.
-/

namespace AsymmetricInformation.Lemons

/-- Two qualities: high (H) and low (L). Concrete inductive, not `Type H ⊕ L`. -/
inductive Quality where
  | low
  | high
  deriving DecidableEq, Repr

/-- Two-quality market: algebraic parameters as **integers** (consistent
    with upstream `BayesGame2` API which uses `Int` for payoffs).
    All theorems in this module operate on these bounded integers. -/
structure TwoQualityMarket where
  cLow : Int     -- L opportunity cost (c_L)
  cHigh : Int    -- H opportunity cost (c_H)
  vLow : Int     -- buyer value of L (v_L)
  vHigh : Int    -- buyer value of H (v_H)
  /-- Coherence constraints: values are strictly ordered and costs
      strictly increasing with quality. -/
  hValue : vLow < vHigh
  hCost : cLow < cHigh

/-- Prior probability π ∈ [0, 1] encoded as numerator over 100. Explicit
    hypothesis: `πNum ≤ 100` is carried by each theorem using it. -/
structure Prior where
  piNum : Nat     -- π = piNum / 100
  hPiNum : piNum ≤ 100

/-- Set of qualities offered at a price P: `{q | c_q ≤ P}`. -/
def offered (m : TwoQualityMarket) (P : Int) : List Quality :=
  let sLow := if m.cLow ≤ P then [Quality.low] else []
  let sHigh := if m.cHigh ≤ P then [Quality.high] else []
  sLow ++ sHigh

/-- Expected buyer value, conditioned on `offered m P`. Convention: if
    `offered` is empty, the expectation is `0` (no-trade). If only one
    type is offered, the expectation is its value. If both, it's the
    weighted mean by prior frequencies `π`. -/
def expectedValue (m : TwoQualityMarket) (π : Prior) (P : Int) : Int :=
  let qs := offered m P
  match qs with
  | []      => 0
  | [q]     => if q = Quality.low then m.vLow else m.vHigh
  | [_, _]  => (π.piNum * m.vHigh + (100 - π.piNum) * m.vLow) / 100
  | _       => 0  -- unreachable for 2 qualities

/-- Buyer condition at price P: `P ≤ E[v(q) | q ∈ S(P)]`.
    This is the **Bayesian anticipation**: the buyer requires the
    expected value of offered cars to cover the price. -/
def buyerAccepts (m : TwoQualityMarket) (π : Prior) (P : Int) : Prop :=
  P ≤ expectedValue m π P

/-- Pooling-tenable price: `c_H * 100 ≤ π * vHigh + (100 - π) * vLow`.
    Multiplied by 100 to stay integer (consistent with upstream API). -/
def poolingTenable (m : TwoQualityMarket) (π : Prior) : Prop :=
  m.cHigh * 100 ≤ π.piNum * m.vHigh + (100 - π.piNum) * m.vLow

/-- `Decidable` instance for `poolingTenable`: all underlying operations
    are on `Int`/`Nat`, and Lean provides `Int.decLe`. -/
instance poolingTenable.decidable (m : TwoQualityMarket) (π : Prior) :
    Decidable (poolingTenable m π) :=
  inferInstanceAs (Decidable (m.cHigh * 100 ≤ ↑π.piNum * m.vHigh + (100 - ↑π.piNum) * m.vLow))

/-- **Local lemons-only characterization**: there exists a price
    P ∈ [c_L, c_H) such that `buyerAccepts m π P` holds **and** only L
    is offered (`offered m P = [Quality.low]`). -/
def lemonsOnlyPossible (m : TwoQualityMarket) (π : Prior) : Prop :=
  ∃ P : Int, m.cLow ≤ P ∧ P < m.cHigh ∧ P ≤ expectedValue m π P ∧
    offered m P = [Quality.low]

/-- No-trade: no price P ∈ [c_L, c_H] simultaneously satisfies seller
    participation and buyer acceptance. -/
def noTrade (m : TwoQualityMarket) (π : Prior) : Prop :=
  ¬ ∃ P : Int, m.cLow ≤ P ∧ P < m.cHigh ∧ P ≤ expectedValue m π P

/-- **Decided examples** — the formalization **actually uses** integer
    arithmetic (no Mathlib):

    (a) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 50%` → lemons-only possible
        with `P = 0`: `offered = [Quality.low]`, `expectedValue m π 0 = 0`,
        so `buyerAccepts 0 ≤ 0 = True`. -/
example : lemonsOnlyPossible ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  refine ⟨0, by decide, by decide, ?_, by decide⟩
  -- `buyerAccepts`: `0 ≤ expectedValue ⟨0,5,0,4⟩ π 0 = vLow = 0`.
  simp [expectedValue, offered]

/-- (b) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 100%` → lemons-only with `P = 0`. -/
example : lemonsOnlyPossible ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨100, by decide⟩ := by
  refine ⟨0, by decide, by decide, ?_, by decide⟩
  simp [expectedValue, offered]

/-- (c) `(c_L, c_H, v_L, v_H) = (0, 2, 0, 4)`, `π = 50%`: pooling tenable. -/
example : poolingTenable ⟨0, 2, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  decide

/-- (d) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 50%`: pooling NOT tenable. -/
example : ¬ poolingTenable ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  decide

end AsymmetricInformation.Lemons