import Mathlib
import Coherence.Basic_en
import Coherence.DutchBook_en
import Coherence.Probability_en

/-!
# Coherence.Premium — the actuarial reading of the Dutch Book: coherence of a tariff

T6 of EPIC #12904 (Decision Theory actuarial leg). The de Finetti theorem proven in
`DutchBook.lean` receives its **actuarial** reading here: the "ticket paying 1 if A
occurs" becomes a **coverage contract** (unit indemnity on event A), the "price
function" becomes a **premium schedule**, and the Dutch Book becomes a **tariff
arbitrage** — a broker (or an informed client, or a competitor) assembling a
portfolio of contracts at **sure profit**, i.e. a **strict and sure loss for the
insurer** in every state of the world.

Three results, 0 `sorry`, each a business reading of the `DutchBook.lean` /
`Probability.lean` bedrock:

1. **`incoherent_premium_sure_insurer_loss`** — a schedule violating
   inclusion–exclusion on two coverages exposes the insurer to a sure loss: the
   witness of `non_additive_implies_dutch_book`, read from the other side of the
   counter (stakes flip sign), is the broker's arbitrage portfolio.
2. **`coherent_premium_disjoint_additive`** — the everyday pricing rule: for two
   **disjoint** risks (two customer segments, two non-overlapping coverages), a
   schedule coherent both in the four-ticket sense and in the single-ticket sense
   satisfies `π(A ∪ B) = π(A) + π(B)` — the premium of the combined risk is the sum
   of the segment premiums. The proof combines `coherent_on_implies_additive`
   (inclusion–exclusion) with the normalisation `π ∅ = 0` forced by the
   single-ticket coherence (`single_coherent_iff_prob_bounds`).
3. **`pure_premium_tariff_unarbitrageable`** — a schedule computed by expectation
   (pure premium `π(A) = Σ_{ω ∈ A} p(ω)`, non-negative weights summing to 1) offers
   **no** sure-profit portfolio: immediate consequence of
   `priceFromWeights_coherent_on` and the symmetry
   `coherent_on_iff_no_sure_profit`.

**Honest scoping (G.3/G.9).** Point 2 is an equivalence of two coherences (four
tickets on `(A, B)` + global single-ticket), not the full
`coherent_iff_probability` — whose general converse remains the open milestone of
`DutchBook.lean` (hyperplane separation / LP duality). Results are stated on the
unit schedule (indemnity 1); scaling to arbitrary amounts (contracts `(α, β)`
coverage × capital) follows by linearity of stakes and is not re-developed here.
See the PyMC sub-series `DecisionTheory/` (EPIC #12904, tranches T1-T5) for the
numerical side (pure premium, loading, partial pooling).

English mirror of `Coherence/Premium.lean` (French canonical). Convention EPIC #4980:
siblings `Foo.lean` (FR) + `Foo_en.lean` (EN), both compile in one lake.
Drift-CI: non-docstring content byte-identical between siblings.
Sibling namespace: `Coherence_en` (the canonical FR remains `Coherence`).
-/

namespace Coherence_en

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Premium schedule, insurer's result, tariff arbitrage --/

/-- A **premium schedule**: each event `A` (coverage) is covered up to 1 of
    indemnity for a unit premium `π A`. This is exactly the de Finetti framework
    (`Price`) read on the insurer's side: the ticket becomes a contract, the price
    becomes a premium. -/
abbrev PremiumSchedule (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Event Ω → ℝ

/-- **Insurer's net result** at state `ω` on a client portfolio of four contracts
    `(A, B, A∩B, A∪B)` with subscriptions `(sA, sB, sAB, sAU)` (positive
    subscription = the client buys the coverage, negative = they place it on the
    insurer's side): premiums collected minus indemnities paid. This is the exact
    opposite of the client book's gain (`ieGain`) — the two sides of the counter see
    opposite results. -/
def InsurerNet (π : PremiumSchedule Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) : ℝ :=
  -ieGain π A B sA sB sAB sAU ω

/-- A **tariff arbitrage**: a client portfolio whose result is strictly positive in
    every state — hence a strictly negative result (sure loss) for the insurer in
    every state. This is the Dutch Book of `DutchBook.lean` read from the company's
    viewpoint: "an incoherent schedule of premiums is a sure-losing bet" — for the
    one who posted it. -/
def TariffArbitrage (π : PremiumSchedule Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) : Prop :=
  ∀ ω : Ω, InsurerNet π A B sA sB sAB sAU ω < 0

/-- A schedule offers **no sure profit** (in the four-ticket sense on `(A, B)`): no
    client portfolio is a tariff arbitrage. This is the exact mirror of `CoherentOn`
    (no sure loss on the client side). -/
def NoSureProfit (π : PremiumSchedule Ω) (A B : Event Ω) : Prop :=
  ∀ sA sB sAB sAU : ℝ, ¬ TariffArbitrage π A B sA sB sAB sAU

/-! ## Counter symmetry: no sure client loss ⟺ no sure profit --/

/-- Opposite-sign stakes give the opposite-sign gain: the book `(-sA, -sB, -sAB,
    -sAU)` is the exact counterparty of the book `(sA, sB, sAB, sAU)`. This is the
    linearity of stakes in `ieGain` — the key to switching client/insurer
    viewpoint. -/
lemma ieGain_neg (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) :
    ieGain q A B (-sA) (-sB) (-sAB) (-sAU) ω = -ieGain q A B sA sB sAB sAU ω := by
  simp only [ieGain]
  ring

/-- **Switching sides of the counter.** A schedule is coherent (no Dutch Book on the
    client side, `CoherentOn`) if and only if it offers no sure profit (no arbitrage
    on the client side, `NoSureProfit`): the two readings are the same property,
    related by inverting the signs of the stakes (`ieGain_neg`). For the insurer, the
    coherence of its schedule and the absence of arbitrage against it are therefore
    one and the same requirement. -/
theorem coherent_on_iff_no_sure_profit (π : PremiumSchedule Ω) (A B : Event Ω) :
    CoherentOn π A B ↔ NoSureProfit π A B := by
  constructor
  · intro hc sA sB sAB sAU harb
    refine hc (-sA) (-sB) (-sAB) (-sAU) ?_
    intro ω
    have h := harb ω
    simp only [InsurerNet] at h
    rw [ieGain_neg]
    linarith
  · intro hnp sA sB sAB sAU harb
    refine hnp (-sA) (-sB) (-sAB) (-sAU) ?_
    intro ω
    have h := harb ω
    simp only [InsurerNet]
    rw [ieGain_neg]
    linarith

/-! ## Target theorems (actuarial reading) -/

/-- **Incoherent schedule ⟹ sure insurer loss.** If the schedule `π` violates
    inclusion–exclusion on two coverages `A, B`, a broker builds a portfolio of
    contracts with strict profit in every state — the insurer suffers a strict and
    sure loss. This is `non_additive_implies_dutch_book` read from the other side of
    the counter: the Dutch Book witness (stakes at sure loss on the client side)
    becomes, by sign inversion, the broker's arbitrage portfolio. -/
theorem incoherent_premium_sure_insurer_loss (π : PremiumSchedule Ω) (A B : Event Ω)
    (h : π (A ∪ B) + π (A ∩ B) ≠ π A + π B) :
    ∃ sA sB sAB sAU : ℝ, TariffArbitrage π A B sA sB sAB sAU := by
  obtain ⟨sA, sB, sAB, sAU, hloss⟩ := non_additive_implies_dutch_book π A B h
  refine ⟨-sA, -sB, -sAB, -sAU, ?_⟩
  intro ω
  have h' := hloss ω
  simp only [InsurerNet]
  rw [ieGain_neg]
  linarith

/-- **Additivity on disjoint risks — the segmentation rule.** For two **disjoint**
    coverages (`A ∩ B = ∅`: two non-overlapping customer segments, two exclusive
    risks), a schedule coherent both in the four-ticket sense (on `(A, B)`) and in
    the single-ticket sense satisfies

    `π (A ∪ B) = π A + π B`:

    the premium of the combined risk is exactly the sum of the segment premiums.
    The proof combines the inclusion–exclusion forced by coherence
    (`coherent_on_implies_additive`: `π(A∪B) + π(∅) = π A + π B` here) with the
    normalisation `π ∅ = 0` forced by single-ticket coherence (`probBounds_empty`
    via `single_coherent_iff_prob_bounds`). A pool premium above (or below) the sum
    of segment premiums is thus either an exploitable incoherence, or the sign that
    an untariffed loading has slipped into the schedule. -/
theorem coherent_premium_disjoint_additive [Nonempty Ω] (π : PremiumSchedule Ω)
    (A B : Event Ω) (hdj : A ∩ B = ∅)
    (hc4 : CoherentOn π A B) (hc1 : SingleCoherent π) :
    π (A ∪ B) = π A + π B := by
  have hIE := coherent_on_implies_additive π A B hc4
  have hb : ProbBounds π := (single_coherent_iff_prob_bounds π).mp hc1
  have h0 : π (∅ : Event Ω) = 0 := probBounds_empty π hb
  rw [hdj] at hIE
  rw [h0] at hIE
  linarith

/-- **The pure premium is unarbitrageable.** A schedule built by expectation under
    non-negative weights `p` summing to 1 — the actuarial **pure premium**
    `π(A) = Σ_{ω ∈ A} p(ω)` — offers no sure-profit portfolio: no broker can
    arbitrage an expectation-consistent tariff. Immediate consequence of
    `priceFromWeights_coherent_on` (no Dutch Book on the client side) and of the
    symmetry `coherent_on_iff_no_sure_profit` (hence also no sure profit on the
    broker side). The pure premium is thereby the only schedule both break-even in
    expectation and unarbitrageable — the mandatory starting point of the security
    loading (tranches T1/T2 of EPIC #12904). -/
theorem pure_premium_tariff_unarbitrageable (p : Ω → ℝ) (hnn : ∀ ω, (0:ℝ) ≤ p ω)
    (hsum : ∑ ω, p ω = 1) (A B : Event Ω) :
    NoSureProfit (priceFromWeights p) A B :=
  (coherent_on_iff_no_sure_profit (priceFromWeights p) A B).mp
    (priceFromWeights_coherent_on p hnn hsum A B)

end Coherence_en
