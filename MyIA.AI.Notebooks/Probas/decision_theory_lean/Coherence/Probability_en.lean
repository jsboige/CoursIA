import Mathlib
import Coherence.Basic_en
import Coherence.DutchBook_en

/-!
# Coherence.Probability — coherence (single-book Dutch Book) ⟺ probability axioms

Issue #4050 — key milestone `coherent_iff_probability` (finite case). The `DutchBook.lean`
module proves the constructive direction "violation of inclusion–exclusion on two events
⟹ four-ticket Dutch Book". We establish here the **correspondence for the finite
single-book framework**: a price function `q` is exploitable by a (single-ticket) Dutch
Book if and only if it violates a probability bound — non-negativity `q A ≥ 0`,
upper bound `q A ≤ 1`, or normalisation `q ∅ = 0`, `q univ = 1`.

**Why this is elementary (not Hahn–Banach).** The "MEDIUM / hyperplane separation"
assessment of issue #4050 targeted a general formulation (books of arbitrary size on
any number of events, whose converse goes through the expectation argument
`E_q[gain] = 0`). For the **single-book characterisation**, each violated axiom
admits an EXPLICIT single-ticket Dutch Book, and the converse follows by disjunction
on the sign of the stake `s`:
- `q A < 0`: sell (`s = −1`), agent payoff `= q A − 𝟙_A ≤ q A < 0`.
- `q A > 1`: buy (`s = +1`), agent payoff `= 𝟙_A − q A < 0` (since `𝟙_A ≤ 1`).
- `q univ ≠ 1`: a ticket on the universe (`s = ±1`) gives a constant-sign payoff `< 0`.
- `q ∅ > 0`: a ticket on the empty set (`s = +1`) gives `−q ∅ < 0` (since `𝟙_∅ = 0`).

Conversely, under the probability bounds, no stake `s` makes `s (𝟙_A − q A) < 0`
at every state (disjunction `s < 0` / `s = 0` / `s > 0`).

**Honest scoping (G.3/G.9).** The COMPLETE `coherent_iff_probability` (books of
arbitrary size, via reconstruction of the measure `q A = Σ_{ω ∈ A} q {ω}` then the
expectation argument) remains a next milestone; we deliver here the single-book
characterisation and its identity with the probability bounds, 0 `sorry`. See
de Finetti (1937), *La prévision: ses lois logiques, ses sources subjectives*.

English mirror of `Coherence/Probability.lean` (French canonical). Convention EPIC #4980:
siblings `Foo.lean` (FR) + `Foo_en.lean` (EN), both compile in one lake.
Drift-CI: non-docstring content byte-identical between siblings.
Sibling namespace: `Coherence_en` (the canonical FR remains `Coherence`).
-/

namespace Coherence_en

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Payoff of a single ticket and single-book Dutch Book --/

/-- The net payoff at state `ω` of a single ticket on event `A` with stake `s` (positive
    stake = buy, negative = sell). As for `ieGain`, the ticket pays `𝟙_A ω` and costs
    `q A`: payoff `= s (𝟙_A ω − q A)`. -/
def ticketGain (q : Price Ω) (A : Event Ω) (s : ℝ) (ω : Ω) : ℝ := s * (ind A ω - q A)

/-- A **single-book Dutch Book** on `A`: a stake `s` whose payoff is strictly
    negative at every state — a sure loss for the agent. -/
def IsSingleDutchBook (q : Price Ω) (A : Event Ω) (s : ℝ) : Prop :=
  ∀ ω : Ω, ticketGain q A s ω < 0

/-- `q` is **coherent in the single-book sense** if no event admits a single-ticket
    Dutch Book. -/
def SingleCoherent (q : Price Ω) : Prop := ∀ A s, ¬ IsSingleDutchBook q A s

/-- `q` satisfies the **probability bounds** (finite case): non-negativity, upper
    bound by 1, and normalisation `q ∅ = 0`, `q univ = 1`. -/
def ProbBounds (q : Price Ω) : Prop :=
  (∀ A, (0:ℝ) ≤ q A) ∧ (∀ A, q A ≤ 1) ∧ q ∅ = 0 ∧ q (Finset.univ : Event Ω) = 1

/-! ## Lemmas: each violated axiom admits a single-book Dutch Book (explicit witness) --/

private lemma ind_nonneg (A : Event Ω) (ω : Ω) : (0:ℝ) ≤ ind A ω := by
  unfold ind; split <;> simp

private lemma ind_le_one (A : Event Ω) (ω : Ω) : ind A ω ≤ (1:ℝ) := by
  unfold ind; split <;> simp

/-- `q A < 0` ⟹ Dutch Book: sell a ticket `A` (`s = −1`), payoff `= q A − 𝟙_A < 0`. -/
theorem single_dutch_book_of_neg (q : Price Ω) (A : Event Ω) (h : q A < 0) :
    ∃ s, IsSingleDutchBook q A s := by
  refine ⟨-1, fun ω => ?_⟩
  show (-1:ℝ) * (ind A ω - q A) < 0
  have heq : (-1:ℝ) * (ind A ω - q A) = q A - ind A ω := by ring
  rw [heq]
  linarith [ind_nonneg A ω]

/-- `q A > 1` ⟹ Dutch Book: buy (`s = +1`), payoff `= 𝟙_A − q A < 0` (since `𝟙_A ≤ 1`). -/
theorem single_dutch_book_of_high (q : Price Ω) (A : Event Ω) (h : (1:ℝ) < q A) :
    ∃ s, IsSingleDutchBook q A s := by
  refine ⟨1, fun ω => ?_⟩
  show (1:ℝ) * (ind A ω - q A) < 0
  have heq : (1:ℝ) * (ind A ω - q A) = ind A ω - q A := by ring
  rw [heq]
  linarith [ind_le_one A ω]

/-- `q ∅ > 0` ⟹ Dutch Book on the empty event (`s = +1`), payoff `= −q ∅ < 0` (since
    `𝟙_∅ = 0` at every state). -/
theorem single_dutch_book_of_pos_empty (q : Price Ω) (h : (0:ℝ) < q (∅ : Event Ω)) :
    ∃ s, IsSingleDutchBook q (∅ : Event Ω) s := by
  refine ⟨1, fun ω => ?_⟩
  show (1:ℝ) * (ind (∅ : Event Ω) ω - q ∅) < 0
  have hind : ind (∅ : Event Ω) ω = 0 := by unfold ind; simp
  have heq : (1:ℝ) * (ind (∅ : Event Ω) ω - q ∅) = ind (∅ : Event Ω) ω - q ∅ := by ring
  rw [heq, hind]; linarith

/-- `q univ < 1` ⟹ Dutch Book on the universe (`s = −1`), payoff `= q univ − 1 < 0`
    (since `𝟙_univ = 1` at every state). -/
theorem single_dutch_book_of_univ_lt (q : Price Ω) (h : q (Finset.univ : Event Ω) < 1) :
    ∃ s, IsSingleDutchBook q (Finset.univ : Event Ω) s := by
  refine ⟨-1, fun ω => ?_⟩
  show (-1:ℝ) * (ind (Finset.univ : Event Ω) ω - q Finset.univ) < 0
  have hind : ind (Finset.univ : Event Ω) ω = 1 := by
    unfold ind; rw [if_pos (Finset.mem_univ ω)]
  have heq : (-1:ℝ) * (ind (Finset.univ : Event Ω) ω - q Finset.univ) =
      q Finset.univ - ind (Finset.univ : Event Ω) ω := by ring
  rw [heq, hind]; linarith

/-! ## Key theorem: single-book coherence ⟺ probability bounds (de Finetti, finite case) --/

/-- **de Finetti (finite case, single-book).** A price function `q` is coherent in the
    single-book sense (no single-ticket Dutch Book) **if and only if** it satisfies the
    probability bounds `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. The `[Nonempty Ω]`
    hypothesis is the natural physical assumption (at least one state of the world).

    **Proof** (0 `sorry`):
    - *⟹* (contrapositive): each violated bound admits an explicit Dutch Book
      (`single_dutch_book_of_neg/high/pos_empty/univ_lt`), contradicting `SingleCoherent`.
    - *⟸*: by trichotomy of the stake sign `s`. If `s < 0`, a payoff `< 0` everywhere
      forces `𝟙_A > q A` everywhere; for a `ω ∉ A` (`A ≠ univ`) this forces `0 > q A` (negates
      `q A ≥ 0`), and for `A = univ` this forces `1 > q univ` (negates `q univ = 1`). If `s = 0`,
      the payoff is zero (not `< 0`). If `s > 0`, a payoff `< 0` everywhere forces `𝟙_A < q A`
      everywhere; for a `ω ∈ A` (`A` non-empty) this forces `1 < q A` (negates `q A ≤ 1`), and
      for `A = ∅` this forces `0 < q ∅` (negates `q ∅ = 0`). -/
theorem single_coherent_iff_prob_bounds (q : Price Ω) [Nonempty Ω] :
    SingleCoherent q ↔ ProbBounds q := by
  refine ⟨fun hsc => ?_, fun hb => ?_⟩
  · -- SingleCoherent ⟹ ProbBounds
    refine ⟨fun A => by_contra fun hn => ?_, fun A => by_contra fun hn => ?_, ?_, ?_⟩
    · -- 0 ≤ q A : hn : ¬(0 ≤ q A) ⟹ q A < 0
      obtain ⟨s, hdb⟩ := single_dutch_book_of_neg q A (not_le.mp hn)
      exact absurd hdb (hsc A s)
    · -- q A ≤ 1 : hn : ¬(q A ≤ 1) ⟹ 1 < q A
      obtain ⟨s, hdb⟩ := single_dutch_book_of_high q A (not_le.mp hn)
      exact absurd hdb (hsc A s)
    · -- q ∅ = 0
      by_contra hn
      rcases lt_or_gt_of_ne hn with hn0 | h0
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_neg q (∅ : Event Ω) hn0
        exact absurd hdb (hsc _ s)
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_pos_empty q h0
        exact absurd hdb (hsc _ s)
    · -- q univ = 1
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_univ_lt q hlt
        exact absurd hdb (hsc _ s)
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_high q (Finset.univ : Event Ω) hgt
        exact absurd hdb (hsc _ s)
  · -- ProbBounds ⟹ SingleCoherent
    obtain ⟨hnn, hn1, h0, hu⟩ := hb
    intro A s hdb
    obtain ⟨w⟩ := ‹Nonempty Ω›
    rcases lt_trichotomy s 0 with hslt | hs0 | hsgt
    · -- s < 0 : 𝟙_A(ω) > q A for all ω
      have hind : ∀ ω, q A < ind A ω := fun ω => by
        have h := hdb ω
        unfold ticketGain at h
        nlinarith [hslt]
      by_cases hU : A = (Finset.univ : Event Ω)
      · -- A = univ : 𝟙_A(w) = 1, q A = 1 ⟹ 1 < 1, absurd
        have hiv : ind A w = 1 := by rw [hU]; unfold ind; simp
        have hqv : q A = 1 := by rw [hU]; exact hu
        linarith [hind w]
      · -- A ≠ univ : ∃ ω ∉ A, 𝟙_A = 0 ⟹ q A < 0, negates q A ≥ 0
        obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ A := by
          by_contra hnex
          simp only [not_exists, Classical.not_not] at hnex
          exact absurd ((Finset.eq_univ_iff_forall).mpr hnex) hU
        have hiv : ind A ω = 0 := by unfold ind; rw [if_neg hω]
        linarith [hind ω, hnn A]
    · -- s = 0 : ticketGain = 0, never < 0
      have h0gain : ticketGain q A 0 w = 0 := by simp [ticketGain]
      have h := hdb w
      rw [hs0] at h
      rw [h0gain] at h
      linarith
    · -- s > 0 : 𝟙_A(ω) < q A for all ω
      have hind : ∀ ω, ind A ω < q A := fun ω => by
        have h := hdb ω
        unfold ticketGain at h
        nlinarith [hsgt]
      by_cases hA : A.Nonempty
      · -- A non-empty : ∃ ω ∈ A, 𝟙_A = 1 ⟹ 1 < q A, negates q A ≤ 1
        obtain ⟨ω, hω⟩ := hA
        have hiv : ind A ω = 1 := by unfold ind; rw [if_pos hω]
        have h1lt : (1:ℝ) < q A := by rw [← hiv]; exact hind ω
        linarith [hn1 A]
      · -- A = ∅ : 𝟙_A(w) = 0, q A = q ∅ = 0 ⟹ 0 < 0, absurd
        rw [Finset.not_nonempty_iff_eq_empty] at hA
        have hiv : ind A w = 0 := by rw [hA]; unfold ind; simp
        have hqv : q A = 0 := by rw [hA]; exact h0
        linarith [hind w]

/-! ## Constructive converse: a true probability is coherent

The key result `single_coherent_iff_prob_bounds` characterises single-book coherent
price functions by the bounds `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. It remains to
verify that **true probability measures** — built from non-negative atomic weights
summing to 1 — satisfy these bounds, hence are coherent. This is the constructive
content of the "why" of probabilities: a *sincere* probabilistic belief (derived from
coherent weights) can never be arbitraged by a Dutch Book. This section completes the
tractable core of the `coherent_iff_probability` milestone (#4050) by delivering the
direction "true probability ⟹ coherence" — single-book AND additive.
-/

/-- A price function **derived from atomic weights**: `q A = Σ_{ω ∈ A} p ω`. When the
    weights `p` form a probability distribution (non-negative, summing to 1), `q` is
    exactly a finite probability measure. -/
noncomputable def priceFromWeights (p : Ω → ℝ) : Price Ω := fun A => ∑ ω ∈ A, p ω

/-- **Additivity of weights-derived prices.** A function `priceFromWeights p` satisfies
    the inclusion–exclusion identity `q(A∪B) + q(A∩B) = q A + q B`. By contrapositive of
    `coherent_on_implies_additive`, no violation of inclusion–exclusion is therefore
    exploitable by a four-ticket Dutch Book: atomic weights make `q` additive. -/
lemma priceFromWeights_additive (p : Ω → ℝ) (A B : Event Ω) :
    priceFromWeights p (A ∪ B) + priceFromWeights p (A ∩ B) =
      priceFromWeights p A + priceFromWeights p B := by
  simp only [priceFromWeights]
  exact Finset.sum_union_inter

/-- **Probabilistic weights satisfy the probability bounds.** If `p` is a
    distribution (non-negative, summing to 1), the price function `priceFromWeights p`
    satisfies `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. -/
lemma priceFromWeights_probBounds (p : Ω → ℝ) (hnn : ∀ ω, (0:ℝ) ≤ p ω)
    (hsum : ∑ ω, p ω = 1) : ProbBounds (priceFromWeights p) := by
  refine ⟨fun A => ?_, fun A => ?_, ?_, ?_⟩
  · -- 0 ≤ q A : sum of non-negative weights
    simp only [priceFromWeights]
    exact Finset.sum_nonneg (fun ω _ => hnn ω)
  · -- q A ≤ 1 : partial sum (over A ⊆ univ) ≤ total sum = 1
    simp only [priceFromWeights]
    have hsub : (A : Finset Ω) ⊆ Finset.univ := Finset.subset_univ _
    calc ∑ ω ∈ A, p ω
        ≤ ∑ ω ∈ (Finset.univ : Finset Ω), p ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hnn ω)
      _ = 1 := hsum
  · -- q ∅ = 0
    simp only [priceFromWeights, Finset.sum_empty]
  · -- q univ = 1
    simp only [priceFromWeights]
    exact hsum

/-- **A true probability is coherent (single-book).** A price function derived from
    atomic weights forming a probability distribution cannot be arbitraged by any
    single-ticket Dutch Book. This is the crowning result of the single-book framework:
    sincere probabilistic beliefs are non-arbitrageable (de Finetti, finite case). The
    proof composes `priceFromWeights_probBounds` with the characterisation
    `single_coherent_iff_prob_bounds`. -/
lemma priceFromWeights_single_coherent (p : Ω → ℝ) [Nonempty Ω]
    (hnn : ∀ ω, (0:ℝ) ≤ p ω) (hsum : ∑ ω, p ω = 1) :
    SingleCoherent (priceFromWeights p) :=
  (single_coherent_iff_prob_bounds _).mpr (priceFromWeights_probBounds p hnn hsum)

end Coherence_en
