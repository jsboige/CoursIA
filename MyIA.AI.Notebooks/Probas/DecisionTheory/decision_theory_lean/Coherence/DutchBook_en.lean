import Mathlib
import Coherence.Basic_en

/-!
# Coherence.DutchBook — incoherence ⟹ Dutch Book (de Finetti, constructive direction)

Issue #4050. De Finetti's coherence theorem (finite case) establishes the
correspondence between **coherence** (absence of a sure-loss bet) and **additivity**
(the price function satisfies inclusion–exclusion, hence is a probability
measure). We prove here the **constructive direction**, mechanically central:
if prices violate inclusion–exclusion on two events, an explicit *Dutch Book*
exists (concrete stakes on the four tickets `A, B, A∩B, A∪B` yielding a sure
loss). The contrapositive gives "coherence ⟹ additivity".

The mathematical key is the inclusion–exclusion identity of indicators
(`ind_inclusion_exclusion` in `Basic.lean`): `𝟙_A + 𝟙_B − 𝟙_{A∩B} − 𝟙_{A∪B} = 0`
at every state, so the payoff of the four tickets with stakes `(1, 1, −1, −1)` is
exactly `δ := q(A∪B) + q(A∩B) − q(A) − q(B)`, **independent of the state**. If
`δ ≠ 0`, choose the sign of the stakes to guarantee a sure loss = a Dutch Book.

**Honest scoping (G.3/G.9).** We prove the direction "incoherence ⟹ Dutch Book"
(constructive, explicit witness, 0 `sorry`) and its contrapositive "coherence ⟹
additivity on two events". The converse "additivity ⟹ coherence" (and the full
`coherent_iff_probability`: general additivity + normalisation `q ∅ = 0`,
`q univ = 1`) requires **hyperplane separation / LP duality** in finite dimension
(Lean feasibility assessed "MEDIUM" in #4050) and is left **open** as a next
milestone — not `sorry`-backed. This structure (one direction proven + the
converse open, documented) is consistent with the `Utility` module of the same lake
(sound direction proven, Herstein–Milnor existence open). See de Finetti (1937).

English mirror of `Coherence/DutchBook.lean` (French canonical). Convention EPIC #4980:
siblings `Foo.lean` (FR) + `Foo_en.lean` (EN), both compile in one lake.
Drift-CI: non-docstring content byte-identical between siblings.
Sibling namespace: `Coherence_en` (the canonical FR remains `Coherence`).
-/

namespace Coherence_en

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Payoff of a four-ticket book and Dutch Book --/

/-- The net payoff at state `ω` of a book of four tickets on `(A, B, A∩B, A∪B)` with
    stakes `(sA, sB, sAB, sAU)` (positive stake = buy, negative = sell). Each ticket
    pays the indicator of its event and costs `q(event)`: the net payoff of a
    ticket is `stake × (indicator − price)`. -/
def ieGain (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) : ℝ :=
  sA * (ind A ω - q A) + sB * (ind B ω - q B)
    + sAB * (ind (A ∩ B) ω - q (A ∩ B)) + sAU * (ind (A ∪ B) ω - q (A ∪ B))

/-- An **inclusion–exclusion Dutch Book**: stakes on `(A, B, A∩B, A∪B)` whose
    net payoff is **strictly negative at every state** — a sure loss for the agent
    (and a sure profit for the arbitrageur). -/
def IsIEArbitrage (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) : Prop :=
  ∀ ω : Ω, ieGain q A B sA sB sAB sAU ω < 0

/-! ## Target theorems (constructive direction) --/

/-- **de Finetti (finite case, ⟸, constructive).** If the price `q` violates
    inclusion–exclusion on events `A, B` (`q(A∪B) + q(A∩B) ≠ q A + q B`), then a
    Dutch Book exists: explicit stakes on `(A, B, A∩B, A∪B)` yielding a sure loss.

    **Proof** (0 `sorry`): set `δ := q(A∪B) + q(A∩B) − q A − q B ≠ 0`. By the
    inclusion–exclusion identity (`ind_inclusion_exclusion`), the payoff of the book
    with stakes `(1, 1, −1, −1)` equals exactly `δ` at every state (the indicator
    combination vanishes). If `δ < 0`, those stakes are the Dutch Book. If `δ > 0`,
    flip the signs `(−1, −1, 1, 1)` and the payoff becomes `−δ < 0`. In both cases,
    `linarith` concludes from the indicator identity. -/
theorem non_additive_implies_dutch_book (q : Price Ω) (A B : Event Ω)
    (h : q (A ∪ B) + q (A ∩ B) ≠ q A + q B) :
    ∃ sA sB sAB sAU : ℝ, IsIEArbitrage q A B sA sB sAB sAU := by
  set δ := q (A ∪ B) + q (A ∩ B) - q A - q B
  have hδ : δ ≠ 0 := fun heq => h (by linarith)
  by_cases hδn : δ < 0
  · -- δ < 0: stakes (1, 1, −1, −1) → payoff = δ < 0 at every state.
    refine ⟨1, 1, -1, -1, ?_⟩
    intro ω
    simp only [ieGain]
    have hie := ind_inclusion_exclusion A B ω
    linarith
  · -- δ ≥ 0; with δ ≠ 0 ⟹ δ > 0: stakes (−1, −1, 1, 1) → payoff = −δ < 0.
    have hδge : 0 ≤ δ := not_lt.mp hδn
    have hδp : 0 < δ := lt_of_le_of_ne hδge (Ne.symm hδ)
    refine ⟨-1, -1, 1, 1, ?_⟩
    intro ω
    simp only [ieGain]
    have hie := ind_inclusion_exclusion A B ω
    linarith

/-- Prices are **coherent** on `(A, B)` if no Dutch Book exists on the four
    events `(A, B, A∩B, A∪B)`. -/
def CoherentOn (q : Price Ω) (A B : Event Ω) : Prop :=
  ∀ sA sB sAB sAU : ℝ, ¬ IsIEArbitrage q A B sA sB sAB sAU

/-- **Coherence ⟹ inclusion–exclusion (de Finetti, contrapositive).** If no Dutch
    Book exists on `(A, B, A∩B, A∪B)`, then `q` is additive on `A, B`: the price
    function satisfies inclusion–exclusion `q(A∪B) + q(A∩B) = q A + q B`. This is
    the immediate contrapositive of `non_additive_implies_dutch_book`. -/
theorem coherent_on_implies_additive (q : Price Ω) (A B : Event Ω)
    (hc : CoherentOn q A B) :
    q (A ∪ B) + q (A ∩ B) = q A + q B := by
  by_contra h
  obtain ⟨sA, sB, sAB, sAU, harb⟩ := non_additive_implies_dutch_book q A B h
  exact hc sA sB sAB sAU harb

end Coherence_en
