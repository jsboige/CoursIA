import Coherence.Basic
import Coherence.DutchBook
import Coherence.Probability

/-!
# Decision Theory — Dutch Book / coherence (de Finetti)

Formalization of de Finetti's coherence theorem (finite case): the conceptual
foundation of probabilities. **Incoherent** betting prices (violating
inclusion–exclusion) expose the agent to a **Dutch Book** — a book of bets at
sure loss. Coherence therefore *forces* the probability axioms.

## Contents
- `Coherence.Basic`: events (`Event`), price functions (`Price`), indicators, and
  the inclusion–exclusion identity (`ind_inclusion_exclusion`) — the keystone.
- `Coherence.DutchBook`: the constructive direction "incoherence ⟹ Dutch Book"
  (`non_additive_implies_dutch_book`, explicit witness, 0 `sorry`) and its
  contrapositive "coherence ⟹ additivity" (`coherent_on_implies_additive`).
- `Coherence.Probability`: the **single-book characterization** of de Finetti
  (`single_coherent_iff_prob_bounds`) — a price function `q` is coherent in the
  single-ticket sense (no single-ticket Dutch Book) **iff** it satisfies the
  probability bounds `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. Each violated axiom
  admits an explicit single-ticket Dutch Book (`single_dutch_book_of_neg/high/pos_empty/univ_lt`),
  0 `sorry`.

## Status
- Proved without `sorry`: the constructive direction (inclusion–exclusion
  violation ⟹ Dutch Book with explicit stakes `(1,1,−1,−1)` or the converse),
  coherence ⟹ additivity on two events, and the **complete single-book
  characterization** (`single_coherent_iff_prob_bounds`, 0 `sorry`, axioms
  `[propext, Classical.choice, Quot.sound]`).
- Open (next milestone): the full `coherent_iff_probability` (arbitrary-size
  books, via the measure reconstruction `q A = Σ_{ω ∈ A} q {ω}` then the
  expectation argument, or hyperplane separation / LP duality in finite
  dimension). The single-book version delivered here is its tractable core (Lean
  feasibility "MEDIUM", cf #4050).

## Cross-references
- `Utility` (same lake): von Neumann–Morgenstern expected-utility representation —
  the other foundation of decision theory under risk.
- Infer-14 (Infer.NET): Bayesian expected utility under the posterior.
- PyMC-1 (PyMC): expected-utility estimation by posterior sampling.
-/

/-!
English mirror of `Coherence.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling files in the
same lake; this is a pure landing doc module (imports + module docstring, no
declarations) so no namespace suffix is needed (mirrors the FR root structure
exactly). Submodule EN siblings live under `Coherence/*_en.lean`.
-/
