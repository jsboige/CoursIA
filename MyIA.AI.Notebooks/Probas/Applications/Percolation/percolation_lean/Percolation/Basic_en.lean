import Mathlib.Combinatorics.SetFamily.HarrisKleitman

/-! # Finite kernel of percolation — seed module

The goal of this lake (`percolation_lean`) is to formalize the **finite kernel**
of Bernoulli percolation on a finite graph, before the bridge toward the ICT
course (see `#14871`).

This milestone covers the **uniform case** `p = 1/2` (uniform measure on the
Boolean cube `2^α`): the passage to the general Bernoulli-`p` product measure
remains out of this milestone.

The core of this kernel is the **uniform Harris–Kleitman** inequality (finite
form of the FKG theorem): on the space of subsets of a finite alphabet `α` —
here the « edges » — two **increasing events** correlate positively. In
percolation, increasing monotone events (more open edges ⇒ the event still
holds, e.g. connectivity) satisfy exactly this correlation.

i18n convention EPIC #4980: docstrings in English here; the French mirror lives
in `Percolation/Basic.lean` (byte-identical apart from docstrings/comments).
-/

namespace Percolation_en

open Finset

/-- **Uniform Harris–Kleitman inequality (finite FKG, case `p = 1/2`)**, « two
increasing » form.

On the configuration space `Finset α` (a configuration = a subset of open edges,
`α` finite), two **increasing** events `𝒜` and `ℬ` correlate:

`#𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ)`

In other words, in the **uniform measure** on the Boolean lattice `2^α` (i.e.
independent percolation with edge-open probability `p = 1/2`), the probability
of `𝒜 ∩ ℬ` is at least the product of the probabilities — the **positive
association** (FKG), which is the finite version of the Harris–Kleitman theorem.

The passage to the general Bernoulli-`p` product measure remains out of this
milestone. The brick applies here to the uniform case: at `p = 1/2` on a finite
graph with `|α|` edges, it bounds the correlation of two increasing events
(e.g. « two vertices are connected » and « a subgraph is connected »).
-/
theorem harris_kleitman_upper_upper {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

/-- **Uniform Harris–Kleitman inequality (finite FKG, case `p = 1/2`)**, « two
decreasing » form.

The dual version: two **decreasing** events also correlate. This statement
dualizes the previous one (pass to the complement); like it, it is at the
uniform case `p = 1/2`, the general Bernoulli-`p` case remaining out of this
milestone. -/
theorem harris_kleitman_lower_lower {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

end Percolation_en
