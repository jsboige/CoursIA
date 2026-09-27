import Discrepancy.Basic_en

/-!
# i18n convention: EN sibling file

i18n convention ratified for this repository (EPIC #4980): for each canonical
FR file `Foo.lean`, an EN sibling `Foo_en.lean` mirrors it with translated
docstrings and comments ONLY — signatures, definitions, proofs and tactics
are byte-identical; the namespace carries the `_en` suffix to avoid name
clashes. The FR file remains the canonical teaching source.
-/

/-!
# Komlós and Bansal–Jiang: unit columns and the large-degree regime

Second installment of the `discrepancy_lean` lake (issue #12823): the
SOTA-frontier statements, in the exact form of the **Komlós** conjecture
(matrices with unit columns, bounded `O(1)` conjectured) and the forms of
the **Bansal–Jiang 2025** paper (arXiv:2508.03961, "Decoupling via Affine
Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk"):

- large-degree regime: the Beck–Fiala conjecture holds from `k ≥ (log n)²`;
- Komlós in `Õ(log^(1/4) n)`, beyond Banaszczyk's `O(√(log n))`.

Documented honesty: these theorems require a layer absent from Mathlib (SDP
+ duality, affine spectral independence, guided discrete Brownian motion,
matrix concentration). The statements therefore live as named `Prop`s
**from now on**; the proofs will wait for the upstream layer (P3 =
documented aspiration, never a promise). For the paper's Komlós form, we
state a **concrete weakened version** (`C * (log n)²`), true as soon as the
paper's theorem is — the exact polylog exponents of the `Õ` are not
pretended.

The sums are written by hand (`∑ i, A i j * c j`) rather than with
`Matrix.mulVec`: the column-line stays readable as a sum of products, as
close as possible to the paper definitions.
-/

namespace Discrepancy_en

/-- **Komlós conjecture**: there exists a universal constant `C` such that
every matrix `A` with `n` **unit** columns (`∑ i, A i j ^ 2 = 1`) admits a
`±1` coloring of the columns whose every line sum remains bounded by `C` in
absolute value.

Banaszczyk's theorem (1998) gives `O(√(log n))`; the conjecture requires
`O(1)`. Open. -/
def KomlosConjecture : Prop :=
  ∃ C : ℚ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
      ∃ c : Fin n → ℚ,
        (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧ ∀ i : Fin m, |∑ j, A i j * c j| ≤ C

/-- **Bansal–Jiang 2025, large-degree regime** (arXiv:2508.03961, theorem
1): the Beck–Fiala conjecture holds as soon as the degree dominates the
squared logarithm, `k ≥ (log₂ n)²` — with the same `O(√k)` conclusion at
universal constant. Resolves the Beck–Fiala conjecture for `k ≥ log² n`. -/
def BansalJiangLargeDegree : Prop :=
  ∃ C : ℕ,
    ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k)
      (_hlog : (Nat.log 2 n) ^ 2 ≤ k),
      ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Komlós, concrete weakened form after Bansal–Jiang 2025**: for matrices
with unit columns, a `±1` coloring bounds every line sum by `C * (log₂ n)²`.

The paper proves `Õ(log^(1/4) n)` — stronger. A conservative polylog
exponent (here `2`) gives a statement **implied** by the paper's theorem,
hence true as soon as the paper is, while remaining beyond the Banaszczyk
target in small powers. This is the SOTA frontier as the repository can
honestly state it without the SDP layer. -/
def KomlosBansalJiangWeak : Prop :=
  ∃ C : ℚ,
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℚ,
          (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
            ∀ i : Fin m, |∑ j, A i j * c j| ≤ C * ((Nat.log 2 n : ℚ) ^ 2)

end Discrepancy_en
