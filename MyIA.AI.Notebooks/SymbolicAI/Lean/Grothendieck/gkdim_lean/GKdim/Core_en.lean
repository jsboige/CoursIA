/-
Gelfand-Kirillov dimension — playable growth lemmas.

Companion to the GROTH-07 notebook. This file does not formalize Smoktunowicz's
gap theorem (that would be a project in its own right — cf. the article in the
bibliography): it establishes the elementary, playable case on which the
notebook's intuition rests. The polynomial ring in one variable, endowed with
its standard `ℕ` grading, grows exactly like `n`; its Gelfand-Kirillov
dimension is therefore `1`.
-/
import Mathlib

open Nat

namespace GKdim_en

variable {K : Type*} [Field K]

/-- Hilbert function of `K[X]` (standard grading by `ℕ`): dimension of the
vector space of polynomials of total degree at most `n`. In one variable, the
monomials of degree at most `n` are `1, X, …, X^n`: there are `n + 1` of
them.

This is no longer a sequence picked by hand: `hilbert_poly1_space_equiv`
identifies the space `K[X]_{< n + 1}` with `Fin (n+1) → K`, and
`hilbert_poly1_eq_finrank` proves that `hilbert_poly1 n` is the finrank of that
space. The definition stays **computable** — Mathlib's finrank is not — which
lets the notebook evaluate the sequence on the first degrees. -/
def hilbert_poly1 (n : ℕ) : ℕ := n + 1

/-- The space `K[X]_{< n + 1}` of polynomials of degree strictly less than
`n + 1` — that is, of degree at most `n` — is `K`-isomorphic to `Fin (n+1) → K`:
this is Mathlib's `Polynomial.degreeLTEquiv`, which reads the coefficients. -/
noncomputable def hilbert_poly1_space_equiv (n : ℕ) :
    Polynomial.degreeLT K (n + 1) ≃ₗ[K] Fin (n + 1) → K :=
  Polynomial.degreeLTEquiv K (n + 1)

/-- The Hilbert function is the finrank of the space `K[X]_{< n + 1}`: through
the isomorphism above and `Module.finrank_fin_fun`, that rank is `n + 1`, that
is `hilbert_poly1 n`. This is the formal link that was missing between the
sequence and the vector space it claims to measure. -/
theorem hilbert_poly1_eq_finrank (n : ℕ) :
    Module.finrank K (Polynomial.degreeLT K (n + 1)) = hilbert_poly1 n := by
  rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K (n + 1))]
  rw [Module.finrank_fin_fun K]
  rfl

/-- A sequence `G : ℕ → ℕ` has polynomial growth of degree **at most** `d` if
there exist a constant `C` and a threshold `n₀` such that `G n ≤ C * n ^ d`
for every `n ≥ n₀`. -/
def growthAtMost (G : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ C n₀, ∀ n ≥ n₀, G n ≤ C * n ^ d

/-- ... and of degree **at least** `d` if there exist `c > 0` and a threshold
`n₀` such that `G n ≥ c * n ^ d` for every `n ≥ n₀`. -/
def growthAtLeast (G : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ c n₀, 0 < c ∧ ∀ n ≥ n₀, G n ≥ c * n ^ d

/-- The growth of `K[X]` is bounded above by a multiple of `n`. -/
theorem poly1_growthAtMost : growthAtMost hilbert_poly1 1 := by
  use 2, 1
  intro n hn
  simp only [hilbert_poly1, pow_one]
  omega

/-- ... and bounded below by `n` (the dominant term). -/
theorem poly1_growthAtLeast : growthAtLeast hilbert_poly1 1 := by
  use 1, 1
  constructor
  · omega
  · intro n hn
    simp only [hilbert_poly1, pow_one, one_mul]
    omega

/-- The playable statement: the Gelfand-Kirillov dimension of `K[X]` is `1`,
characterized by the two growth bounds above (exactly linear growth). -/
theorem poly1_gkdim_is_one :
    growthAtMost hilbert_poly1 1 ∧ growthAtLeast hilbert_poly1 1 :=
  ⟨poly1_growthAtMost, poly1_growthAtLeast⟩

end GKdim_en
