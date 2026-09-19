/-
Grokking — effective theory of representation learning (slice 1: R02).

This module formalizes the short statements of Part 3 of the paper
"Towards Understanding Grokking — An Effective Theory of Representation Learning"
(Liu, Michaud, Tegmark; arXiv:2205.10343), issue #16752, arc "open, accountable,
provable, explicable" of the Tegmark corpus (#16741).

Setting: toy modular addition on `Fin p`. The model `M = (Dec, R)` maps each integer
`k` to an embedding `E k` in an abelian group `V` (the representation space); the
decoder `Dec : V → W` reads a paired embedding `E i + E j` and must produce the label
`Y (i + j)` of the sum. Training is at zero loss whenever
`Dec (E i + E j) = Y (i + j)` for all pairs.

Contents:
* `Grokking_en.IsParallelogram` — Definition 1 of the paper (exact case δ = 0):
  `(i, j, m, n)` forms a parallelogram in the representation if `E i + E j = E m + E n`.
* `Grokking_en.prop1_zeroLoss` — Proposition 1: at zero training loss, any
  parallelogram of the representation comes from an equality of indices
  `i + j = m + n` (labels being pairwise distinct). Contrapositive: a representation
  that "cheats" by forming a parallelogram between different sums is impossible at
  zero loss — that would be memory, not structure.
* `Grokking_en.prop2_injectiveDecoder` — Proposition 2: conversely, if the decoder of
  an ideal model (zero loss + injective decoder) is injective, then any two training
  pairs `(i, j)`, `(m, n)` with `i + j = m + n` FORCES a parallelogram in the
  representation. This is the formation mechanism of parallelograms: decoder
  injectivity forbids two equal sums from having different embeddings.

The two propositions are dual: 1 trades decoder injectivity for label injectivity,
2 restores it. No topological structure is needed — an abelian group `V` suffices
(the paper works in `ℝ^d`, but the statements are purely algebraic).

The dynamical part (conservation laws of Appendix F) lives in
`Grokking.Conservation_en`.

English mirror of `Grokking/Effective.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`Grokking_en` (anti-collision with the FR `Grokking` namespace); cross-module
`_en` imports `_en`; non-docstring proof code unchanged.
-/
import Mathlib

namespace Grokking_en

section Definitions

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- Definition 1 (R02, case δ = 0): `(i, j, m, n)` forms a **parallelogram** in the
representation `E` if the embedding sums coincide exactly. In the paper the
definition tolerates a threshold `δ` for numerical errors; we take `δ = 0`,
the limiting case where all statements are exact. -/
def IsParallelogram (E : Fin p → V) (i j m n : Fin p) : Prop :=
  E i + E j = E m + E n

/-- Zero training loss: the decoder returns the label of the sum for every pair of
indices. (The paper restricts this to the training set `D`; we take all pairs,
which only strengthens the hypotheses.) -/
def ZeroTrainingLoss (E : Fin p → V) (Dec : V → W) (Y : Fin p → W) : Prop :=
  ∀ i j, Dec (E i + E j) = Y (i + j)

end Definitions

section Proposition1

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- **Proposition 1 (R02).** At zero training loss with pairwise distinct labels,
every parallelogram of the representation is "permissible": `i + j = m + n`.

Proof (by contradiction, as in the paper): the parallelogram gives
`Dec (E i + E j) = Dec (E m + E n)`, zero loss identifies both sides with
`Y (i + j)` and `Y (m + n)`, and label injectivity concludes. The formalized
version is direct rather than by contradiction — same content, fewer steps. -/
theorem prop1_zeroLoss {E : Fin p → V} {Dec : V → W} {Y : Fin p → W}
    (hloss : ZeroTrainingLoss E Dec Y) (hY : Function.Injective Y) {i j m n : Fin p}
    (hpara : IsParallelogram E i j m n) : i + j = m + n := by
  have h1 : Y (i + j) = Y (m + n) := by
    rw [(hloss i j).symm, (hloss m n).symm, hpara]
  exact hY h1

end Proposition1

section Proposition2

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- **Proposition 2 (R02).** In an ideal model (zero loss + injective decoder), any
index equality `i + j = m + n` forces a parallelogram of the representation.

This is the **formation** mechanism of parallelograms: zero loss gives
`Dec (E i + E j) = Y (i + j) = Y (m + n) = Dec (E m + E n)`, and decoder
injectivity turns the equality of outputs into an equality of inputs. Combined with
Proposition 1, a representation learned by an ideal model has exactly the
permissible parallelograms — the linear structure observed after grokking. -/
theorem prop2_injectiveDecoder {E : Fin p → V} {Dec : V → W} {Y : Fin p → W}
    (hloss : ZeroTrainingLoss E Dec Y) (hDec : Function.Injective Dec) {i j m n : Fin p}
    (hsum : i + j = m + n) : IsParallelogram E i j m n := by
  have h1 : Dec (E i + E j) = Dec (E m + E n) := by
    rw [hloss, hloss, hsum]
  exact hDec h1

end Proposition2

section Permissible

variable {p : ℕ} [NeZero p]

/-- The set of **permissible** parallelograms `P₀` (Eq. 1 of the paper): index
quadruples consistent with addition. This will support the effective loss `ℓ₀`
of the module `Grokking.Conservation_en`. -/
def permissible : Finset (Fin p × Fin p × Fin p × Fin p) :=
  Finset.univ.filter fun q => q.1 + q.2.1 = q.2.2.1 + q.2.2.2

end Permissible

end Grokking_en
