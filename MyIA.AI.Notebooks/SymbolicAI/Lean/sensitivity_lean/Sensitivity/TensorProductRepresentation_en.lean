/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

New module (G7 grain of #14366, McCoy et al. arXiv:2608.29530): bounded TPR
algebra — binding/unbinding, constituent surgery identity, affine projection
hypothesis and approximation hypothesis.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Tensor product representations (TPR) — bounded algebra

This file formalizes the TPR model of Smolensky as used by McCoy,
Soulos, Linzen and Smolensky (arXiv:2608.29530):

* a **binding** ties a filler to a role by tensor product (`tprBind`);
* a **superposition** sums the bindings (`tprSuperpos`);
* **unbinding** reads a filler back by multiplication with the role
  vector (`tprUnbind`) — exact under independence (orthonormality) of
  the roles;
* **constituent surgery** replaces the binding of one constituent and
  reads back: the algebraic identity is `tprSurgery`;
* the **affine projection hypothesis** formalizes the affine decoder
  (`tprReadout`) and the surgery correction (`tprSurgery_readout`);
* the **approximation hypothesis** (`TprApproxEntrywise`) bounds the
  readout error when the real state is only approximately a TPR
  superposition (`tprUnbind_approx`).

## Epistemic frontier (G7, #14366)

These definitions and theorems concern the TPR ALGEBRAIC MODEL only.
The empirical claim "GPT-OSS uses these roles" is NOT formalized
here: in McCoy et al.'s terms, the symbolic structure would emerge
only as APPROXIMATE. `TprApproxEntrywise` and `tprReadout` are
HYPOTHESES that a network may or may not satisfy — never conclusions
about a particular network.

i18n convention #4980 (sibling pair): this file is the English twin;
the canonical French file is `Sensitivity/TensorProductRepresentation.lean`
(namespace `Sensitivity.TPR`), with byte-identical statements and proofs.
-/

namespace Sensitivity_en.TPR

open Matrix

/-! ### Model definitions -/

variable {p q k m : ℕ}

/-- **Binding**: tensor product filler ⊗ role — the `p × q` matrix of
entries `f i * r j`. -/
def tprBind (f : Fin p → ℝ) (r : Fin q → ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  Matrix.of fun i j => f i * r j

/-- **Superposition**: sum of role-filler bindings — the TPR state. -/
def tprSuperpos (fs : Fin m → (Fin p → ℝ)) (rs : Fin m → (Fin q → ℝ)) :
    Matrix (Fin p) (Fin q) ℝ :=
  ∑ i, tprBind (fs i) (rs i)

/-- **Unbinding**: reading of the filler at role `r` by matrix-vector
product. -/
def tprUnbind (T : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) : Fin p → ℝ :=
  T *ᵥ r

/-- **Role independence**: orthonormal family w.r.t. the canonical inner
product — `rs i ⬝ᵥ rs j = δᵢⱼ`. This is the hypothesis under which
unbinding is EXACT. -/
def RoleFamily (rs : Fin m → (Fin q → ℝ)) : Prop :=
  ∀ i j, rs i ⬝ᵥ rs j = if i = j then 1 else 0

/-- **Affine projection hypothesis**: the decoder reads one role of the
state then applies an affine map `A · + b` (`tprReadout`). The decoder of
the studied networks is assumed affine — a hypothesis, not a theorem. -/
def tprReadout (A : Matrix (Fin k) (Fin p) ℝ) (b : Fin k → ℝ)
    (T : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) : Fin k → ℝ :=
  A *ᵥ (tprUnbind T r) + b

/-- **Approximation hypothesis**: the real state `S` is close, entry by
entry, to a TPR superposition `T` within `ε`. An explicit hypothesis —
the TPR-exactness of a real network is neither asserted nor provable
here. -/
def TprApproxEntrywise (S T : Matrix (Fin p) (Fin q) ℝ) (ε : ℝ) : Prop :=
  ∀ i j, |S i j - T i j| ≤ ε

/-! ### Entry lemmas: unbinding is linear and computes on a binding -/

@[simp]
theorem tprUnbind_bind (f : Fin p → ℝ) (r r' : Fin q → ℝ) :
    tprUnbind (tprBind f r) r' = fun κ => f κ * (r ⬝ᵥ r') := by
  funext κ
  simp [tprUnbind, tprBind, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem tprUnbind_sum (Ts : Fin m → Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) :
    tprUnbind (∑ i, Ts i) r = ∑ i, tprUnbind (Ts i) r := by
  simp [tprUnbind, Matrix.sum_mulVec]

theorem tprUnbind_sub (T T' : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) :
    tprUnbind (T - T') r = tprUnbind T r - tprUnbind T' r := by
  simp [tprUnbind, Matrix.sub_mulVec]

theorem tprUnbind_add (T T' : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) :
    tprUnbind (T + T') r = tprUnbind T r + tprUnbind T' r := by
  simp [tprUnbind, Matrix.add_mulVec]

/-! ### Theorem 1: exact unbinding under role independence -/

/-- **Exact unbinding**: under independence (orthonormality) of the roles,
reading the superposition at role `rs j` returns EXACTLY the filler
`fs j` — the other constituents cancel (`rs i ⬝ᵥ rs j = 0` for
`i ≠ j`). -/
theorem tprUnbind_superpos {fs : Fin m → (Fin p → ℝ)} {rs : Fin m → (Fin q → ℝ)}
    (h : RoleFamily rs) (j : Fin m) :
    tprUnbind (tprSuperpos fs rs) (rs j) = fs j := by
  unfold RoleFamily at h
  rw [tprSuperpos, tprUnbind_sum]
  funext κ
  simp only [tprUnbind_bind, h]
  simp

/-! ### Theorem 2: algebraic identity of constituent surgery -/

/-- **Constituent surgery** (McCoy et al., §interventions): replacing in
the state the binding of constituent `j` by that of a new filler `f'`,
then reading back at role `rs j`, returns exactly `f'` — the other
constituents contribute nothing. This is the algebraic identity of the
TPR model; what a real network approximates is an EMPIRICAL question,
out of scope. -/
theorem tprSurgery {fs : Fin m → (Fin p → ℝ)} {rs : Fin m → (Fin q → ℝ)}
    (h : RoleFamily rs) (j : Fin m) (f' : Fin p → ℝ) :
    tprUnbind (tprSuperpos fs rs - tprBind (fs j) (rs j) + tprBind f' (rs j)) (rs j)
      = f' := by
  rw [tprUnbind_add, tprUnbind_sub, tprUnbind_superpos h, tprUnbind_bind]
  funext κ
  simp [h j j]

/-! ### Theorem 3: affine projection and surgery -/

/-- **Surgery seen by the affine decoder**: under the model hypotheses
(role independence, affine decoder), the output of the surgered state
differs from the original output by `A *ᵥ (f' - fs j)` — a term that
depends ONLY on the replaced constituent, not on the others. This is
the algebraic form of "surgery on one constituent changes the readout
of that constituent and of no other" in the TPR model. -/
theorem tprSurgery_readout {fs : Fin m → (Fin p → ℝ)} {rs : Fin m → (Fin q → ℝ)}
    (h : RoleFamily rs) (j : Fin m) (f' : Fin p → ℝ)
    (A : Matrix (Fin k) (Fin p) ℝ) (b : Fin k → ℝ) :
    tprReadout A b (tprSuperpos fs rs - tprBind (fs j) (rs j) + tprBind f' (rs j)) (rs j)
      = tprReadout A b (tprSuperpos fs rs) (rs j) + A *ᵥ (f' - fs j) := by
  simp only [tprReadout]
  rw [tprSurgery h, tprUnbind_superpos h]
  funext κ
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  abel

/-! ### Theorem 4: stability of the readout under approximation -/

/-- **Approximate readout**: if the real state `S` is close to a TPR
superposition `T` within `ε` per entry, the read at role `r` is close
to the ideal filler within `ε * ∑ |r|` — the readout error is bounded
by the state error weighted by the role mass. This theorem makes the
approximation hypothesis operational: it quantifies WHAT CAN BE
CONCLUDED if a network satisfies `TprApproxEntrywise` (and nothing
otherwise). -/
theorem tprUnbind_approx (S T : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ)
    (ε : ℝ) (h : TprApproxEntrywise S T ε) (κ : Fin p) :
    |tprUnbind S r κ - tprUnbind T r κ| ≤ ε * ∑ j, |r j| := by
  have entry : ∀ j, |S κ j * r j - T κ j * r j| ≤ ε * |r j| := by
    intro j
    have key : |S κ j - T κ j| * |r j| ≤ ε * |r j| :=
      mul_le_mul_of_nonneg_right (h κ j) (abs_nonneg (r j))
    calc |S κ j * r j - T κ j * r j|
        = |(S κ j - T κ j) * r j| := by rw [sub_mul]
      _ = |S κ j - T κ j| * |r j| := abs_mul _ _
      _ ≤ ε * |r j| := key
  calc |tprUnbind S r κ - tprUnbind T r κ|
      = |∑ j, S κ j * r j - ∑ j, T κ j * r j| := by
        simp [tprUnbind, Matrix.mulVec, dotProduct]
    _ = |∑ j, (S κ j * r j - T κ j * r j)| := by rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ j, |S κ j * r j - T κ j * r j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ε * |r j| := Finset.sum_le_sum (fun j _ => entry j)
    _ = ε * ∑ j, |r j| :=
        (Finset.mul_sum Finset.univ (fun j => |r j|) ε).symm

end Sensitivity_en.TPR
