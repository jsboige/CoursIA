import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Classical Hecke operators on the upper half-plane

This module introduces the "classical" Hecke operators: for an integer `p`
(usually prime), the operator `T_p` acts on a function `f` of the upper
half-plane ℍ by a finite sum of slash actions over explicit representatives
of the classes `Γ(1) \ M₂(ℤ)` of determinant `p`, and the operator `U_p`
keeps only the triangular part. The induced formula on Fourier
coefficients — `a(np) + p^{k-1} a(n/p)` according to whether `p` divides
`n` — is formalized by `coeffHeckeT`.

**Provenance**: this file is a port of the
`anthropics/fermats-last-theorem` repository (file
`Definitions/Def_ModularForm_HeckeOperator.lean`, commit `aa2d8b34692b`),
with English docstrings and added computable examples (`Examples` section
at the end of the module). Statements and proofs are carried over
unchanged; the Apache-2.0 license is preserved (see `NOTICE.md`).

The Petersson product and cusp forms are outside the scope of this first
tranche (downstream grain).
-/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm_en

/-- The upper-triangular matrix `!![a, b; 0, d]` viewed as an element of
`GL (Fin 2) ℝ`, under the hypothesis `a * d ≠ 0` guaranteeing invertibility
(the determinant is then `a * d ≠ 0`). This is the building block of the
Hecke representatives. -/
def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

/-- The representative `γ_{p,j} = !![1, j; 0, p]`: the family
`heckeMatrix p 0, …, heckeMatrix p (p-1)` enumerates the left classes of
`Γ(1)` among integer matrices of determinant `p` whose reduction modulo
`p` is upper-triangular (the "U" part of the operator `T_p`). The
degenerate case `p = 0` is neutralized by returning the identity. -/
def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

/-- The diagonal representative `!![p, 0; 0, 1]` of determinant `p`: the
"diagonal" class that completes `U_p` into `T_p` (the term
`f ∣[k] heckeDiagMatrix p` of `heckeT`). -/
def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

@[simp] theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

/-- The determinant of the representative `γ_{p,j}` is exactly `p`. -/
theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

/-- The determinant of the diagonal representative is exactly `p`. -/
theorem det_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) : ((heckeDiagMatrix p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hp, Matrix.det_fin_two_of]
  ring

/-- The determinant of `γ_{p,j}` is positive (including the degenerate case
`p = 0`, where the matrix is the identity): Hecke representatives preserve
the upper half-plane. -/
theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

/-- Diagonal version of `det_heckeMatrix_pos`. -/
theorem det_heckeDiagMatrix_pos (p : ℕ) : 0 < ((heckeDiagMatrix p).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeDiagMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

/-- The denominator of the action of `γ_{p,j}` on `τ` is `p`: this `1/p`
factor will appear in front of the sum in `heckeU_apply`. -/
theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

/-- The denominator of the diagonal representative is `1`: its action
contributes no `1/p` factor. -/
theorem denom_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeDiagMatrix p) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hp]

/-- The action of `γ_{p,j}` on `τ ∈ ℍ` is the homothety-translation
`(τ + j) / p`: the `p` "U" representatives cut the neighbourhood of the
cusp into `p` translates squashed by `1/p`. -/
theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

/-- The action of the diagonal representative is the dilation `p • τ`. -/
theorem coe_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hp]

/-- The character `σ` of the Hecke representatives is trivial: they act
without extra conjugation (positive determinant). -/
theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeMatrix_pos p j)]

/-- Diagonal version of `σ_heckeMatrix`. -/
theorem σ_heckeDiagMatrix (p : ℕ) : UpperHalfPlane.σ (heckeDiagMatrix p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeDiagMatrix_pos p)]

/-- The slash by `γ_{p,j}`: `(f ∣[k] γ_{p,j}) τ = p⁻¹ • f (γ_{p,j} • τ)`.
This is the explicit reading of the slash action on a "U" representative. -/
theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

/-- The slash by the diagonal representative carries the power `p^(k-1)`
characteristic of the weight `k`. -/
theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hp, denom_heckeDiagMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast, one_zpow, mul_one]
  rw [mul_comm]

/-- The operator `U_p`: sum of the slashes by the `p` triangular
representatives `γ_{p,j}`, `j = 0, …, p-1`. -/
def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

/-- The Hecke operator `T_p = U_p + f ∣[k] (diagonal)`: the classical
definition on explicit representatives of `Γ(1)`. -/
def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeU_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j := rfl

theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

theorem heckeT_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = (∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j) + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

/-- Degenerate case `p = 0`: `T_0` is the identity. -/
@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

/-- Pointwise reading of `U_p`: average (up to the `p⁻¹` factor) of the
values of `f` on the `p` translates `(τ + j)/p`. -/
theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

/-- Pointwise reading of `T_p`: sum of the `U_p` part and the diagonal
term `p^(k-1) • f (p • τ)`. -/
theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

/-- Linearity of `U_p` in its argument: `U_p (f + g) = U_p f + U_p g`. -/
theorem heckeU_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

/-- Linearity of `T_p` in its argument. -/
theorem heckeT_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

/-- Homogeneity of `U_p`: `U_p (c • f) = c • U_p f`. -/
theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply,
    Finset.smul_sum]

/-- Homogeneity of `T_p`. -/
theorem heckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeT k p (c • f) = c • heckeT k p f := by
  rw [heckeT, heckeT, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply, smul_add]

theorem heckeU_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeU k p (-f) = -heckeU k p f := by
  simp [heckeU, Finset.sum_neg_distrib]

theorem heckeT_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeT k p (-f) = -heckeT k p f := by
  simp only [heckeT, heckeU_neg, SlashAction.neg_slash, neg_add]

theorem heckeU_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f - g) = heckeU k p f - heckeU k p g := by
  rw [sub_eq_add_neg, heckeU_add, heckeU_neg, ← sub_eq_add_neg]

theorem heckeT_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f - g) = heckeT k p f - heckeT k p g := by
  rw [sub_eq_add_neg, heckeT_add, heckeT_neg, ← sub_eq_add_neg]

/-- The Hecke coefficient formula: if `f = ∑ a n q^n`, then
`T_p f = ∑ (coeffHeckeT k p a n) q^n` with
`coeffHeckeT k p a n = a (n p) + p^(k-1) a (n/p)` when `p ∣ n`
(the second term vanishes otherwise). This is the combinatorial
transcription of the geometric action of `T_p` on Fourier coefficients. -/
def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

/-- The coefficient formula of the `U_p` part: a plain "sampling"
`a (n p)` of the sequence. -/
def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

/-- Reading of `coeffHeckeT` in the case `p ∣ n`: both contributions
coexist. -/
theorem coeffHeckeT_of_dvd (k : ℤ) {p n : ℕ} (h : p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) + (p : ℂ) ^ (k - 1) * a (n / p) := by
  rw [coeffHeckeT, if_pos h]

/-- Reading of `coeffHeckeT` in the case `p ∤ n`: only the sampling term
`a (n p)` remains. -/
theorem coeffHeckeT_of_not_dvd (k : ℤ) {p n : ℕ} (h : ¬ p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) := by
  rw [coeffHeckeT, if_neg h, add_zero]

theorem coeffHeckeT_eq_coeffHeckeU_add (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = coeffHeckeU p a n + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeT_add (k : ℤ) (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeT k p (a + b) = coeffHeckeT k p a + coeffHeckeT k p b := by
  funext n
  simp only [coeffHeckeT, Pi.add_apply]
  split_ifs <;> ring

theorem coeffHeckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeT k p (c • a) = c • coeffHeckeT k p a := by
  funext n
  simp only [coeffHeckeT, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem coeffHeckeU_add (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeU p (a + b) = coeffHeckeU p a + coeffHeckeU p b := rfl

theorem coeffHeckeU_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeU p (c • a) = c • coeffHeckeU p a := rfl

/-!
## Computable examples

These examples (absent from the upstream file) connect the operator to
the concrete reading of coefficients: for the sequence `a n = n` and
weight `k = 12` (that of the discriminant modular form Δ), the formula
`a (n p) + p^(k-1) a (n/p)` is read off directly, according to the
divisibility of `n` by `p`.
-/

/-- `T_0` is the identity, including on functions. -/
example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by simp

/-- `U_p` samples: `coeffHeckeU 2 a 3 = a 6`, with no extra factor. -/
example : coeffHeckeU 2 (fun n => (n : ℂ)) 3 = 6 := rfl

/-- `2 ∤ 1`: only the sampling term remains, `coeffHeckeT = a 2 = 2`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 1 = 2 := by
  have h : ¬ (2 : ℕ) ∣ 1 := by decide
  simp only [coeffHeckeT, if_neg h]
  norm_num

/-- `2 ∣ 2`: both terms coexist, `a 4 + 2¹¹ • a 1 = 4 + 2¹¹`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 2 = 4 + 2 ^ 11 := by
  have h : (2 : ℕ) ∣ 2 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

/-- `2 ∤ 3`: sampling only again, `a 6 = 6`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 3 = 6 := by
  have h : ¬ (2 : ℕ) ∣ 3 := by decide
  simp only [coeffHeckeT, if_neg h]
  norm_num

/-- Same reading for `p = 3`: `3 ∣ 3` gives `a 9 + 3¹¹ • a 1 = 9 + 3¹¹`. -/
example : coeffHeckeT 12 3 (fun n => (n : ℂ)) 3 = 9 + 3 ^ 11 := by
  have h : (3 : ℕ) ∣ 3 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

/-- A zero-index coefficient gives access to `a 0`: the eigenvalue of the
constant term under `T_p` is `1 + p^(k-1)` (for `a ≡ 1`). -/
example : coeffHeckeT 12 2 (fun _ => (1 : ℂ)) 2 = 1 + 2 ^ 11 := by
  have h : (2 : ℕ) ∣ 2 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

end ModularForm_en

end
