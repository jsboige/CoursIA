/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Saturation of the Tsirelson bound: the Pauli witness and Landau's criterion

This module is the fourth tranche of the quantum pilot of Epic #13106. The
first three bounded the deterministic classical frontier (`Conway.CHSH`),
its randomized envelope (`Conway.CHSHRandomized`), then imported Mathlib's
quantum bound `2√2` together with its hypothesis map (`Conway.CHSHQuantum`).
`Conway.CHSHQuantum` left four points declared **not established**; this
tranche lifts three of them through a single explicit construction:

1. **Saturation** — the witness's CHSH operator equals *exactly* `2√2 • 1`,
   an equality rather than a bound: Tsirelson's constant is attained;
2. **Matrix construction** — four explicit observables on ℝ^(2×2),
   combinations of the Pauli matrices σz and σx;
3. **Two-sided spectral form** — `chsh_landau_diagonal`: the operator is
   diagonal with `2√2` on the diagonal — every basis vector is an
   eigenvector, the equality holds on both sides. (The "operator norm" of
   `CHSHQuantum`'s status table is delivered here as an explicit spectral
   form: in Mathlib v4.32.1 matrix norms are scoped non-instances
   (`Matrix.Norms.Operator`), and the exact equality `S = 2√2 • 1` carries
   the substance — the bound is attained, not merely true.)

### The reduced model, and what it does not claim to be

The observables live in `Matrix (Fin 2) (Fin 2) ℝ`: this is the **reduced**
single-qubit model, where the product `Aᵢ * Bⱼ` is the matrix product of the
reduced representatives. In the unreduced tensor model (operators `A ⊗ 1` and
`1 ⊗ B` on ℝ⁴), cross-commutation `Aᵢ Bⱼ = Bⱼ Aᵢ` is a structural hypothesis
of Mathlib's `IsCHSHTuple`; in the reduced model it is **false** —
`[σz, σz + σx] = [σz, σx] ≠ 0` — and this module does not claim it. What it
establishes is more modest and exact: the value of the witness's CHSH
operator, i.e. the constant that the abstract bound majorizes, is *realized*
by a concrete construction. The full probabilistic interpretation (states,
measurements, expectations on the tensor model) remains declared open, as in
`Conway.CHSHQuantum`.

### Landau: what is retained, what remains open

Landau (1988) characterizes the maximal quantum CHSH value of a correlation
matrix `C` through the eigenvalues of its symmetric part. This module does
not formalize the general theorem (a complete SDP proof); it checks the
criterion **on the witness**: the reduced correlation matrix

- is symmetric,
- squares to the identity, hence has eigenvalues ±1,

and the witness's score is `2√2` — the value Landau's characterization
predicts for that spectrum. The "sufficient" direction is thus documented by
an explicit witness; the general characterization (necessary and sufficient)
remains open and declared.

### Statement status (digestion grid #13106)

| Statement | Status |
|---|---|
| Witness's CHSH operator `= 2√2 • 1` (exact equality) | **proved here** |
| Involutivity of the four observables (`M² = 1`) | **proved here** |
| Self-adjointness (symmetry of the real matrices) | **proved here** |
| Spectral form: `S` diagonal, `2√2` on the diagonal (two-sided) | **proved here** |
| Symmetric correlation matrix squaring to `1` (spectrum ±1) | **proved here** |
| Landau's general characterization (theorem, both directions) | **not established** — witness check only |
| Full probabilistic interpretation (states, measurements, tensor ℝ⁴) | **not established** — declared open |
| Cross-commutation in the reduced model | **false** and not claimed (see above) |

### Digestion grid (10 points)

1. **Statements and guarantee level**: exact matrix equalities over ℝ, no
   functional analysis; the constant `2√2` is the one of
   `Conway.CHSHQuantum.tsirelson_bound`.
2. **Provenance**: L. J. Landau, "On the violation of Bell inequalities in
   quantum theory", Physics Letters A 120 (1988), 54-56; standard saturation
   construction (Tsirelson 1980; pedagogical account Nielsen & Chuang
   §2.4-2.5). Priority of the characterization: Landau 1988; of the bound:
   Tsirelson 1980.
3. **Novelty**: the CHSH series had the bound (imported) and the strict gap
   `2 < 2√2`; the equality witness is new to the repository.
4. **Dependencies**: Mathlib v4.32.1 (`Matrix`, `Real.sqrt`, `!![...]`
   notation via `Mathlib.LinearAlgebra.Matrix.Notation`),
   reuses `Conway.CHSHQuantum.chshOperator` without redefining it; no
   `sorry`, no axioms beyond the standard ones.
5. **Trivial condensed / new developed**: the squares of σz, σx are
   entry-level computations; the heart is the anticommutator
   `σzσx + σxσz = 0`, from which follow the involutivity of the `Bⱼ` and the
   central equality — the proofs are entry-level (ext + fin_cases): matrix
   non-commutativity forbids `ring`, so each identity is distributed then
   closed on the atom `(√2)² = 2`.
6. **Friction**: the reduced model does not carry cross-commutation (a
   hypothesis of the abstract tuple) — that is the declared limit, detailed
   above; handling `√2` goes through the atom `hsq : (√2)² = 2` and
   `linear_combination`, never through a numerical approximation.
7. **Discovery path**: (1) reduce the tensor to the single qubit;
   (2) check anticommutation; (3) derive `S = (4/√2) • 1` by distributivity,
   then `4/√2 = 2√2`; (4) only then compute the correlations. The final
   reconstruction follows the same order, each intermediate lemma carrying
   one step.
8. **Limits**: the three "not established / false" rows of the status table.
9. **Corpus connection**: fourth module of the CHSH series of `conway_lean`
   (with `CHSH`, `CHSHRandomized`, `CHSHQuantum`); notebook pointers:
   `Lean-13b-CHSH-Tsirelson-Native` (native execution of the series under
   the `lean4-wsl` kernel — a future tranche may execute this module's
   statements there), `Lean-13-Kochen-Specker`,
   `Lean-16f-Conway-Free-Will-Theorem`.
10. **Transmission**: each lemma carries a docstring separating what the
    computation's output shows from what it suggests; the status table is
    the falsifiable summary.

### Sources

- L. J. Landau, "On the violation of Bell inequalities in quantum theory",
  Physics Letters A 120 (1988), 54-56.
- B. S. Cirel'son (Tsirelson), "Quantum generalizations of Bell's
  inequality", Letters in Mathematical Physics 4 (1980), 93-100.
- M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information*,
  Cambridge University Press (2000), §2.4-2.5.
-/

import Conway.CHSHQuantum_en
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Conway_en
namespace CHSHLandau_en

/-! ### The Pauli building blocks on ℝ^(2×2) -/

/-- Pauli matrix `σz = diag(1, -1)`, representative of the "spin along z"
observable: self-adjoint, involutive, diagonal. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Pauli matrix `σx`, representative of the "spin along x" observable:
self-adjoint, involutive, antidiagonal. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The computation atom of the module: `√2` is handled as a formal quantity
through its square. No proof below uses a numerical approximation. -/
theorem sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sigmaZ_sq : sigmaZ * sigmaZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sigmaX_sq : sigmaX * sigmaX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Anticommutator of the two Paulis: `σzσx + σxσz = 0`.

This is the algebraic heart of the module — from it follow the involutivity
of the `B` observables (their square mixes `σzσx` and `σxσz`) and the central
equality (the cross terms of the CHSH operator cancel pairwise). -/
theorem sigmaZ_anticomm_sigmaX : sigmaZ * sigmaX + sigmaX * sigmaZ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sigmaZ_symm : Matrix.transpose sigmaZ = sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ]

theorem sigmaX_symm : Matrix.transpose sigmaX = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX]

/-! ### The four observables of the witness -/

/-- Alice's observable `A₀ = σz`. -/
def A₀ : Matrix (Fin 2) (Fin 2) ℝ := sigmaZ

/-- Alice's observable `A₁ = σx`. -/
def A₁ : Matrix (Fin 2) (Fin 2) ℝ := sigmaX

/-- Bob's observable `B₀ = (σz + σx)/√2`. -/
noncomputable def B₀ : Matrix (Fin 2) (Fin 2) ℝ := (√2 : ℝ)⁻¹ • (sigmaZ + sigmaX)

/-- Bob's observable `B₁ = (σz - σx)/√2`. -/
noncomputable def B₁ : Matrix (Fin 2) (Fin 2) ℝ := (√2 : ℝ)⁻¹ • (sigmaZ - sigmaX)

theorem A₀_sq : A₀ * A₀ = 1 := sigmaZ_sq

theorem A₁_sq : A₁ * A₁ = 1 := sigmaX_sq

/-- Involutivity of `B₀`: the square of `(σz + σx)/√2` is the identity
because the cross terms cancel by anticommutation and
`(1/√2)² · (1 + 1) = 1`. Each entry is closed on the atom `sqrt_two_sq`. -/
theorem B₀_sq : B₀ * B₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₀, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two, sigmaZ, sigmaX, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

/-- Involutivity of `B₁`, by the same scheme as `B₀_sq`: the cross terms
change sign but cancel just the same. -/
theorem B₁_sq : B₁ * B₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Fin.sum_univ_two, sigmaZ, sigmaX,
      Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

theorem B₀_symm : Matrix.transpose B₀ = B₀ := by
  rw [B₀]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, sigmaZ_symm, sigmaX_symm]

theorem B₁_symm : Matrix.transpose B₁ = B₁ := by
  rw [B₁]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, sigmaZ_symm, sigmaX_symm]

/-! ### The central equality: the witness's CHSH operator is exactly `2√2` -/

/-- **Saturation of the Tsirelson bound** (sufficient direction of Landau's
criterion, by explicit witness): the CHSH operator of the quadruple
`(σz, σx, (σz+σx)/√2, (σz-σx)/√2)` equals *exactly* `2√2 • 1` — every
vector is an eigenvector with eigenvalue `2√2`, and the constant that
`Conway.CHSHQuantum.tsirelson_bound` majorizes is attained.

The algebraic reading: by distributivity, `S = (1/√2) • (σz(σz+σx) +
σz(σz-σx) + σx(σz+σx) - σx(σz-σx))`; the eight products reorder into
`2·σz² + 2·σx²` plus four cross terms `σzσx + σxσz` that cancel pairwise by
`sigmaZ_anticomm_sigmaX`; what remains is `(4/√2) • 1`, and `4/√2 = 2√2`
by `sqrt_two_sq`. The proof carries out this program entry by entry. -/
theorem chsh_landau :
    CHSHQuantum_en.chshOperator A₀ A₁ B₀ B₁ = (2 * √2 : ℝ) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CHSHQuantum_en.chshOperator, A₀, A₁, B₀, B₁, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two,
      sigmaZ, sigmaX, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

/-- **Two-sided spectral form**: the witness's CHSH operator is diagonal,
with `2√2` on the diagonal and `0` elsewhere — every basis vector is an
eigenvector with eigenvalue `2√2`. This is the "two-sided" leg the series
was missing: `Conway.CHSHQuantum.tsirelson_bound` gives `≤ 2√2` in general,
and the central equality `chsh_landau`, made entrywise here, shows the
bound is *attained* — the majorization is an equality, on both sides. -/
theorem chsh_landau_diagonal (i j : Fin 2) :
    CHSHQuantum_en.chshOperator A₀ A₁ B₀ B₁ i j = if i = j then 2 * √2 else 0 := by
  rw [chsh_landau]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply]

/-! ### Correlation matrix and Landau's criterion (checked on the witness) -/

/-- Reduced correlation matrix of the witness: entry `(i, j)` is the
correlation of the quadruple's observables `Aᵢ` and `Bⱼ`, all equal to
`1/√2` up to sign (entry `(1,1)` carries the `-` sign of the CHSH
operator's `- A₁ * B₁` term). -/
noncomputable def corrMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(√2 : ℝ)⁻¹, (√2 : ℝ)⁻¹; (√2 : ℝ)⁻¹, -(√2 : ℝ)⁻¹]

/-- The witness's correlation matrix is symmetric — the first half of the
hypothesis of Landau's criterion (1988). -/
theorem corrMatrix_symm : Matrix.transpose corrMatrix = corrMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMatrix]

/-- The square of the correlation matrix is the identity: its spectrum is
exactly `{-1, 1}` — the second half of Landau's criterion, checked on the
witness. The general characterization (both directions, for any correlation
matrix) remains declared open. -/
theorem corrMatrix_sq : corrMatrix * corrMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corrMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

end CHSHLandau_en
end Conway_en
