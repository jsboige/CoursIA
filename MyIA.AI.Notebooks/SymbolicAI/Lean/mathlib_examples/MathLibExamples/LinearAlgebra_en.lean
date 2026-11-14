import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear Algebra: the Axler staircase (steps 1 to 5)

This module is an **executable** progression in linear algebra, written to
fill the missing step between `Lean-06` (discovering Mathlib) and `Lean-12`
(sensitivity) / `Lean-13` (Kochen-Specker, CHSH): no notebook in the series
covers this foundation.

The order of the steps follows Sheldon Axler, *Linear Algebra Done Right*,
4th edition, Springer 2024, freely available under the **CC BY-NC 4.0**
license. Archived copy (bibliography-hygiene):
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\2024 - Axler - Linear Algebra Done Right (Springer, 4e edition, CC BY-NC 4.0, version 30 oct 2026).pdf`
Axler's choice of relegating determinants to the last chapter (ch. 9) is
respected: this module uses none. No statement or solution from the book is
copied; every exercise below is written for Mathlib.

**Prerequisites: only `Lean-01`..`Lean-06`.** The tactics `rw`, `exact`,
`simp`, `apply`, and the idea that a Mathlib theorem is found and cited. Each
step opens with the Mathlib definitions it uses, with their file.

Each exercise carries a **bridging sentence** to the notebook it unlocks:
steps 1-3 -> `Lean-12`, steps 4-5 -> `Lean-13`.

EN sibling (`LinearAlgebra_en.lean`) of the FR canonical (`LinearAlgebra.lean`),
per EPIC #4980 Lean FR+EN i18n convention (See #4980). Tactical code
byte-identical modulo namespace wrap (`MathLibExamples_en`, anti-collision);
docstrings and comments translated; statements, proofs and tactics unchanged.
-/

open scoped InnerProductSpace

namespace MathLibExamples_en

/-!
## Step 1 - Vector spaces (Axler ch. 1-2)

Mathlib definitions used:
* `Submodule.span R s` (`Mathlib.LinearAlgebra.Span.Defs`) - the smallest
  subspace containing `s`;
* `Basis` / `OrthonormalBasis` (`Mathlib.LinearAlgebra.Basis`) - a free and
  generating family; on a Euclidean space, of unit vectors orthogonal two by
  two;
* `Module.finrank R E` (`Mathlib.LinearAlgebra.Dimension`) - the dimension.

We instantiate them on `EuclideanSpace ℝ (Fin 3)`: vectors with 3
coordinates. **Bridge to `Lean-12`**: the inputs there are vectors, and
reading a vector as an explicit linear combination of basis vectors is its
first gesture.
-/

/-- The canonical basis of `ℝ³`, seen as an indexed family: each
`EuclideanSpace.single i 1` is the basis vector number `i`
(`EuclideanSpace.basisFun_apply`). -/
theorem exemple_base_canonique (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i = EuclideanSpace.single i 1 :=
  EuclideanSpace.basisFun_apply (Fin 3) ℝ i

/-- The dimension of `ℝ³` is 3 (`finrank_euclideanSpace_fin`). -/
theorem exemple_dimension : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
  simp

/-- **Exercise 1.1.** Every vector of `ℝ³` is an explicit linear combination
of the canonical basis vectors: the canonical basis spans the whole space.
That is the exact meaning of "basis" - and the first gesture of `Lean-12`
when it reads an input vector. -/
theorem exercice_1_1 (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 => EuclideanSpace.single i 1) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => v i, ?_⟩
  simpa [EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v

/-!
## Step 2 - Linear maps (Axler ch. 3)

Mathlib definitions used:
* `LinearMap` (`→ₗ`) - a map compatible with `+` and `•`; built from a
  matrix by `Matrix.toLpLin 2 2 A` (`Mathlib.Analysis.Normed.Lp.Matrix`):
  `A` acts by matrix-vector product;
* `LinearMap.ker f` - the vectors sent to zero; `LinearMap.range f` - the
  image;
* `LinearMap.finrank_range_add_finrank_ker` and
  `LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank`
  (`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`) - the **rank theorem**
  and its corollary in equal dimension.

**Bridge to `Lean-12`**: the layers of a sensitivity network are linear
maps; "the layer loses no information" is written there `ker = ⊥`.
-/

/-- The shear operator of `ℝ²`: matrix `!![1, 1; 0, 1]`. -/
def cisaillement : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toLpLin 2 2 !![1, 1; 0, 1]

/-- **Exercise 2.1.** The shear is injective: its kernel is trivial.
Proof: `Matrix.toLpLin_apply` brings the computation back to a
matrix-vector product, then each coordinate is read off the matrix
(`w 1 = 0`, then `w 0 = 0`). -/
theorem exercice_2_1 : LinearMap.ker cisaillement = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  simp only [cisaillement, Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hv
  have h1 : v 1 = 0 := by
    have h := congrFun hv 1
    simpa [Matrix.mulVec, dotProduct] using h
  have h0 : v 0 = 0 := by
    have h := congrFun hv 0
    simpa [Matrix.mulVec, dotProduct, h1] using h
  ext j
  fin_cases j
  · exact h0
  · exact h1

/-- The rank theorem, instantiated on the shear: rank + kernel = 2. -/
theorem exemple_theoreme_du_rang :
    Module.finrank ℝ (LinearMap.range cisaillement)
      + Module.finrank ℝ (LinearMap.ker cisaillement)
      = 2 := by
  rw [LinearMap.finrank_range_add_finrank_ker]
  simp

/-- **Exercise 2.2.** Corollary of the rank theorem in equal dimension: an
injective endomorphism of `ℝ²` is surjective - the image fills the space. -/
theorem exercice_2_2 : LinearMap.range cisaillement = ⊤ :=
  (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl).mp exercice_2_1

/-!
## Step 3 - Eigenvalues (Axler ch. 5)

Mathlib definitions used (`Mathlib.LinearAlgebra.Eigenspace`):
* `Module.End.HasEigenvector f μ x` - `f x = μ • x` with `x ≠ 0` (via
  `Module.End.mem_eigenspace_iff`);
* `Module.End.HasEigenvalue f μ` - such a vector exists;
* `Module.End.hasEigenvalue_iff_isRoot` (`Eigenspace.Minpoly`) - `μ` is an
  eigenvalue iff `μ` is a root of the minimal polynomial;
* over an algebraically closed field, `Module.End.exists_eigenvalue`
  (`Eigenspace.Triangularizable`): every endomorphism of a nonzero
  finite-dimensional space has an eigenvalue.

**Bridge to `Lean-12` / `Lean-13`**: the sensitivity of a network is read on
its Jacobian matrix; eigenvalues are its vocabulary. Over `ℂ`, existence is
guaranteed - the reason for the complex vectors in `Lean-13`.
-/

/-- The diagonal `diag(2, 3)` on `ℂ²`. -/
def diag23 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toLpLin 2 2 !![2, 0; 0, 3]

/-- **Exercise 3.1.** `2` is an eigenvalue of `diag23`, with eigenvector
`e₀ = single 0 1`: direct computation, coordinate by coordinate. -/
theorem exercice_3_1 : Module.End.HasEigenvector diag23 2
    (EuclideanSpace.single (0 : Fin 2) 1) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext j
    fin_cases j <;>
      simp [diag23, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, PiLp.single_apply, PiLp.smul_apply, smul_eq_mul] <;>
      ring
  · intro hcontra
    have h0 := PiLp.ext_iff.mp hcontra 0
    simp [PiLp.single_apply] at h0

/-- The theoretical link (cited, not recomputed): eigenvalues are exactly
the roots of the minimal polynomial. -/
theorem exemple_valeurs_propres_minpoly (f : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
    (μ : ℂ) :
    f.HasEigenvalue μ ↔ (minpoly ℂ f).IsRoot μ :=
  Module.End.hasEigenvalue_iff_isRoot

/-- **Exercise 3.2.** Over `ℂ`, the existence of an eigenvalue is guaranteed
for every endomorphism of a nonzero finite-dimensional space - it is the
fundamental theorem of algebra at work. -/
theorem exercice_3_2 (f : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∃ μ, Module.End.HasEigenvalue f μ :=
  Module.End.exists_eigenvalue f

/-!
## Step 4 - Inner product and orthonormalization (Axler ch. 6)

Mathlib definitions used:
* `⟪x, y⟫` (`inner`) - the inner product; on `EuclideanSpace`,
  `PiLp.inner_apply` unfolds it as a sum of coordinate-by-coordinate
  products (`Mathlib.Analysis.InnerProductSpace.PiL2`);
* `Orthonormal` - a family of unit vectors orthogonal two by two;
* `gramSchmidtOrthonormalBasis`
  (`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`) - the
  Gram-Schmidt process: from any generating family of cardinality the
  dimension, one extracts an orthonormal basis.

**Bridge to `Lean-13`**: the states there are vectors of a finite-dimensional
real Hilbert space; orthogonality of two measurements is a zero inner
product.
-/

/-- The usual inner product of `ℝ²`, computed coordinate by coordinate. -/
theorem exemple_produit_scalaire (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **Exercise 4.1.** Two distinct basis vectors are orthogonal: the inner
product keeps only the common coordinate - which does not exist. -/
theorem exercice_4_1 {i j : Fin 3} (h : i ≠ j) :
    ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, PiLp.single_apply, h]

/-- **Exercise 4.2.** The diagonals `(1, 1)` and `(1, -1)` of the plane are
orthogonal - the full computation, no theory. -/
theorem exercice_4_2 :
    ⟪(EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 :
        EuclideanSpace ℝ (Fin 2)),
      (EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1)⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, PiLp.single_apply, inner_add_left,
    inner_sub_right, Fin.sum_univ_two]

/-- The Gram-Schmidt process (cited): from any basis of a finite-dimensional
Euclidean space, one extracts an orthonormal basis. -/
noncomputable def exemple_gram_schmidt (b : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) b

/-!
## Step 5 - Self-adjoint operators and the spectral theorem (Axler ch. 7)

Mathlib definitions used:
* `LinearMap.adjoint` (`Mathlib.Analysis.InnerProductSpace.Adjoint`) - the
  adjoint `f†`, defined by `⟪f x, y⟫ = ⟪x, f† y⟫`;
* `LinearMap.IsSymmetric` (`Mathlib.Analysis.InnerProductSpace.Symmetric`) -
  `∀ x y, ⟪f x, y⟫ = ⟪x, f y⟫`, equivalent to `IsSelfAdjoint`
  (`isSymmetric_iff_isSelfAdjoint`);
* `LinearMap.IsSymmetric.eigenvectorBasis`
  (`Mathlib.Analysis.InnerProductSpace.Spectrum`) - **the spectral theorem**:
  a self-adjoint operator of a finite-dimensional Euclidean space admits an
  **orthonormal basis of eigenvectors**, with real eigenvalues sorted.

**Bridge to `Lean-13`**: the CHSH correlation operator is self-adjoint; its
computation goes through its eigenvalues - exactly this step.
-/

/-- The symmetric operator with matrix `!![2, 1; 1, 2]` on `ℝ²`. -/
def T_sym : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toLpLin 2 2 !![2, 1; 1, 2]

/-- **Exercise 5.1.** `T_sym` is self-adjoint: the two sides of
`⟪T x, y⟫ = ⟪x, T y⟫` unfold into the same polynomial in the coordinates -
the symmetry of the matrix, computed by hand. -/
theorem exercice_5_1 : T_sym.IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fin.sum_univ_two, T_sym, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- **Exercise 5.2.** The spectral theorem applied: `T_sym` admits an
orthonormal basis of eigenvectors. No eigenvalue is computed here - it is
the existence that is Axler's ch. 7 result. -/
theorem exercice_5_2 :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      ∃ μ : Fin 2 → ℝ, ∀ i, T_sym (b i) = ((μ i : ℝ) : ℝ) • b i :=
  ⟨exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin,
    fun i => exercice_5_1.eigenvalues finrank_euclideanSpace_fin i,
    fun i => exercice_5_1.apply_eigenvectorBasis finrank_euclideanSpace_fin i⟩

/-- **Exercise 5.3.** The vector `(1, 1)` is an eigenvector of `T_sym` for
the eigenvalue `3`: direct computation, no spectral theorem. -/
theorem exercice_5_3 : Module.End.HasEigenvector T_sym 3
    (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 :
      EuclideanSpace ℝ (Fin 2)) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext j
    fin_cases j <;>
      simp [T_sym, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, WithLp.ofLp_add, PiLp.single_apply, PiLp.smul_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.head_cons] <;>
      ring
  · intro hcontra
    have h0 := PiLp.ext_iff.mp hcontra 0
    simp [WithLp.ofLp_add, PiLp.single_apply] at h0

/-- Diagonalization (cited): in the orthonormal basis of eigenvectors of
Exercise 5.2, the matrix of `T_sym` is diagonal - the operator form of the
spectral theorem (`IsSymmetric.toMatrix_eigenvectorBasis`). -/
theorem exemple_diagonalisation :
    T_sym.toMatrix (exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis
        (exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis
      = Matrix.diagonal
          (RCLike.ofReal ∘ exercice_5_1.eigenvalues finrank_euclideanSpace_fin) :=
  exercice_5_1.toMatrix_eigenvectorBasis finrank_euclideanSpace_fin

end MathLibExamples_en
