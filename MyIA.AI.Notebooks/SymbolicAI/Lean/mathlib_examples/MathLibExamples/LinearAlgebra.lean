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
# Linear Algebra : la marche Axler (paliers 1 a 5)

Ce module est une progression d'algebre lineaire **executable**, ecrite pour
combler la marche manquante entre `Lean-06` (decouvrir Mathlib) et `Lean-12`
(sensibilite) / `Lean-13` (Kochen-Specker, CHSH) : aucun carnet de la serie ne
couvre ce socle.

L'ordre des paliers suit Sheldon Axler, *Linear Algebra Done Right*, 4e edition,
Springer 2024, en acces libre sous licence **CC BY-NC 4.0**. Copie archivee
(bibliography-hygiene) :
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\2024 - Axler - Linear Algebra Done Right (Springer, 4e edition, CC BY-NC 4.0, version 30 oct 2026).pdf`
Le choix d'Axler de releguer les determinants au dernier chapitre (ch. 9) est
respecte : ce module n'en utilise aucun. Aucun enonce ni solution du livre
n'est recopie ; chaque exercice ci-dessous est ecrit pour Mathlib.

**Prerequis : uniquement `Lean-01`..`Lean-06`.** Les tactiques `rw`, `exact`,
`simp`, `apply`, et l'idee qu'un theoreme Mathlib se trouve et se cite. Chaque
palier ouvre par les definitions Mathlib qu'il utilise, avec leur fichier.

Chaque exercice porte une **phrase de liaison** vers le carnet qu'il debloque :
paliers 1-3 -> `Lean-12`, paliers 4-5 -> `Lean-13`.
-/

open scoped InnerProductSpace

/-!
## Palier 1 - Espaces vectoriels (Axler ch. 1-2)

Definitions Mathlib utilisees :
* `Submodule.span R s` (`Mathlib.LinearAlgebra.Span.Defs`) - le plus petit
  sous-espace contenant `s` ;
* `Basis` / `OrthonormalBasis` (`Mathlib.LinearAlgebra.Basis`) - une famille
  libre et generatrice ; sur un espace euclidien, de vecteurs unitaires deux a
  deux orthogonaux ;
* `Module.finrank R E` (`Mathlib.LinearAlgebra.Dimension`) - la dimension.

On les instancie sur `EuclideanSpace ℝ (Fin 3)` : les vecteurs a 3 coordonnees.
**Liaison `Lean-12`** : les entrees y sont des vecteurs, et lire un vecteur
comme combinaison lineaire explicite de vecteurs de base en est le premier
geste.
-/

/-- La base canonique de `ℝ³`, vue comme famille indexee : chaque
`EuclideanSpace.single i 1` est le vecteur de base numero `i`
(`EuclideanSpace.basisFun_apply`). -/
theorem exemple_base_canonique (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i = EuclideanSpace.single i 1 :=
  EuclideanSpace.basisFun_apply (Fin 3) ℝ i

/-- La dimension de `ℝ³` est 3 (`finrank_euclideanSpace_fin`). -/
theorem exemple_dimension : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
  simp

/-- **Exercice 1.1.** Tout vecteur de `ℝ³` est combinaison lineaire explicite
des vecteurs de la base canonique : la base canonique engendre tout l'espace.
C'est le sens exact de « base » - et le premier geste de `Lean-12` quand il
lit un vecteur d'entrees. -/
theorem exercice_1_1 (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 => EuclideanSpace.single i 1) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => v i, ?_⟩
  simpa [EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v

/-!
## Palier 2 - Applications lineaires (Axler ch. 3)

Definitions Mathlib utilisees :
* `LinearMap` (`→ₗ`) - application compatible avec `+` et `•` ; construite
  depuis une matrice par `Matrix.toLpLin 2 2 A`
  (`Mathlib.Analysis.Normed.Lp.Matrix`) : `A` agit par produit matrice-vecteur ;
* `LinearMap.ker f` - les vecteurs envoyes sur zero ; `LinearMap.range f` -
  l'image ;
* `LinearMap.finrank_range_add_finrank_ker` et
  `LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank`
  (`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`) - le **theoreme du rang**
  et son corollaire en dimension egale.

**Liaison `Lean-12`** : les couches d'un reseau de sensibilite sont des
applications lineaires ; « la couche ne perd aucune information » s'y ecrit
`ker = ⊥`.
-/

/-- L'operateur de cisaillement de `ℝ²` : matrice `!![1, 1; 0, 1]`. -/
def cisaillement : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toLpLin 2 2 !![1, 1; 0, 1]

/-- **Exercice 2.1.** Le cisaillement est injectif : son noyau est trivial.
Preuve : `Matrix.toLpLin_apply` ramene le calcul a un produit matrice-vecteur,
puis chaque coordonnee se lit sur la matrice (`w 1 = 0`, puis `w 0 = 0`). -/
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

/-- Le theoreme du rang, instancie sur le cisaillement : rang + noyau = 2. -/
theorem exemple_theoreme_du_rang :
    Module.finrank ℝ (LinearMap.range cisaillement)
      + Module.finrank ℝ (LinearMap.ker cisaillement)
      = 2 := by
  rw [LinearMap.finrank_range_add_finrank_ker]
  simp

/-- **Exercice 2.2.** Corollaire du theoreme du rang en dimension egale : un
endomorphisme injectif de `ℝ²` est surjectif - l'image remplit l'espace. -/
theorem exercice_2_2 : LinearMap.range cisaillement = ⊤ :=
  (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl).mp exercice_2_1

/-!
## Palier 3 - Valeurs propres (Axler ch. 5)

Definitions Mathlib utilisees (`Mathlib.LinearAlgebra.Eigenspace`) :
* `Module.End.HasEigenvector f μ x` - `f x = μ • x` avec `x ≠ 0`
  (via `Module.End.mem_eigenspace_iff`) ;
* `Module.End.HasEigenvalue f μ` - il existe un tel vecteur ;
* `Module.End.hasEigenvalue_iff_isRoot` (`Eigenspace.Minpoly`) - `μ` est valeur
  propre ssi `μ` est racine du polynome minimal ;
* sur un corps algebriquement clos, `Module.End.exists_eigenvalue`
  (`Eigenspace.Triangularizable`) : tout endomorphisme d'un espace non nul de
  dimension finie a une valeur propre.

**Liaison `Lean-12` / `Lean-13`** : la sensibilite d'un reseau se lit sur sa
matrice jacobienne ; les valeurs propres en sont le vocabulaire. Sur `ℂ`,
l'existence est garantie - la raison d'etre des vecteurs complexes dans
`Lean-13`.
-/

/-- La diagonale `diag(2, 3)` sur `ℂ²`. -/
def diag23 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toLpLin 2 2 !![2, 0; 0, 3]

/-- **Exercice 3.1.** `2` est valeur propre de `diag23`, de vecteur propre
`e₀ = single 0 1` : calcul direct, coordonnee par coordonnee. -/
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

/-- Le lien theorique (cite, non recalcule) : les valeurs propres sont
exactement les racines du polynome minimal. -/
theorem exemple_valeurs_propres_minpoly (f : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
    (μ : ℂ) :
    f.HasEigenvalue μ ↔ (minpoly ℂ f).IsRoot μ :=
  Module.End.hasEigenvalue_iff_isRoot

/-- **Exercice 3.2.** Sur `ℂ`, l'existence d'une valeur propre est garantie
pour tout endomorphisme d'un espace non nul de dimension finie - c'est le
theoreme de d'Alembert-Gauss qui travaille. -/
theorem exercice_3_2 (f : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∃ μ, Module.End.HasEigenvalue f μ :=
  Module.End.exists_eigenvalue f

/-!
## Palier 4 - Produit scalaire et orthonormalisation (Axler ch. 6)

Definitions Mathlib utilisees :
* `⟪x, y⟫` (`inner`) - le produit scalaire ; sur `EuclideanSpace`,
  `PiLp.inner_apply` le developpe en somme des produits coordonnee par
  coordonnee (`Mathlib.Analysis.InnerProductSpace.PiL2`) ;
* `Orthonormal` - famille de vecteurs unitaires deux a deux orthogonaux ;
* `gramSchmidtOrthonormalBasis`
  (`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`) - le procede de
  Gram-Schmidt : de toute famille generatrice de cardinal la dimension, on
  extrait une base orthonormee.

**Liaison `Lean-13`** : les etats y sont des vecteurs d'un espace de Hilbert
reel de dimension finie ; l'orthogonalite de deux mesures est un produit
scalaire nul.
-/

/-- Le produit scalaire usuel de `ℝ²`, calcule coordonnee par coordonnee. -/
theorem exemple_produit_scalaire (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **Exercice 4.1.** Deux vecteurs de base distincts sont orthogonaux : le
produit scalaire ne garde que la coordonnee commune - qui n'existe pas. -/
theorem exercice_4_1 {i j : Fin 3} (h : i ≠ j) :
    ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, PiLp.single_apply, h]

/-- **Exercice 4.2.** Les diagonales `(1, 1)` et `(1, -1)` du plan sont
orthogonales - le calcul complet, sans theorie. -/
theorem exercice_4_2 :
    ⟪(EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 :
        EuclideanSpace ℝ (Fin 2)),
      (EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1)⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, PiLp.single_apply, inner_add_left,
    inner_sub_right, Fin.sum_univ_two]

/-- Le procede de Gram-Schmidt (cite) : de toute base d'un espace euclidien de
dimension finie, on extrait une base orthonormee. -/
noncomputable def exemple_gram_schmidt (b : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) b

/-!
## Palier 5 - Operateurs auto-adjoints et theoreme spectral (Axler ch. 7)

Definitions Mathlib utilisees :
* `LinearMap.adjoint` (`Mathlib.Analysis.InnerProductSpace.Adjoint`) -
  l'adjoint `f†`, defini par `⟪f x, y⟫ = ⟪x, f† y⟫` ;
* `LinearMap.IsSymmetric` (`Mathlib.Analysis.InnerProductSpace.Symmetric`) -
  `∀ x y, ⟪f x, y⟫ = ⟪x, f y⟫`, equivalent a `IsSelfAdjoint`
  (`isSymmetric_iff_isSelfAdjoint`) ;
* `LinearMap.IsSymmetric.eigenvectorBasis`
  (`Mathlib.Analysis.InnerProductSpace.Spectrum`) - **le theoreme spectral** :
  un operateur auto-adjoint d'un espace euclidien de dimension finie admet une
  base **orthonormee de vecteurs propres**, a valeurs propres reelles triees.

**Liaison `Lean-13`** : l'operateur de correlation CHSH est auto-adjoint ; son
calcul passe par ses valeurs propres - c'est exactement ce palier.
-/

/-- L'operateur symetrique de matrice `!![2, 1; 1, 2]` sur `ℝ²`. -/
def T_sym : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toLpLin 2 2 !![2, 1; 1, 2]

/-- **Exercice 5.1.** `T_sym` est auto-adjoint : les deux membres de
`⟪T x, y⟫ = ⟪x, T y⟫` se developpent en le meme polynome en les coordonnees -
la symetrie de la matrice, calculee a la main. -/
theorem exercice_5_1 : T_sym.IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fin.sum_univ_two, T_sym, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- **Exercice 5.2.** Le theoreme spectral applique : `T_sym` admet une base
orthonormee de vecteurs propres. Aucune valeur propre n'est calculee ici -
c'est l'existence qui est le resultat d'Axler ch. 7. -/
theorem exercice_5_2 :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      ∃ μ : Fin 2 → ℝ, ∀ i, T_sym (b i) = ((μ i : ℝ) : ℝ) • b i :=
  ⟨exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin,
    fun i => exercice_5_1.eigenvalues finrank_euclideanSpace_fin i,
    fun i => exercice_5_1.apply_eigenvectorBasis finrank_euclideanSpace_fin i⟩

/-- **Exercice 5.3.** Le vecteur `(1, 1)` est vecteur propre de `T_sym` pour
la valeur propre `3` : calcul direct, sans theoreme spectral. -/
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

/-- La diagonalisation (citee) : dans la base orthonormee de vecteurs propres
de l'exercice 5.2, la matrice de `T_sym` est diagonale - c'est la forme
operatorielle du theoreme spectral (`IsSymmetric.toMatrix_eigenvectorBasis`). -/
theorem exemple_diagonalisation :
    T_sym.toMatrix (exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis
        (exercice_5_1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis
      = Matrix.diagonal
          (RCLike.ofReal ∘ exercice_5_1.eigenvalues finrank_euclideanSpace_fin) :=
  exercice_5_1.toMatrix_eigenvectorBasis finrank_euclideanSpace_fin
