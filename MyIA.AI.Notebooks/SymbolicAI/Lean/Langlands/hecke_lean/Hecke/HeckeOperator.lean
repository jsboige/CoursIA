import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Opérateurs de Hecke classiques sur le demi-plan supérieur

Ce module introduit les opérateurs de Hecke « classiques » : pour un entier
`p` (usuellement premier), l'opérateur `T_p` agit sur une fonction `f` du
demi-plan supérieur ℍ par une somme finie d'actions de slash sur des
représentants explicites des classes `Γ(1) \ M₂(ℤ)` de déterminant `p`,
et l'opérateur `U_p` n'en retient que la partie triangulaire. La formule
induite sur les coefficients de Fourier — `a(np) + p^{k-1} a(n/p)` selon
que `p` divise `n` ou non — est formalisée par `coeffHeckeT`.

**Adaptation pédagogique** : ce fichier est un port du dépôt
`anthropics/fermats-last-theorem` (fichier `Definitions/Def_ModularForm_HeckeOperator.lean`,
commit `aa2d8b34692b`), avec docstrings pédagogiques en français et exemples
calculables ajoutés (section `Examples` en fin de module). Les preuves et
énoncés sont repris tels quels ; la licence Apache-2.0 est préservée (voir
`NOTICE.md`).

Le produit de Petersson et les cusp forms sont hors du périmètre de cette
première tranche (grain aval).
-/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm

/-- La matrice triangulaire supérieure `!![a, b; 0, d]` vue comme élément de
`GL (Fin 2) ℝ`, sous l'hypothèse `a * d ≠ 0` qui garantit l'inversibilité
(le déterminant vaut alors `a * d ≠ 0`). C'est la brique de construction des
représentants de Hecke. -/
def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

/-- Le représentant `γ_{p,j} = !![1, j; 0, p]` : la famille
`heckeMatrix p 0, …, heckeMatrix p (p-1)` décrit les classes à gauche de
`Γ(1)` dans les matrices entières de déterminant `p` dont la réduction
modulo `p` est triangulaire supérieure (partie « U » de l'opérateur `T_p`).
Le cas dégénéré `p = 0` est neutralisé en renvoyant l'identité. -/
def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

/-- Le représentant diagonal `!![p, 0; 0, 1]` de déterminant `p` : c'est la
classe « diagonale » qui complète `U_p` en `T_p` (terme `f ∣[k] heckeDiagMatrix p`
de `heckeT`). -/
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

/-- Le déterminant du représentant `γ_{p,j}` vaut exactement `p`. -/
theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

/-- Le déterminant du représentant diagonal vaut exactement `p`. -/
theorem det_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) : ((heckeDiagMatrix p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hp, Matrix.det_fin_two_of]
  ring

/-- Le déterminant de `γ_{p,j}` est positif (y compris dans le cas dégénéré
`p = 0`, où la matrice est l'identité) : les représentants de Hecke
préservent le demi-plan supérieur. -/
theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

/-- Version diagonale de `det_heckeMatrix_pos`. -/
theorem det_heckeDiagMatrix_pos (p : ℕ) : 0 < ((heckeDiagMatrix p).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeDiagMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

/-- Le dénominateur de l'action de `γ_{p,j}` sur `τ` vaut `p` : c'est ce
facteur `1/p` qui apparaîtra devant la somme dans `heckeU_apply`. -/
theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

/-- Le dénominateur du représentant diagonal vaut `1` : son action ne
contribute aucun facteur `1/p`. -/
theorem denom_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeDiagMatrix p) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hp]

/-- L'action de `γ_{p,j}` sur `τ ∈ ℍ` est l'homothétie-translations
`(τ + j) / p` : les `p` représentants « U » découpent le voisinage de la
pointe en `p` translatées écrasées par `1/p`. -/
theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

/-- L'action du représentant diagonal est la dilatation `p • τ`. -/
theorem coe_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hp]

/-- Le caractère `σ` des représentants de Hecke est trivial : ils agissent
sans conjugaison supplémentaire (déterminant positif). -/
theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeMatrix_pos p j)]

/-- Version diagonale de `σ_heckeMatrix`. -/
theorem σ_heckeDiagMatrix (p : ℕ) : UpperHalfPlane.σ (heckeDiagMatrix p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeDiagMatrix_pos p)]

/-- Le slash par `γ_{p,j}` : `(f ∣[k] γ_{p,j}) τ = p⁻¹ • f (γ_{p,j} • τ)`.
C'est la lecture explicite de l'action de slash sur un représentant « U ». -/
theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

/-- Le slash par le représentant diagonal porte la puissance `p^(k-1)`
caractéristique du poids `k`. -/
theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hp, denom_heckeDiagMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast, one_zpow, mul_one]
  rw [mul_comm]

/-- L'opérateur `U_p` : somme des slashs par les `p` représentants
triangulaires `γ_{p,j}`, `j = 0, …, p-1`. -/
def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

/-- L'opérateur de Hecke `T_p = U_p + f ∣[k] (diagonal)` : la définition
classique sur les représentants explicites de `Γ(1)`. -/
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

/-- Cas dégénéré `p = 0` : `T_0` est l'identité. -/
@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

/-- Lecture ponctuelle de `U_p` : moyenne (au facteur `p⁻¹` près) des
valeurs de `f` sur les `p` translatées `(τ + j)/p`. -/
theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

/-- Lecture ponctuelle de `T_p` : somme de la partie `U_p` et du terme
diagonal `p^(k-1) • f (p • τ)`. -/
theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

/-- Linéarité de `U_p` en l'argument : `U_p (f + g) = U_p f + U_p g`. -/
theorem heckeU_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

/-- Linéarité de `T_p` en l'argument. -/
theorem heckeT_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

/-- Homogénéité de `U_p` : `U_p (c • f) = c • U_p f`. -/
theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply,
    Finset.smul_sum]

/-- Homogénéité de `T_p`. -/
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

/-- La formule des coefficients de Hecke : si `f = ∑ a n q^n`, alors
`T_p f = ∑ (coeffHeckeT k p a n) q^n` avec
`coeffHeckeT k p a n = a (n p) + p^(k-1) a (n/p)` quand `p ∣ n`
(le second terme disparaît sinon). C'est la transcription combinatoire de
l'action géométrique de `T_p` sur les coefficients de Fourier. -/
def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

/-- La formule des coefficients de la partie `U_p` : un simple
« échantillonnage » `a (n p)` de la suite. -/
def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

/-- Lecture de `coeffHeckeT` dans le cas `p ∣ n` : les deux contributions
coexistent. -/
theorem coeffHeckeT_of_dvd (k : ℤ) {p n : ℕ} (h : p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) + (p : ℂ) ^ (k - 1) * a (n / p) := by
  rw [coeffHeckeT, if_pos h]

/-- Lecture de `coeffHeckeT` dans le cas `p ∤ n` : seul subsiste le terme
d'échantillonnage `a (n p)`. -/
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
## Exemples calculables

Ces exemples (absents du fichier amont) relient l'opérateur à la lecture
concrète des coefficients : pour la suite `a n = n` et le poids `k = 12`
(celui de la forme modulaire discriminant Δ), on lit directement la
formule `a (n p) + p^(k-1) a (n/p)` selon la divisibilité de `n` par `p`.
-/

/-- `T_0` est l'identité, y compris sur les fonctions. -/
example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by simp

/-- `U_p` échantillonne : `coeffHeckeU 2 a 3 = a 6`, sans aucun facteur. -/
example : coeffHeckeU 2 (fun n => (n : ℂ)) 3 = 6 := rfl

/-- `2 ∤ 1` : seul le terme d'échantillonnage subsiste, `coeffHeckeT = a 2 = 2`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 1 = 2 := by
  have h : ¬ (2 : ℕ) ∣ 1 := by decide
  simp only [coeffHeckeT, if_neg h]
  norm_num

/-- `2 ∣ 2` : les deux termes coexistent, `a 4 + 2¹¹ • a 1 = 4 + 2¹¹`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 2 = 4 + 2 ^ 11 := by
  have h : (2 : ℕ) ∣ 2 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

/-- `2 ∤ 3` : à nouveau le seul échantillonnage, `a 6 = 6`. -/
example : coeffHeckeT 12 2 (fun n => (n : ℂ)) 3 = 6 := by
  have h : ¬ (2 : ℕ) ∣ 3 := by decide
  simp only [coeffHeckeT, if_neg h]
  norm_num

/-- Même lecture pour `p = 3` : `3 ∣ 3` donne `a 9 + 3¹¹ • a 1 = 9 + 3¹¹`. -/
example : coeffHeckeT 12 3 (fun n => (n : ℂ)) 3 = 9 + 3 ^ 11 := by
  have h : (3 : ℕ) ∣ 3 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

/-- Un coefficient d'indice nul donne accès à `a 0` : la valeur propre du
terme constant sous `T_p` est `1 + p^(k-1)` (pour `a ≡ 1`). -/
example : coeffHeckeT 12 2 (fun _ => (1 : ℂ)) 2 = 1 + 2 ^ 11 := by
  have h : (2 : ℕ) ∣ 2 := by decide
  simp only [coeffHeckeT, if_pos h]
  norm_num

end ModularForm

end
