/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Module nouveau (grain G7 de #14366, McCoy et al. arXiv:2608.29530) :
algebre TPR bornee — binding/unbinding, identite de constituent surgery,
hypothese de projection affine et hypothese d'approximation.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Representations par produit tensoriel (TPR) — algebre bornee

Ce fichier formalise le modele TPR de Smolensky tel qu'utilise par McCoy,
Soulos, Linzen et Smolensky (arXiv:2608.29530) :

* un **binding** lie un filler a un role par produit tensoriel (`tprBind`) ;
* une **superposition** somme les bindings (`tprSuperpos`) ;
* l'**unbinding** relit un filler par multiplication par le vecteur de role
  (`tprUnbind`) — exact sous independance (orthonormalite) des roles ;
* la **constituent surgery** remplace le binding d'un constituant et relit :
  l'identite algebrique est `tprSurgery` ;
* l'**hypothese de projection affine** formalise le decodeur affine
  (`tprReadout`) et la correction de chirurgie (`tprSurgery_readout`) ;
* l'**hypothese d'approximation** (`TprApproxEntrywise`) borne l'erreur de
  lecture quand l'etat reel n'est qu'approximativement une superposition TPR
  (`tprUnbind_approx`).

## Frontiere epistemique (G7, #14366)

Ces definitions et theoremes portent sur le MODELE ALGEBRIQUE TPR uniquement.
L'assertion empirique « GPT-OSS utilise ces roles » N'EST PAS formalisee ici :
dans les termes de McCoy et al., la structure symbolique emergerait comme
APPROCHEE. `TprApproxEntrywise` et `tprReadout` sont des HYPOTHESES qu'un
reseau satisferait ou non — jamais des conclusions sur un reseau particulier.

Convention i18n #4980 (sibling pair) : ce fichier est le canonique FR ; le
jumeau anglais est `Sensitivity/TensorProductRepresentation_en.lean`
(namespace `Sensitivity_en.TPR`), enonces et preuves byte-identiques.
-/

namespace Sensitivity.TPR

open Matrix

/-! ### Definitions du modele -/

variable {p q k m : ℕ}

/-- **Binding** : produit tensoriel filler ⊗ role — la matrice `p × q`
d'entrees `f i * r j`. -/
def tprBind (f : Fin p → ℝ) (r : Fin q → ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  Matrix.of fun i j => f i * r j

/-- **Superposition** : somme des bindings role-filler — l'etat TPR. -/
def tprSuperpos (fs : Fin m → (Fin p → ℝ)) (rs : Fin m → (Fin q → ℝ)) :
    Matrix (Fin p) (Fin q) ℝ :=
  ∑ i, tprBind (fs i) (rs i)

/-- **Unbinding** : lecture du filler au role `r` par produit
matrice-vecteur. -/
def tprUnbind (T : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) : Fin p → ℝ :=
  T *ᵥ r

/-- **Independance des roles** : famille orthonormale au sens du produit
scalaire canonique — `rs i ⬝ᵥ rs j = δᵢⱼ`. C'est l'hypothese sous laquelle
l'unbinding est EXACT. -/
def RoleFamily (rs : Fin m → (Fin q → ℝ)) : Prop :=
  ∀ i j, rs i ⬝ᵥ rs j = if i = j then 1 else 0

/-- **Hypothese de projection affine** : le decodeur lit un role de l'etat
puis applique une carte affine `A · + b` (`tprReadout`). Le decodeur des
reseaux etudies est suppose affine — hypothese, pas un theoreme. -/
def tprReadout (A : Matrix (Fin k) (Fin p) ℝ) (b : Fin k → ℝ)
    (T : Matrix (Fin p) (Fin q) ℝ) (r : Fin q → ℝ) : Fin k → ℝ :=
  A *ᵥ (tprUnbind T r) + b

/-- **Hypothese d'approximation** : l'etat reel `S` est proche, entree par
entree, d'une superposition TPR `T` a `ε` pres. Hypothese explicite —
l'exactitude TPR d'un reseau reel n'est ni affirmee ni demontrable ici. -/
def TprApproxEntrywise (S T : Matrix (Fin p) (Fin q) ℝ) (ε : ℝ) : Prop :=
  ∀ i j, |S i j - T i j| ≤ ε

/-! ### Lemmes d'entree : l'unbinding est lineaire et se calcule sur un binding -/

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

/-! ### Theoreme 1 : unbinding exact sous independance des roles -/

/-- **Unbinding exact** : sous independance (orthonormalite) des roles, la
lecture de la superposition au role `rs j` rend EXACTEMENT le filler `fs j` —
les autres constituants s'annulent (`rs i ⬝ᵥ rs j = 0` pour `i ≠ j`). -/
theorem tprUnbind_superpos {fs : Fin m → (Fin p → ℝ)} {rs : Fin m → (Fin q → ℝ)}
    (h : RoleFamily rs) (j : Fin m) :
    tprUnbind (tprSuperpos fs rs) (rs j) = fs j := by
  unfold RoleFamily at h
  rw [tprSuperpos, tprUnbind_sum]
  funext κ
  simp only [tprUnbind_bind, h]
  simp

/-! ### Theoreme 2 : identite algebrique de la constituent surgery -/

/-- **Constituent surgery** (McCoy et al., §interventions) : remplacer dans
l'etat le binding du constituant `j` par celui d'un nouveau filler `f'`, puis
relire au role `rs j`, rend exactement `f'` — les autres constituants ne
contribuent pas. C'est l'identite algebrique du modele TPR ; ce qu'un reseau
reel approche est une question EMPIRIQUE, hors scope. -/
theorem tprSurgery {fs : Fin m → (Fin p → ℝ)} {rs : Fin m → (Fin q → ℝ)}
    (h : RoleFamily rs) (j : Fin m) (f' : Fin p → ℝ) :
    tprUnbind (tprSuperpos fs rs - tprBind (fs j) (rs j) + tprBind f' (rs j)) (rs j)
      = f' := by
  rw [tprUnbind_add, tprUnbind_sub, tprUnbind_superpos h, tprUnbind_bind]
  funext κ
  simp [h j j]

/-! ### Theoreme 3 : projection affine et chirurgie -/

/-- **Chirurgie vue par le decodeur affine** : sous les hypotheses du modele
(independance des roles, decodeur affine), la sortie de l'etat chirurge
differe de la sortie originale par `A *ᵥ (f' - fs j)` — un terme qui ne
depend QUE du constituant remplace, pas des autres. C'est la forme algebrique
de « la chirurgie d'un constituant change la lecture de ce constituant et
d'aucun autre » dans le modele TPR. -/
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

/-! ### Theoreme 4 : stabilite de la lecture sous approximation -/

/-- **Lecture approximee** : si l'etat reel `S` est proche d'une superposition
TPR `T` a `ε` par entree, la lecture au role `r` est proche du filler ideal a
`ε * ∑ |r|` pres — l'erreur de lecture est bornee par l'erreur d'etat
ponderee par la masse du role. Ce theoreme rend l'hypothese d'approximation
operationnelle : il quantifie CE QUE L'ON PEUT CONCLURE si un reseau
satisfait `TprApproxEntrywise` (et rien sinon). -/
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

end Sensitivity.TPR
