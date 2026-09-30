import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic

/-!
# Lemme de Yoneda calculé : l'évaluation est une bijection, prouvée par le noyau

Pendant kernel du notebook `04-lemme-yoneda-categories-finies.ipynb` (série
*Serre 100*, EPIC #16334 — voie de graduation « pendants kernel »). Le
notebook *énumère* les transformations naturelles des catégories finies en
Python et *mesure* la bijection ; ce module la *démontre* pour toute
catégorie, et fait vérifier par le noyau les tables du notebook sur les
instances concrètes.

Plan, en miroir du notebook :

1. **Une catégorie finie** : Sierpinski et `cercle4` (deux minimaux `a1`,
   `a3`, deux maximaux `a2`, `a4`) comme préordres — la construction
   `cat_poset` du notebook, côté Lean.
2. **Le lemme : l'évaluation est une bijection** : le couple
   évaluation/inverse du notebook (`alpha ↦ alpha_X(id_X)` et
   `x ↦ (f ↦ F(f)(x))`) EST `coyonedaEquiv` dans Mathlib — les deux
   round-trips sont des théorèmes, pas des mesures.
3. **Plein et fidèle** : `Nat(h_X, h_Y) ≃ Hom(Y, X)` —
   `Coyoneda.fullyFaithful`, et la matrice 4×4 de `cercle4` vérifiée par
   le noyau, entrée par entrée.
4. **Le pont Čech** : `h_x = U_x` — sur un préordre, le représentable
   covariant lit exactement l'ouvert supérieur `U x = {y | x ≤ y}` du
   notebook 03.
5. **Exercices** : le foncteur constant (`Nat(h_X, cst_E) ≃ E`, card 3
   mesuré et prouvé sur Sierpinski), la fidélité calculée, et le
   monoïde `ℤ/3` (`|Nat(h_*, h_*)| = 3`, kernel).

Remarque de vocabulaire : le notebook travaille en foncteurs *covariants*
`C → Ens` avec `h_X(y) = Hom(X, y)` — côté Mathlib c'est `coyoneda`
(`Cᵒᵖ ⥤ C ⥤ Type`) ; le côté préfaisceaux `yoneda` est le miroir dual.
-/

set_option autoImplicit false

namespace Serre100

open CategoryTheory Opposite

/-! ## 1. Une catégorie finie

Deux préordres finis, la construction `cat_poset` du notebook : un
ensemble ordonné est une catégorie mince (au plus une flèche par paire),
`x ⟶ y` est la preuve de `x ≤ y`. Sierpinski (deux éléments, `a ≤ b`)
est le témoin minimal ; `cercle4` est la catégorie des cellules 14-16 du
notebook : deux minimaux `a1`, `a3` sous deux maximaux `a2`, `a4`.
-/

/-- Le préordre de Sierpinski : deux éléments, `a ≤ b` (notebook,
`sierpinski`). -/
inductive Sierpinski : Type where
  | a : Sierpinski
  | b : Sierpinski
  deriving DecidableEq

instance : LE Sierpinski := ⟨fun x y => x = .a ∨ x = y⟩

instance : DecidableLE Sierpinski := fun x y =>
  decidable_of_iff (x = Sierpinski.a ∨ x = y) Iff.rfl

instance : Preorder Sierpinski where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases x <;> rcases y <;> rcases z <;> tauto

/-- La catégorie `cercle4` du notebook : deux minimaux `a1`, `a3`, deux
maximaux `a2`, `a4` — `a1, a3 ≤ a2, a4` (notebook, cellule 14). -/
inductive Cercle4 : Type where
  | a1 : Cercle4
  | a2 : Cercle4
  | a3 : Cercle4
  | a4 : Cercle4
  deriving DecidableEq

instance : LE Cercle4 :=
  ⟨fun x y => (x = .a1 ∨ x = .a3) ∧ (y = .a2 ∨ y = .a4) ∨ x = y⟩

instance : DecidableLE Cercle4 := fun x y =>
  decidable_of_iff ((x = Cercle4.a1 ∨ x = Cercle4.a3) ∧
    (y = Cercle4.a2 ∨ y = Cercle4.a4) ∨ x = y) Iff.rfl

instance : Preorder Cercle4 where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases x <;> rcases y <;> rcases z <;> tauto

-- Les instances de catégorie arrivent de `Preorder.smallCategory` :
-- `Hom x y := ULift (PLift (x ≤ y))`, mince par `subsingleton_hom`.

/-! ## 2. Le lemme : l'évaluation est une bijection, calculée

Le couple du notebook — évaluation `α ↦ α_X(id_X)` et inverse
`x ↦ (f ↦ F(f)(x))` — est exactement `coyonedaEquiv` : le round-trip
que le notebook mesure par énumération exhaustive est un théorème de
Mathlib, et le calcul de l'inverse sur une flèche est `rfl`.
-/

section Lemme

variable {C : Type} [SmallCategory C]

/-- Le `h_X` du notebook : le représentable covariant `Hom(X, ·)`.
Il EST `coyoneda.obj (op X)`, composante par composante. -/
theorem hX_app (X : C) (Y : C) :
    (coyoneda.obj (op X)).obj Y = (X ⟶ Y) :=
  rfl

/-- **L'évaluation du notebook est `coyonedaEquiv`** : la composante en
`X` du domaine, sur l'identité, puis la bijection (notebook §4,
`evaluation` + vérification « bijectif/round-trip/inverse naturel »). -/
theorem evaluation_eq (X : C) (F : C ⥤ Type) (α : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv α = α.app X (𝟙 X) :=
  rfl

/-- **L'inverse du notebook, sur une flèche** : la composante en `Y` de
`yoneda_inverse x` appliquée à `f : X ⟶ Y` est `F.map f x` — calculé
par le noyau, sans énumération (notebook §4, `yoneda_inverse`). -/
theorem inverse_app (X : C) (F : C ⥤ Type) (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

/-- Le premier round-trip du notebook : évaluer l'image inverse redonne
la transformation de départ — pour toute catégorie, pas seulement les
finies (notebook, `round-trip`). -/
theorem round_trip_domain (X : C) (F : C ⥤ Type)
    (α : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv.symm (coyonedaEquiv α) = α :=
  coyonedaEquiv.symm_apply_apply α

/-- Le second round-trip : l'inverse appliqué à l'évaluation redonne
l'élément (notebook, `inverse naturel`). -/
theorem round_trip_codomain (X : C) (F : C ⥤ Type) (x : F.obj X) :
    coyonedaEquiv (coyonedaEquiv.symm x) = x :=
  coyonedaEquiv.apply_symm_apply x

end Lemme

/-! ## 3. Plein et fidèle : `Nat(h_X, h_Y) ≃ Hom(Y, X)`

La pleinement-fidélité de `coyoneda` donne la bijection de la section 5
du notebook ; sur une catégorie mince, chaque hom est un 0-ou-1, et la
matrice de `cercle4` se vérifie par le noyau, entrée par entrée.
-/

section PleinFidele

variable {C : Type} [SmallCategory C]

/-- **Plein et fidèle** (notebook §5) : les transformations naturelles
entre représentables sont exactement les flèches. C'est le lemme de la
section 2 une fois de plus, instancié à `F = h_Y` — le codomaine est
`h_Y(X) = (Y ⟶ X)` par `hX_app`. C'est la lecture calculatoire de
`Coyoneda.fullyFaithful`. -/
def natEquiv (X Y : C) :
    (coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) ≃ (Y ⟶ X) :=
  coyonedaEquiv

/-- La flèche se lit sur sa transformation : évaluer au point `id_X`
(notebook §5, fidélité calculée ; Mathlib, `fullyFaithful_preimage`). -/
theorem natEquiv_apply (X Y : C) (α : coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) :
    natEquiv X Y α = α.app X (𝟙 X) :=
  rfl

/-- Le cardinal d'un hom d'un préordre : 1 si `x ≤ y`, 0 sinon — la
matrice du notebook, côté noyau. -/
def homCard {α : Type} [Preorder α] [DecidableLE α] (x y : α) : ℕ :=
  if x ≤ y then 1 else 0

/-- La matrice de `cercle4` (notebook, cellule 14), lignes non triviales :
`|Hom(a1, ·)|` et `|Hom(a3, ·)|` — les deux zéros `a1 → a3` et `a3 → a1`
sont les entrées non triviales ; les lignes des maximaux `a2`, `a4` ne
portent que l'identité. -/
example : ∀ y : Cercle4, homCard Cercle4.a1 y =
    (match y with | .a1 => 1 | .a2 => 1 | .a3 => 0 | .a4 => 1) := by
  intro y
  rcases y <;> decide

example : ∀ y : Cercle4, homCard Cercle4.a3 y =
    (match y with | .a1 => 0 | .a2 => 1 | .a3 => 1 | .a4 => 1) := by
  intro y
  rcases y <;> decide

example : ∀ y : Cercle4, homCard Cercle4.a2 y =
    (match y with | .a1 => 0 | .a2 => 1 | .a3 => 0 | .a4 => 0)
    ∧ homCard Cercle4.a4 y =
      (match y with | .a1 => 0 | .a2 => 0 | .a3 => 0 | .a4 => 1) := by
  intro y
  rcases y <;> decide

/-- **La colonne Yoneda de la matrice** : le cardinal de
`Nat(h_X, h_Y)` est le cardinal de `Hom(Y, X)` — la ligne du notebook
« accord = True » sur toute la matrice, pour toute catégorie aux homs
finis. -/
theorem card_nat_eq_homCard {α : Type} [Preorder α] (X Y : α) :
    Nat.card (coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) = Nat.card (Y ⟶ X) :=
  Nat.card_congr (natEquiv X Y)

end PleinFidele

/-! ## 4. Le pont Čech : `h_x = U_x`

Sur un préordre, le représentable covariant `h_x(y) = Hom(x, y)` lit
exactement l'appartenance à l'ouvert supérieur `U x = {y | x ≤ y}` —
la table d'incidence du notebook 03 (cohomologie Čech), où la
préfaisceau-des-ouverts et le représentable coïncident.
-/

section PontCech

variable {α : Type} [Preorder α]

/-- L'ouvert supérieur de `x` : le `U_x` du notebook 03. -/
def ouverture (x : α) : Set α := {y | x ≤ y}

/-- **`h_x = U_x`** : avoir une flèche `x ⟶ y`, c'est appartenir à
l'ouvert `U x` — le pont Čech du notebook §6, une entrée de la table
d'incidence par paire d'objets. -/
theorem pont_cech (x y : α) : Nonempty (x ⟶ y) ↔ y ∈ ouverture x := by
  constructor
  · intro ⟨f⟩
    exact leOfHom f
  · intro h
    exact ⟨homOfLE h⟩

end PontCech

/-! ## 5. Exercices — les trois du notebook, côté noyau

1. Le foncteur constant : `Nat(h_X, cst_E) ≃ E` — le card 3 de Sierpinski,
   prouvé.
2. La fidélité calculée : `coyoneda.map` est injective (exercice 2).
3. Le monoïde `ℤ/3` : `|Nat(h_*, h_*)| = 3` (exercice 3), et le
   `ℤ/2`-ensemble à deux points de la cellule 11.
-/

section Exercices

/-- Le foncteur constant d'un notebook : tout objet voit `E`, toute
flèche voit l'identité (`const C E`, cellule 8). -/
def foncteurConstant (C) [SmallCategory C] (E : Type) : C ⥤ Type where
  obj _ := E
  map _ := 𝟙 E
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Exercice 1** : transformations du représentable vers le foncteur
constant `E` = éléments de `E` — l'instance `F = cst` du lemme, card
mesuré 3 sur Sierpinski dans le notebook. -/
def nat_const (C : Type) [SmallCategory C] (X : C) (E : Type) :
    (coyoneda.obj (op X) ⟶ foncteurConstant C E) ≃ E :=
  coyonedaEquiv (X := X) (F := foncteurConstant C E)

/-- Exercice 1, kernel : sur Sierpinski avec `E = Fin 3`, le compte du
notebook (`3`), prouvé par le noyau. -/
example : Nat.card
    (coyoneda.obj (op Sierpinski.a) ⟶ foncteurConstant Sierpinski (Fin 3)) = 3 := by
  rw [Nat.card_congr (nat_const Sierpinski Sierpinski.a (Fin 3))]
  rw [Nat.card_eq_fintype_card]
  decide

/-- **Exercice 2** : la fidélité calculée — chaque flèche donne une
transformation (par précomposition via l'évaluation), et deux flèches
de même transformation sont égales (notebook, « chaque flèche EST une
transformation »). -/
theorem fidelite (C : Type) [SmallCategory C] (X Y : C) :
    Function.Injective (natEquiv X Y) :=
  (natEquiv X Y).injective

/-- **Exercice 3** : le monoïde `ℤ/3` (additif — transporté en
multiplicatif par `Multiplicative`) vu comme catégorie à un objet —
`|Nat(h_*, h_*)| = |ℤ/3| = 3`, kernel (notebook, cellule 23). -/
example : Nat.card
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 3)))) ⟶
     coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 3))))) = 3 := by
  rw [Nat.card_congr
    (natEquiv (SingleObj.star (M := Multiplicative (ZMod 3)))
      (SingleObj.star (M := Multiplicative (ZMod 3))))]
  rw [Nat.card_eq_fintype_card]
  decide

/-- Le `ℤ/2`-ensemble à deux points de la cellule 11 du notebook :
`F_z2 = {p, q}` avec `t = (p q)` — ici le `ℤ/2`-ensemble régulier
(`ZMod 2` agissant sur lui-même par translation), qui est ce swap :
`t` échange les deux éléments, `t ∘ t = id`. -/
def z2ensemble : SingleObj (Multiplicative (ZMod 2)) ⥤ Type where
  obj _ := ZMod 2
  map f := TypeCat.ofHom (fun x : ZMod 2 => x + Multiplicative.toAdd f)
  map_id := by
    intro X
    apply ConcreteCategory.hom_ext
    intro x
    show x + (0 : ZMod 2) = x
    ring
  map_comp := by
    intro X Y Z f g
    apply ConcreteCategory.hom_ext
    intro x
    show x + (Multiplicative.toAdd g + Multiplicative.toAdd f : ZMod 2)
      = x + Multiplicative.toAdd f + Multiplicative.toAdd g
    ring

section Z2

-- La finitude du type de transformations est héritée du lemme : c'est
-- `F_z2(*) = ℤ/2`, fini. Instance locale, pour l'énoncé ci-dessous.
local instance : Fintype
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 2)))) ⟶ z2ensemble) :=
  Fintype.ofEquiv (ZMod 2) (coyonedaEquiv
    (X := SingleObj.star (M := Multiplicative (ZMod 2))) (F := z2ensemble)).symm

/-- La cellule 11 du notebook, côté noyau : sur le groupe `ℤ/2` (un
objet), `|Nat(h_*, F_z2)| = |F_z2(*)| = 2` — le lemme au travail sur un
cas non-poset. -/
example : Nat.card
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 2)))) ⟶ z2ensemble)
      = 2 := by
  rw [Nat.card_congr (coyonedaEquiv
    (X := SingleObj.star (M := Multiplicative (ZMod 2))) (F := z2ensemble))]
  show Nat.card (ZMod 2) = 2
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card 2

end Z2

end Exercices

end Serre100
