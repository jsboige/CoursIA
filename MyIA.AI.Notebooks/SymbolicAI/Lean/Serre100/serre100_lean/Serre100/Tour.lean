import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Algebra.Category.Grp.IsFinite
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Field.ZMod

/-!
# Serre dans Mathlib : tour des cinq monuments

Ce module accompagne le notebook `08-serre-dans-mathlib.ipynb` (série
*Serre 100*, grain 6 de l'EPIC #16334). Jean-Pierre Serre a donné son nom à
cinq constructions distinctes que Mathlib formalise chacune dans un coin
différent de la bibliothèque ; ce tour les visite une à une :

1. **Les classes de Serre** (`Mathlib.CategoryTheory.Abelian.SerreClass.Basic`) :
   une classe d'objets d'une catégorie abélienne stable par sous-objets,
   quotients et extensions — le langage des conditions de finitude de
   *Corps locaux*.
2. **La dérivée de Serre** (`Mathlib.NumberTheory.ModularForms.Derivative`) :
   la dérivation qui préserve les formes modulaires de poids `k + 2`,
   `∂ₖ = D − (k/12)·E₂`.
3. **La construction de Serre** (`Mathlib.Algebra.Lie.SerreConstruction`) :
   l'algèbre de Lie présentée par générateurs `H`, `E`, `F` et relations
   encodant une matrice de Cartan — la porte des algèbres de Kac–Moody.
4. **Le critère de Serre** (`Mathlib.RingTheory.DiscreteValuationRing.Basic`) :
   un anneau intègre est un anneau de valuation discrète si et seulement
   s'il est principal avec un unique idéal premier non nul.
5. **Les anneaux parfaits « au sens de Serre »** (`Mathlib.FieldTheory.Perfect`) :
   Frobenius bijectif en caractéristique `p`, comme dans *Corps locaux*,
   ch. II §3 — distinct de la perfection de Bass.

Chaque station ci-dessous énonce et démontre un fait significatif tiré de
Mathlib, prêt à être exploré interactivement depuis le notebook.
-/

set_option autoImplicit false

noncomputable section

namespace Serre100

/-! ## Station 1 — Les classes de Serre

Une classe de Serre `P` sur une catégorie abélienne `C` contient l'objet
nul et passe aux sous-objets, quotients et extensions. Le critère
« deux-sur-trois » d'une suite exacte courte en est le théorème central.
-/

open CategoryTheory

section SerreClasses

variable {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C)

/-- La propriété universelle `⊤` (tous les objets) est une classe de
Serre : la plus grosse, celle qui ne filtre rien. -/
example : (⊤ : ObjectProperty C).IsSerreClass := inferInstance

/-- La classe des objets isomorphes à zéro est une classe de Serre : la
plus petite, celle qui ne retient que l'objet nul. -/
example {C : Type*} [Category C] [Abelian C] :
    ObjectProperty.IsSerreClass (Limits.IsZero (C := C)) := inferInstance

/-- Les groupes abéliens **finis** forment une classe de Serre de
`AddCommGrp` : c'est l'exemple historique du chapitre I de *Corps locaux*,
et la raison d'être du formalisme. -/
example : AddCommGrpCat.isFinite.IsSerreClass := inferInstance

variable [P.IsSerreClass]

/-- Le critère « deux-sur-trois » : dans une suite exacte courte, le terme
du milieu appartient à la classe si et seulement si les deux extrêmes y
appartiennent. C'est la reformulation de la stabilité par extensions et
des deux demi-stabilités (sous-objets et quotients). -/
theorem member_iff_outer {S : ShortComplex C} (hS : S.ShortExact) :
    P S.X₂ ↔ P S.X₁ ∧ P S.X₃ := P.prop_iff_of_shortExact hS

/-- Version « trois-sur-trois » : une suite exacte (pas nécessairement
courte) dont les extrêmes sont dans la classe y a aussi son terme du
milieu. -/
theorem member_of_exact {S : ShortComplex C} (hS : S.Exact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ := P.prop_X₂_of_exact hS h₁ h₃

end SerreClasses

/-! ## Station 2 — La dérivée de Serre

Sur le demi-plan supérieur `ℍ`, la dérivée de Serre de poids `k` corrige
la dérivée normalisée `D` par le terme en `E₂` :

`∂ₖ F(z) = D F(z) − (k/12) · E₂(z) · F(z)`

de sorte que `∂ₖ` envoie les formes modulaires de poids `k` sur celles de
poids `k + 2` (le notebook explore la variance sous `SL(2, ℤ)` ; ici nous
fixons les identités algébriques).
-/

open Derivative
open UpperHalfPlane
open scoped Manifold ModularForm

section SerreDerivative

/-- La formule définitoire, réexposée : la dérivée de Serre est la
dérivée normalisée corrigée du terme en `E₂`, avec la normalisation
`k/12`. -/
example (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serreDerivative k F z =
      normalizedDerivOfComplex F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/-- Additivité : la dérivée de Serre est additive en la fonction, à poids
fixé. -/
example (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F + G) = serreDerivative k F + serreDerivative k G :=
  serreDerivative_add k F G hF hG

/-- Règle de Leibniz **pondérée** : sur un produit, les poids s'ajoutent et
chaque facteur est dérivé avec son propre poids — la signature même d'une
dérivation graduée. -/
example (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative (k₁ + k₂) (F * G) =
      serreDerivative k₁ F * G + F * serreDerivative k₂ G :=
  serreDerivative_mul k₁ k₂ F G hF hG

/-- La dérivée de Serre préserve la différentiabilité : `∂ₖ` n'engendre
pas de singularité nouvelle. -/
example (k : ℂ) {F : ℍ → ℂ} (hF : MDiff F) :
    MDiff (serreDerivative k F) :=
  serreDerivative_mdifferentiable k hF

end SerreDerivative

/-! ## Station 3 — La construction de Serre

Étant donnée une matrice de Cartan généralisée `CM : Matrix B B ℤ`,
l'algèbre de Lie « de Serre » est le quotient de l'algèbre de Lie libre
sur les générateurs `H i`, `E i`, `F i` (`i : B`) par l'idéal des
**relations de Serre** : commutation des `H`, crochet `⁅E i, F j⁆`
diagonal, action des `H` sur les `E` et `F` pondérée par `CM`, et
nilpotence d'ordre `1 − CM i j` des `ad E i`, `ad F i`.
-/

section SerreConstruction

/-- La matrice de Cartan de type **A₂** : le système de racines de rang 2
le plus simple, celui de `sl₃`. -/
def cartanA2 : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]

/-- Les générateurs de la construction : une famille `H` (cartan), une
famille `E` (positifs), une famille `F` (négatifs), indicées par `B`. -/
example (i : Fin 2) : CartanMatrix.Generators (Fin 2) := .H i

/-- L'idéal des relations de Serre de `A₂` vit dans l'algèbre de Lie
libre sur les générateurs — c'est lui que l'on quotientte pour obtenir
l'algèbre de Serre `sl₃`. -/
example (R : Type*) [CommRing R] :
    LieIdeal R (FreeLieAlgebra R (CartanMatrix.Generators (Fin 2))) :=
  CartanMatrix.Relations.toIdeal R cartanA2

end SerreConstruction

/-! ## Station 4 — Le critère de Serre pour les anneaux de valuation discrète

*Corps locaux*, ch. I §2, prop. 2 : un anneau de valuation discrète est
exactement un anneau principal **possédant un unique idéal premier non
nul**. Mathlib l'énonce pour les anneaux intègres commutatifs.
-/

section DVRCriterion

/-- Le critère de Serre : `R` est un anneau de valuation discrète si et
seulement si `R` est principal et a exactement un idéal premier non nul
(l'idéal maximal). Le « ∃! » capture l'unicité. -/
example (R : Type*) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
  IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R

end DVRCriterion

/-! ## Station 5 — Les anneaux parfaits « au sens de Serre »

*Corps locaux*, ch. II §3 : un anneau de caractéristique `p` est parfait
lorsque l'endomorphisme de Frobenius `x ↦ x ^ p` est bijectif. Mathlib
nomme cela `PerfectRing` et précise dans sa docstring qu'il s'agit du sens
de Serre — à ne pas confondre avec la perfection de Bass.
-/

section PerfectInTheSenseOfSerre

/-- `ZMod 2` est parfait au sens de Serre, exposant `2` : Frobenius
`x ↦ x²` est bijectif sur le corps à deux éléments. -/
example : PerfectRing (ZMod 2) 2 := inferInstance

/-- Tout corps fini `ZMod p` hérite de la même perfection — anneau fini
réduit de caractéristique `p`. (Les instances `Fact` littérales n'existent
que pour 2 et 3 : on les fournit à la main pour les autres premiers.) -/
example : PerfectRing (ZMod 5) 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact inferInstance

/-- Un anneau fini réduit de caractéristique `2` est parfait au sens de
Serre : la surjectivité du Frobenius est gratuite (cardinal fini +
injectivité), et l'injectivité vient de la réduction. -/
example (R : Type*) [CommRing R] [ExpChar R 2] [Finite R] [IsReduced R] :
    PerfectRing R 2 := inferInstance

/- Le pont de Serre exige `Field (ZMod 7)` dès l'élaboration de
l'énoncé : le `Fact` littéral doit donc être enregistré AVANT, au niveau
du fichier (les instances littérales n'existent que pour 2 et 3). -/
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Le pont de Serre : un **corps** parfait au sens de Serre est un corps
parfait au sens des polynômes (tout irréductible est séparable). -/
example : PerfectField (ZMod 7) := PerfectRing.toPerfectField (ZMod 7) 7

end PerfectInTheSenseOfSerre

end Serre100
