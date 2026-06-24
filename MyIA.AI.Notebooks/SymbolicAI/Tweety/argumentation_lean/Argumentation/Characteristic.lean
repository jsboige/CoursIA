import Mathlib
import Argumentation.Basic

/-!
# Fonction caractéristique de Dung — morphisme d'ordre sur `Set α`

Le cœur de la théorie de l'argumentation de Dung est la **fonction
caractéristique** `F(S) = { a | S défend a }`. Sa propriété fondamentale est la
**monotonie** : `S ⊆ T ⇒ F(S) ⊆ F(T)` (avoir plus de défenseurs ne peut qu'élargir
l'ensemble des arguments défendus). Cette monotonie en fait un morphisme d'ordre
`Set α →o Set α` ; sur le treillis complet `(Set α, ⊆)`, le théorème de
**Knaster–Tarski** (Mathlib `OrderHom.lfp`) garantit l'existence d'un plus petit
point fixe — l'extension **grounded**.

Mathlib fournit `OrderHom.lfp`, `map_lfp` (le lfp est un point fixe), `lfp_le`
(le lfp majore tout pré-point-fixe) et `isLeast_lfp_le`, que nous exploitons dans
`Grounded.lean`.
-/

namespace Argumentation

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- La **fonction caractéristique** de Dung `F(S) = { a | S défend a }`, bundlée
comme un morphisme d'ordre monotone sur le treillis complet `Set α`. L'extension
grounded en est le plus petit point fixe (`F.lfp`). -/
def characteristic : Set α →o Set α where
  toFun S := af.defendedBy S
  monotone' := fun S T hST ↦ by
    show af.defendedBy S ⊆ af.defendedBy T
    rintro a ha
    exact af.defends_mono hST ha

/-- Reformulation : `a ∈ F(S) ⇔ S défend a`. -/
theorem mem_characteristic_iff (S : Set α) (a : α) :
    a ∈ af.characteristic S ↔ af.defends S a :=
  Iff.rfl

/-- L'image de `S` par `F` est exactement l'ensemble des arguments défendus par
`S`. (Identité de définition, fournie pour le raisonnement par réécriture.) -/
theorem characteristic_eq_defendedBy (S : Set α) :
    af.characteristic S = af.defendedBy S :=
  rfl

end AF

end Argumentation
