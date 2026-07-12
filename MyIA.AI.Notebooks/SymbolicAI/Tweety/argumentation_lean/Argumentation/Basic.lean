import Mathlib

/-!
# Cadres d'argumentation (Dung 1995) — définitions de base

Un **cadre d'argumentation abstraite** (Dung, 1995) est un couple `(A, R)` où `A`
est un ensemble d'arguments et `R ⊆ A × A` une relation d'attaque. On l'encode
comme une structure `AF α` munissant un type d'arguments `α` d'une relation
`attacks : α → α → Prop` : on lit `af.attacks a b` comme « l'argument `a` attaque
l'argument `b` » (flèche `a → b`). L'univers des arguments est le type `α` tout
entier — encodage standard en formalisation, qui évite de transporter un sous-ensemble
`A` explicite et rend `Set α` un treillis complet sans hypothèse de finitude.

Deux notions Fondamentales :
- **Sans conflat (conflict-free)** : aucun membre de `S` n'en attaque un autre.
- **Défense** : `S` défend un argument `a` si tout attaquant de `a` est à son tour
  attaqué par un membre de `S`.

La défense est **monotone** en l'ensemble défenseur (plus de défenseurs ⇒ plus
d'arguments défendus) — propriété clé qui fait de la fonction caractéristique
`F(S) = {a | S défend a}` un `OrderHom` (voir `Characteristic.lean`).

Référence croisée :
- Notebook `Tweety-5-Abstract-Argumentation.ipynb` (série Tweety) : présentation
  Python des cadres de Dung, dont cette formalisation est le pendant prouvé.
- Epic Argumentum #2137.
-/

namespace Argumentation

variable {α : Type*}

/-- Un cadre d'argumentation abstraite de Dung : un type d'arguments `α` muni
d'une relation d'attaque binaire. `af.attacks a b` se lit « `a` attaque `b` ». -/
structure AF (α : Type*) where
  /-- Relation d'attaque : `attacks a b` signifie que l'argument `a` attaque `b`. -/
  attacks : α → α → Prop

namespace AF

variable (af : AF α)

/-- Un ensemble `S` est **sans conflat** si aucun de ses membres n'en attaque
un autre (Dung 1995, Définition 1). -/
def conflictFree (S : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ af.attacks a b

/-- L'argument `a` est **défendu** par l'ensemble `S` si tout attaquant de `a`
est à son tour attaqué par un membre de `S` (Dung 1995, Définition 3). -/
def defends (S : Set α) (a : α) : Prop :=
  ∀ b, af.attacks b a → ∃ c ∈ S, af.attacks c b

/-- L'ensemble des arguments défendus par `S` : l'image de `S` par la fonction
caractéristique de Dung. Défini ici pour commodité ; la version `OrderHom` bundlée
(monotone) vit dans `Characteristic.lean`. -/
def defendedBy (S : Set α) : Set α :=
  { a | af.defends S a }

/-!
## Lemmes élémentaires
-/

/-- L'ensemble vide est sans conflat : il n'a aucun membre à attaquer. -/
theorem conflictFree_empty : af.conflictFree (∅ : Set α) := by
  rintro _ ⟨⟩

/-- La défense est **monotone** en l'ensemble défenseur : si `S ⊆ T` et `S`
défend `a`, alors `T` défend aussi `a`. C'est la *croissance* de la fonction
caractéristique, cœur de la théorie du point fixe de Dung. -/
theorem defends_mono {S T : Set α} (hST : S ⊆ T) {a : α} (hS : af.defends S a) :
    af.defends T a := by
  intro b hb
  obtain ⟨c, hcS, hcb⟩ := hS b hb
  exact ⟨c, hST hcS, hcb⟩

/-- Si `S` est sans conflat, défend ses propres membres et défend `a`, alors aucun
membre de `S` n'attaque `a` : un attaquant interne de `a` serait lui-même attaqué
par un défenseur de `a` dans `S`, contredisant l'absence de conflat. Lemme-clé de
la preuve de la *Fundamental Lemma* de Dung. -/
theorem no_internal_attack_on_defended {S : Set α} (hcf : af.conflictFree S)
    (hself : ∀ a ∈ S, af.defends S a) {a : α} (hdef : af.defends S a) :
    ∀ b, b ∈ S → ¬ af.attacks b a := by
  intro b hbS hbatt
  obtain ⟨c, hcS, hcb⟩ := hdef b hbatt
  exact hcf hcS hbS hcb

end AF

end Argumentation
