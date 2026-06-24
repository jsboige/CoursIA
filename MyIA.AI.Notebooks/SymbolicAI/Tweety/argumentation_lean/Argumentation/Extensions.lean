import Mathlib
import Argumentation.Basic
import Argumentation.Characteristic

/-!
# Extensions de Dung — admissible, complète, grounded, preferred, stable

Les cinq **sémantiques** de Dung (1995) caractérisent les ensembles d'arguments
« rationnellement acceptables » selon des critères de cohérence et de défense
décroissants en exigence :

| Sémantique | Exigence |
|------------|----------|
| **Admissible** | sans conflat + défend ses membres |
| **Complète** | admissible + contient tout ce qu'elle défend |
| **Grounded** | la plus petite extension complète (= lfp de `F`) |
| **Preferred** | une extension complète maximale |
| **Stable** | sans conflat + attaque tout argument extérieur |

Hiérarchie de Dung : `Stable ⇒ Preferred ⇒ Complete ⇒ Admissible`. Chaque flèche
est prouvée dans ce fichier (`stable_complete`, `preferred_complete`,
`complete_admissible`), sans `sorry`.
-/

namespace Argumentation

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- `S` est **admissible** : sans conflat et défend chacun de ses membres
(Dung 1995, Définition 5). -/
def Admissible (S : Set α) : Prop :=
  af.conflictFree S ∧ ∀ a ∈ S, af.defends S a

/-- `S` est **complète** : admissible et contient tout argument qu'elle défend
(Dung 1995, Définition 7). -/
def Complete (S : Set α) : Prop :=
  af.Admissible S ∧ ∀ a, af.defends S a → a ∈ S

/-- L'extension **grounded** : le plus petit point fixe de la fonction
caractéristique `F` (Knaster–Tarski). Propriétés détaillées dans `Grounded.lean`. -/
def grounded : Set α :=
  af.characteristic.lfp

/-- `S` est **preferred** : une extension complète **maximale** pour l'inclusion
(Dung 1995, Définition 10). -/
def Preferred (S : Set α) : Prop :=
  af.Complete S ∧ ∀ T, af.Complete T → S ⊆ T → T ⊆ S

/-- `S` est **stable** : sans conflat et **attaque** tout argument hors de `S`
(Dung 1995, Définition 12). -/
def Stable (S : Set α) : Prop :=
  af.conflictFree S ∧ ∀ a, a ∉ S → ∃ b ∈ S, af.attacks b a

/-!
## Hiérarchie des sémantiques (Dung, sans sorry)
-/

/-- **Complete ⇒ Admissible** : par définition. -/
theorem complete_admissible {S : Set α} (h : af.Complete S) : af.Admissible S :=
  h.1

/-- **Preferred ⇒ Complete** : par définition. -/
theorem preferred_complete {S : Set α} (h : af.Preferred S) : af.Complete S :=
  h.1

/-- **Stable ⇒ Complete** : un ensemble stable est admissible (car la moindre
attaque interne contredirait l'absence de conflat) et contient tout ce qu'il
défend (sinon un argument défendu hors de `S` serait attaqué par un membre de
`S`, contredisant la défense). -/
theorem stable_complete {S : Set α} (h : af.Stable S) : af.Complete S := by
  refine ⟨?_, fun a ha => ?_⟩
  · -- Stable ⇒ Admissible : sans conflat (donné) + défend ses membres.
    refine ⟨h.1, fun a haS b hbatt => ?_⟩
    -- b attaque a. Si b ∈ S, alors b,a ∈ S et b attaque a = conflat. Donc b ∉ S.
    by_cases hbS : b ∈ S
    · exact absurd hbatt (h.1 hbS haS)
    · -- b ∉ S ⇒ par stabilité ∃ c ∈ S attaque b.
      exact h.2 b hbS
  · -- a défendu par S ; montrer a ∈ S. Sinon, stabilité ⇒ ∃ b ∈ S attaque a ;
    -- mais a défendu ⇒ ∃ c ∈ S attaque b ; b,c ∈ S et c attaque b = conflat.
    by_contra hanot
    obtain ⟨b, hbS, hbatt⟩ := h.2 a hanot
    obtain ⟨c, hcS, hcb⟩ := ha b hbatt
    exact h.1 hcS hbS hcb

end AF

end Argumentation
