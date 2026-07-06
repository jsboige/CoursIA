import Mathlib
import Argumentation.Basic_en
import Argumentation.Characteristic_en

/-!
# Dung's extensions — admissible, complete, grounded, preferred, stable

The five **semantics** of Dung (1995) characterize the sets of arguments that
are "rationally acceptable" according to criteria of coherence and defence of
decreasing strength:

| Semantics | Requirement |
|-----------|-------------|
| **Admissible** | conflict-free + defends its members |
| **Complete** | admissible + contains everything it defends |
| **Grounded** | the smallest complete extension (= lfp of `F`) |
| **Preferred** | a maximal complete extension |
| **Stable** | conflict-free + attacks every outside argument |

Dung's hierarchy: `Stable ⇒ Preferred ⇒ Complete ⇒ Admissible`. Each arrow is
proved in this file (`stable_complete`, `preferred_complete`,
`complete_admissible`), without `sorry`.
-/

namespace Argumentation_en

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- `S` is **admissible**: conflict-free and defends each of its members
(Dung 1995, Definition 5). -/
def Admissible (S : Set α) : Prop :=
  af.conflictFree S ∧ ∀ a ∈ S, af.defends S a

/-- `S` is **complete**: admissible and contains every argument it defends
(Dung 1995, Definition 7). -/
def Complete (S : Set α) : Prop :=
  af.Admissible S ∧ ∀ a, af.defends S a → a ∈ S

/-- The **grounded** extension: the least fixed point of the characteristic
function `F` (Knaster–Tarski). Detailed properties in `Grounded.lean`. -/
def grounded : Set α :=
  af.characteristic.lfp

/-- `S` is **preferred**: a **maximal** complete extension for inclusion
(Dung 1995, Definition 10). -/
def Preferred (S : Set α) : Prop :=
  af.Complete S ∧ ∀ T, af.Complete T → S ⊆ T → T ⊆ S

/-- `S` is **stable**: conflict-free and **attacks** every argument outside `S`
(Dung 1995, Definition 12). -/
def Stable (S : Set α) : Prop :=
  af.conflictFree S ∧ ∀ a, a ∉ S → ∃ b ∈ S, af.attacks b a

/-!
## Hierarchy of the semantics (Dung, sorry-free)
-/

/-- **Complete ⇒ Admissible**: by definition. -/
theorem complete_admissible {S : Set α} (h : af.Complete S) : af.Admissible S :=
  h.1

/-- **Preferred ⇒ Complete**: by definition. -/
theorem preferred_complete {S : Set α} (h : af.Preferred S) : af.Complete S :=
  h.1

/-- **Stable ⇒ Complete**: a stable set is admissible (since any internal attack
would contradict conflict-freeness) and contains everything it defends
(otherwise a defended argument outside `S` would be attacked by a member of `S`,
contradicting defence). -/
theorem stable_complete {S : Set α} (h : af.Stable S) : af.Complete S := by
  refine ⟨?_, fun a ha => ?_⟩
  · -- Stable ⇒ Admissible : conflict-free (given) + defends its members.
    refine ⟨h.1, fun a haS b hbatt => ?_⟩
    -- b attacks a. If b ∈ S, then b,a ∈ S and b attacks a = conflict. So b ∉ S.
    by_cases hbS : b ∈ S
    · exact absurd hbatt (h.1 hbS haS)
    · -- b ∉ S ⇒ by stability ∃ c ∈ S attacks b.
      exact h.2 b hbS
  · -- a defended by S ; show a ∈ S. Otherwise, stability ⇒ ∃ b ∈ S attacks a ;
    -- but a defended ⇒ ∃ c ∈ S attacks b ; b,c ∈ S and c attacks b = conflict.
    by_contra hanot
    obtain ⟨b, hbS, hbatt⟩ := h.2 a hanot
    obtain ⟨c, hcS, hcb⟩ := ha b hbatt
    exact h.1 hcS hbS hcb

end AF

end Argumentation_en
