import Mathlib
import Argumentation.Basic_en

/-!
# Dung's characteristic function — an order morphism on `Set α`

The heart of Dung's argumentation theory is the **characteristic function**
`F(S) = { a | S defends a }`. Its fundamental property is **monotonicity**:
`S ⊆ T ⇒ F(S) ⊆ F(T)` (having more defenders can only widen the set of defended
arguments). This monotonicity makes it an order morphism `Set α →o Set α`; on
the complete lattice `(Set α, ⊆)`, the **Knaster–Tarski** theorem (Mathlib
`OrderHom.lfp`) guarantees the existence of a least fixed point — the **grounded**
extension.

Mathlib provides `OrderHom.lfp`, `map_lfp` (the lfp is a fixed point), `lfp_le`
(the lfp majorizes every pre-fixed-point) and `isLeast_lfp_le`, which we exploit
in `Grounded.lean`.
-/

namespace Argumentation_en

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- Dung's **characteristic function** `F(S) = { a | S defends a }`, bundled as
a monotone order morphism on the complete lattice `Set α`. The grounded
extension is its least fixed point (`F.lfp`). -/
def characteristic : Set α →o Set α where
  toFun S := af.defendedBy S
  monotone' := fun S T hST ↦ by
    show af.defendedBy S ⊆ af.defendedBy T
    rintro a ha
    exact af.defends_mono hST ha

/-- Reformulation: `a ∈ F(S) ⇔ S defends a`. -/
theorem mem_characteristic_iff (S : Set α) (a : α) :
    a ∈ af.characteristic S ↔ af.defends S a :=
  Iff.rfl

/-- The image of `S` under `F` is exactly the set of arguments defended by `S`.
(Definitional identity, provided for rewriting-style reasoning.) -/
theorem characteristic_eq_defendedBy (S : Set α) :
    af.characteristic S = af.defendedBy S :=
  rfl

end AF

end Argumentation_en
