import Mathlib
import Argumentation.Basic_en
import Argumentation.Characteristic_en
import Argumentation.Extensions_en

/-!
# Grounded extension — fixed point and properties (Knaster–Tarski)

Dung's **grounded** extension is defined as the **least fixed point** of the
characteristic function `F`:
```
grounded = F.lfp   (Knaster–Tarski on the complete lattice (Set α, ⊆))
```
Mathlib provides `OrderHom.map_lfp` (`F.lfp` is a fixed point), `OrderHom.lfp_le`
(`F.lfp` majorizes every pre-fixed-point) — which we exploit to prove, **without
any `sorry`**, the identities characterizing the grounded extension:

- `grounded_fixed` : `F(grounded) = grounded` (it is indeed a fixed point).
- `grounded_defends_iff_mem` : `a ∈ grounded ⇔ grounded defends a`
  (defence-based characterization, the heart of the grounded semantics).
- `grounded_least_complete` : every complete extension contains `grounded`
  (the grounded is the **smallest** complete extension — `lfp_le`).

Plus Dung's key lemma **`F_preserves_admissible`**: the characteristic function
preserves admissibility (`Admissible S ⇒ Admissible (F S)`), the cornerstone of
the existence of complete extensions.

### OPEN milestone (documented, NOT sorry-backed)

The proof that `grounded` is **itself** a complete extension (hence conflict-free)
is the substantial result of Dung (Proposition 11). It requires, for a finite
framework, the **finite stabilization** of the iterated sequence
`∅ ⊂ F(∅) ⊂ F²(∅) ⊂ …` towards the `lfp` (each iterate is admissible via
`F_preserves_admissible`; the chain stabilizes in `|α|` steps). This
finite-iteration↔`lfp` connection is deliberately **not stated as a `sorry`**: the
current library remains entirely `sorry`-free, delivering the fixed-point
identities, least-completeness, the hierarchy of the semantics and the
Fundamental Lemma.
-/

namespace Argumentation_en

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- `grounded` is a **fixed point** of the characteristic function
(`F(grounded) = grounded`). Knaster–Tarski identity via `OrderHom.map_lfp`. -/
theorem grounded_fixed :
    af.characteristic af.grounded = af.grounded :=
  af.characteristic.map_lfp

/-- Defence-based characterization: `a ∈ grounded` **if and only if** `grounded`
defends `a`. Immediate consequence of the fixed point and the definition of `F`. -/
theorem grounded_defends_iff_mem (a : α) :
    af.defends af.grounded a ↔ a ∈ af.grounded := by
  constructor
  · intro h
    rw [← af.grounded_fixed]
    exact (af.mem_characteristic_iff af.grounded a).mpr h
  · intro h
    rw [← af.grounded_fixed] at h
    exact (af.mem_characteristic_iff af.grounded a).mp h

/-- The `grounded` is the **smallest complete extension**: every complete
extension `T` contains `grounded`. Proof via `OrderHom.lfp_le` applied to the
pre-fixed-point `F(T) ⊆ T` (a complete extension contains everything it defends). -/
theorem grounded_least_complete (T : Set α) (h : af.Complete T) :
    af.grounded ⊆ T := by
  have hFT : af.characteristic T ⊆ T := by
    rintro a ha
    exact h.2 a ((af.mem_characteristic_iff T a).mp ha)
  show af.characteristic.lfp ⊆ T
  exact af.characteristic.lfp_le hFT

/-!
## Dung's key lemma: `F` preserves admissibility
-/

/-- The characteristic function **preserves conflict-freeness**:
if `S` is conflict-free, then so is `F(S)`. -/
theorem F_preserves_conflictFree {S : Set α} (hcf : af.conflictFree S) :
    af.conflictFree (af.characteristic S) := by
  rintro a ha b hb hab
  -- a,b ∈ F(S) ⟹ S defends a and b ; a attacks b ⟹ chain of counter-attacks
  -- in S ⟹ contradicts the conflict-freeness of S.
  obtain ⟨c, hcS, hca⟩ := hb a hab
  obtain ⟨d, hdS, hdc⟩ := ha c hca
  exact hcf hdS hcS hdc

/-- **Dung's lemma (Proposition 7)**: the characteristic function preserves
admissibility — `Admissible S ⇒ Admissible (F S)`. This is the fundamental fact
guaranteeing the existence of complete extensions by iteration from `∅`. -/
theorem F_preserves_admissible {S : Set α} (h : af.Admissible S) :
    af.Admissible (af.characteristic S) := by
  refine ⟨af.F_preserves_conflictFree h.1, ?_⟩
  rintro a ha b hb
  obtain ⟨c, hcS, hcb⟩ := ha b hb
  refine ⟨c, ?_, hcb⟩
  exact (af.mem_characteristic_iff S c).mpr (h.2 c hcS)

end AF

end Argumentation_en
