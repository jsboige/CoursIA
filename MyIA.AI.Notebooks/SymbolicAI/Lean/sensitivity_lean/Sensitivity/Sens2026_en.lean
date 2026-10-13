import Sensitivity.Separations_en
import Mathlib.Tactic.FinCases

/-!
# Sensitivity 2026: three teams, one refutation, and what the openai/math repo says about these objects

This file is an **additive** contribution to the `sensitivity_lean` lake
(Origami Epic #19898, fold 2, issue #20184): it modifies no existing
statement — neither Huang's theorem (`MainTheorem`) nor the definitions and
witnesses of `Separations`. It reuses `sensitivity`, `blockSensitivity` and
`flipBlock` as they stand, and adds the **three-tribe witness** `tribes32`:
the disjunction of three size-two conjunctions over `Q 6`.

## Family 132, quoted with its status

Family 132 of the openai/math repository (2026) — "total Boolean functions
with `bs(f) ≥ s(f)^α` for a fixed `α > 2`" — **refutes** the quadratic
strengthening of the sensitivity conjecture: the `bs/s` gap can exceed any
fixed polynomial in `s`. That result is quoted **with its status**
(formalized upstream, `lean/docs/132.md` of the repository; not re-proved by
us): re-proving it is out of scale for this lake.

`tribes32` is the **computable echo** of this neighbourhood — and it teaches
two things, one of them counterintuitive:

1. **The local separation extends**: at the zero vertex, `s = 0` and
   `bs ≥ 3` (the family of the three tribes is admissible) — the same local
   gap as the `orOfAnds` witness of `Separations`, but with three blocks
   instead of one.
2. **The naive bound `s ≤ t` (one tribe's size) is FALSE** — and it is
   `decide` that refuted it, at compile time: at the "one lit lamp per
   tribe" vertex, each first coordinate lights up its conjunction on its
   own, and the local sensitivity there is **3**
   (`tribes32_sensitivity_eq_three`). At this scale, `s` catches up with
   `bs`: tribes alone do not separate *globally* — the literature's
   separation requires addressing constructions (Rubinstein 1995), out of
   scale here and quoted for that reason.

The pedagogical story is exactly the 2026 one: **measured, not assumed** —
the intuition "two lamps per tribe, hence sensitivity 2" does not survive
the kernel's exhaustive enumeration.
-/

namespace Sensitivity_en

open Bool Finset Fintype

/-- The "tribes" witness in dimension 6: disjunction of three size-two
conjunctions (three "teams" of two coordinates) — the `tribes` of the
Nisan–Szegedy literature, at computable scale. -/
def tribes32 (x : Q 6) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)

/-- At the zero vertex, no single coordinate lights up `tribes32`: a whole
tribe must be flipped. The local sensitivity there is zero. -/
theorem tribes32_sensitivity_zero :
    sensitivity tribes32 (fun _ => false) = 0 := by
  decide

/-- **The refutation of the intuition, by exhaustive enumeration.** At the
"one lit lamp per tribe" vertex (odd coordinates), each first coordinate
lights up its conjunction by itself: the local sensitivity there is **3**,
not 2. The naive bound "at most one tribe's size" is false — it is the Lean
kernel that established this, by refuting the conjecture `∀ x, s ≤ 2` at
compile time. -/
theorem tribes32_sensitivity_eq_three :
    sensitivity tribes32 (fun i => i.val % 2 = 1) = 3 := by
  decide

set_option maxRecDepth 8192 in
/-- At the zero vertex, the family of the three tribes `{{0,1}, {2,3}, {4,5}}`
is admissible in the sense of `blockSensitivity`: nonempty blocks, each
flipping the value, pairwise disjoint. The block sensitivity there is
therefore at least **3**. -/
theorem tribes32_blockSensitivity_ge_three :
    3 ≤ blockSensitivity tribes32 (fun _ => false) := by
  classical
  have hfam : ∀ B ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))),
      B.Nonempty ∧ tribes32 (flipBlock (fun _ => false) B) ≠ tribes32 (fun _ => false) := by
    decide
  have hpair : ∀ B₁ ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))),
      ∀ B₂ ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
        Finset (Finset (Fin 6))),
      B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin 6)) = ∅ := by
    decide
  have hcard : ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))).card = 3 := by
    decide
  have hle : ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))).card ≤ blockSensitivity tribes32 (fun _ => false) :=
    Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩)
  rw [hcard] at hle
  exact hle

/-- **Local separation with three blocks**: at the zero vertex,
`s = 0 < 3 ≤ bs`. The same local gap as the `orOfAnds` witness of
`Separations` (one block), generalized to three disjoint blocks — the exact
mechanics by which the literature's addressing constructions build their
gaps. The *global* separation is not claimed:
`tribes32_sensitivity_eq_three` shows that `s` catches up with `bs`
elsewhere on the cube. -/
theorem tribes32_local_separation :
    sensitivity tribes32 (fun _ => false) <
      blockSensitivity tribes32 (fun _ => false) := by
  rw [tribes32_sensitivity_zero]
  exact Nat.lt_of_lt_of_le (by decide) tribes32_blockSensitivity_ge_three

end Sensitivity_en
