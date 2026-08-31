import Mathlib
import Argumentation.Extensions_en

/-!
# Certified synthesis of stable extensions — Z3 witnesses (Law II, variant `-c`)

Fourth independent substrate for Building Site 2 (#12205, §4): the chain
**specification → generator ≠ verifier → witness → certificate** transferred
to Dung's abstract argumentation.

```
specification (AF-A, Stable semantics)  →  Z3 4.16.0  →  S = {1, 2, 5}  →  afA_stable_SA : afA.Stable SA := by decide
specification (AF-B, 3-cycle)           →  Z3 (UNSAT)  →  —            →  afB_no_stable : ∀ p, ¬ afB.Stable {a | p a} := by decide
```

Law II ("move from verifier to constructor", #12204) had already been crossed
on Life (#12286), Robinson-Goforth (#12364) and AMD (#12648); this module
tests whether it **transfers** to a finite substrate where the semantics is a
combinatorial constraint (conflict-freeness + dominance).

**Assumed debt (as in B1)**: the searcher — Z3, outside Lean — is not
certified. What is certified is the **witness**, by Lean kernel evaluation
(`decide`, no axioms). Nobody hand-wrote `{1, 2, 5}`: it is the model returned
by Z3 on the specification (script `synth_stable.py`, #13597).

## The no-solution case is a deliverable

AF-B (3-cycle) admits **no** stable extension: no conflict-free dominating
set exists — the three arguments mutually exclude each other in a cascade and
no singleton attacks the other two. Z3 returns UNSAT; `afB_no_stable`
certifies it by decisive enumeration of the 8 characteristic functions
`Fin 3 → Bool`: this is a **dissociation recorded at the bound n = 3**, not a
failed experiment.
-/

namespace Argumentation_en.Synthesis

/-- Decidability of implication — the component missing from the `decide`
synthesis chain for Dung semantics on a finite framework: the guards
`a ∈ S → φ` of `conflictFree` and `Stable` need it. `private`: file-scoped,
nothing exported. -/
private instance impDec (p q : Prop) [Decidable p] [Decidable q] :
    Decidable (p → q) :=
  match inferInstanceAs (Decidable p), inferInstanceAs (Decidable q) with
  | isFalse hp, _ => isTrue fun h => absurd h hp
  | isTrue _, isTrue hq => isTrue fun _ => hq
  | isTrue hp, isFalse hq => isFalse fun h => hq (h hp)

/-! ## AF-A: 6 arguments, specification with decidable attack table -/

/-- Attack table of AF-A — this is the **specification** (no witness here):
0 ↔ 1 mutual, 2 → 3, 4 ↔ 5 mutual, 1 → 3, 3 → 4, 0 → 5. -/
def afA_edges : List (Nat × Nat) :=
  [(0, 1), (1, 0), (2, 3), (4, 5), (5, 4), (1, 3), (3, 4), (0, 5)]

/-- The concrete AF-A on `Fin 6`: the attack relation is decidable
membership in the table. -/
def afA : AF (Fin 6) where
  attacks a b := afA_edges.contains (a.val, b.val) = true

/-- Witness returned by Z3 4.16.0 (solver model, transcribed verbatim):
the set `{1, 2, 5}`. -/
def SA : Set (Fin 6) := {a | a.val ∈ [1, 2, 5]}

instance (a b : Fin 6) : Decidable (afA.attacks a b) :=
  instDecidableEqBool (afA_edges.contains (a.val, b.val)) true

-- `def SA` (and `def afA`) do not unfold at `instances` transparency:
-- membership must be declared explicitly for synthesis to find it.
instance : DecidablePred (· ∈ SA) := fun a =>
  if h : a.val ∈ [1, 2, 5] then isTrue h else isFalse h

/-- **Certificate**: the Z3 witness `{1, 2, 5}` is a stable extension of
AF-A, evaluated by the Lean kernel — the "verifier → constructor" step is
crossed on this substrate. -/
theorem afA_stable_SA : afA.Stable SA := by
  unfold AF.Stable AF.conflictFree
  decide

/-! ## AF-B: the 3-cycle, no-solution case -/

/-- Attack table of AF-B: the cycle 0 → 1 → 2 → 0. -/
def afB_edges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 0)]

/-- The concrete AF-B on `Fin 3`. -/
def afB : AF (Fin 3) where
  attacks a b := afB_edges.contains (a.val, b.val) = true

instance (a b : Fin 3) : Decidable (afB.attacks a b) :=
  instDecidableEqBool (afB_edges.contains (a.val, b.val)) true

instance {p : Fin 3 → Bool} : DecidablePred (· ∈ {a | p a}) := fun a =>
  if h : p a = true then isTrue h else isFalse h

/-- **Dissociation certified at the bound n = 3**: the 3-cycle admits no
stable extension. Z3 returns UNSAT on the same specification; Lean certifies
the impossibility by enumerating the 8 characteristic functions `Fin 3 → Bool`
(every subset of `{0, 1, 2}` is `{a | p a}` for some `p`). A generator that
returns "no solution" with this certificate does not bypass the step: it
crosses point 4 of #12205's criterion. -/
theorem afB_no_stable : ∀ p : Fin 3 → Bool, ¬ afB.Stable {a | p a} := by
  intro p
  unfold AF.Stable AF.conflictFree
  decide +revert

end Argumentation_en.Synthesis
