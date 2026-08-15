/-!
# Flip descent — Phase 1: skeleton of Proposition 9.1 (core, no Mathlib)

This module formalizes the **combinatorial backbone** of the MIMO
coordinate-flip detection algorithm (Papailiopoulos, 2026 — issue #10984):
a descent over a state space where every **accepted** flip strictly decreases
the cost. The file is deliberately **dependency-free** (Lean 4 core only):
the real objective function (Lemma 11.1) and the LMMSE analysis (Lemma 5.1)
land in Phase 2 (`Objective.lean`, Mathlib); the §11 converse in Phase 3 via
the external SLT lake.

The flagship theorem `descent_target_before_ceiling` is the abstract form of
Proposition 9.1 of the paper: under (i) strict cost decrease at every
accepted flip, (ii) confinement of the cost within a barrier `B`, and
(iii) absence of stuck points outside the target, every **terminal** run
reaches the target in a number of flips **strictly below the ceiling `M_N`**.

The four ingredients of the proof, each pedagogically interesting:

1. `run_tail_cost_lt` — the strict decrease propagates from the local step to
   the whole tail of the run (recursion on the run structure);
2. `run_nodup` — a run never revisits a state (otherwise the cost would be
   strictly below itself);
3. `run_length_le_cost` — the number of flips of a run starting at `s₀` is
   bounded by `cost s₀` (the "descent budget");
4. `descent_flips_le_barrier` — under the confinement barrier `B`, the number
   of flips is bounded by `B`, hence strictly by `M_N > B`.
-/

namespace Mimo_en

variable {σ : Type} {accept : σ → σ → Prop} {cost : σ → Nat} {target : σ → Prop}

/-- A **run** of the algorithm: a list of states whose every consecutive pair
is an **accepted** flip (relation `accept`). The `single` case covers the run
reduced to the initial state; `nil` the empty run (convenient for proofs by
recursion). -/
inductive Run (accept : σ → σ → Prop) : List σ → Prop
  | nil : Run accept []
  | single (s : σ) : Run accept [s]
  | cons (s t : σ) (rest : List σ) (h : accept s t) (hr : Run accept (t :: rest)) :
      Run accept (s :: t :: rest)

/-- Last state of a run starting at `s₀`: where the algorithm stops. -/
def lastState : σ → List σ → σ
  | s, [] => s
  | _, t :: rest => lastState t rest

/-! ## Lemma 1 — the strict decrease propagates to the whole tail -/

/-- If every accepted flip strictly decreases the cost, then the cost of every
state visited after `s₀` is strictly below `cost s₀`. This is the key to
non-revisiting and to the descent budget. -/
theorem run_tail_cost_lt (hstrict : ∀ s t, accept s t → cost t < cost s) :
    ∀ (rest : List σ) (s₀ : σ), Run accept (s₀ :: rest) →
      ∀ x ∈ rest, cost x < cost s₀ := by
  intro rest
  induction rest with
  | nil => intro _ _ x hx; cases hx
  | cons u rest' ih =>
    intro s₀ hL x hx
    cases hL with
    | cons _ _ _ h hr =>
      cases List.mem_cons.1 hx with
      | inl hxu => subst hxu; exact hstrict _ _ h
      | inr hx' => exact Nat.lt_trans (ih u hr x hx') (hstrict _ _ h)

/-! ## Lemma 2 — a run never revisits a state -/

/-- A run with strictly decreasing cost is repetition-free: the state space
may be infinite, but the run itself lives in a finite set of distinct states
(one visit per strictly decreasing cost value). -/
theorem run_nodup (hstrict : ∀ s t, accept s t → cost t < cost s)
    {L : List σ} (hL : Run accept L) : L.Nodup := by
  induction hL with
  | nil => exact List.nodup_nil
  | single s => simp
  | cons s u rest h hr ih =>
    refine List.nodup_cons.2 ⟨?_, ih⟩
    intro hmem
    have hrun : Run accept (s :: u :: rest) := Run.cons s u rest h hr
    have hlt := run_tail_cost_lt hstrict (u :: rest) s hrun s hmem
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## Lemma 3 — the descent budget bounds the number of flips -/

/-- The number of flips of a run starting at `s₀` is at most `cost s₀`:
each flip consumes at least one unit of cost (values in `Nat`), and the cost
cannot go below zero. -/
theorem run_length_le_cost (hstrict : ∀ s t, accept s t → cost t < cost s) :
    ∀ (rest : List σ) (s₀ : σ), Run accept (s₀ :: rest) →
      rest.length ≤ cost s₀ := by
  intro rest
  induction rest with
  | nil => intro _ _; exact Nat.zero_le _
  | cons u rest' ih =>
    intro s₀ hL
    cases hL with
    | cons _ _ _ h hr =>
      have h1 : rest'.length ≤ cost u := ih u hr
      have h2 : cost u < cost s₀ := hstrict _ _ h
      have h3 : (u :: rest').length = rest'.length + 1 := rfl
      omega

/-! ## Proposition 9.1 — confinement, flip ceiling, target reached -/

/-- **Confinement barrier**: if the cost of every visited state stays below
`B`, then the number of flips is bounded by `B`. In the paper, the barrier
reflects the geometry of the problem (the cost cannot escape a bounded
strip); here it is a hypothesis, instantiated in Phase 2. -/
theorem descent_flips_le_barrier (hstrict : ∀ s t, accept s t → cost t < cost s)
    (s₀ : σ) (rest : List σ) (B : Nat)
    (hbarrier : ∀ s ∈ s₀ :: rest, cost s ≤ B)
    (hL : Run accept (s₀ :: rest)) :
    rest.length ≤ B := by
  have h1 := run_length_le_cost hstrict rest s₀ hL
  have h0 := hbarrier s₀ (by simp)
  omega

/-- **Proposition 9.1 (abstract form, Phase 1 skeleton).** Let a **terminal**
run (no accepted flip escapes the last state) under the three assumptions of
the paper:

- `hstrict` — every accepted flip strictly decreases the cost (Lemma 11.1 in
  Phase 2: a flip cost reads `4·(ρ/N·‖hᵢ‖² + √(ρ/N)·hᵢᵀw)`, and only flips
  decreasing the objective are accepted);
- `hbarrier` — the cost stays confined below `B` along the whole run;
- `hnostall` — outside the target, an accepted flip always exists (the
  algorithm can only get stuck on the target).

Then the last state of the run **belongs to the target**, and the run used
**strictly fewer than `M_N` flips** as soon as the ceiling `M_N` exceeds the
barrier `B`. This is exactly the complexity guarantee of the algorithm:
termination in the target before the flip budget runs out. -/
theorem descent_target_before_ceiling
    (hstrict : ∀ s t, accept s t → cost t < cost s)
    (hnostall : ∀ s : σ, (∀ u, ¬ accept s u) → target s)
    (s₀ : σ) (rest : List σ) (B M_N : Nat)
    (hbarrier : ∀ s ∈ s₀ :: rest, cost s ≤ B)
    (hL : Run accept (s₀ :: rest))
    (hterm : ∀ u, ¬ accept (lastState s₀ rest) u)
    (hceiling : B < M_N) :
    target (lastState s₀ rest) ∧ rest.length < M_N :=
  ⟨hnostall _ hterm,
   Nat.lt_of_le_of_lt (descent_flips_le_barrier hstrict s₀ rest B hbarrier hL) hceiling⟩

end Mimo_en
