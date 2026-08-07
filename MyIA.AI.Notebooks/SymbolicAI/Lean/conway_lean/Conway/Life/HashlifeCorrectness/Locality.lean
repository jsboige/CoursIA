/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Locality

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-! ## P0. Light-cone warm-up lemmas (prover ramp)
was byte-identically displaced from the original monolith at PR A of
#9863 (po-2023, dispatch ai-01 2026-08-07T12:20:37Z).

Proof bodies are unchanged — only framing (imports, namespace opens,
this docstring) is added. The 38 allow-axioms names referenced by the
audit job in `.github/workflows/lean-conway.yml` depend only on the
`Conway.Life.*` namespace prefix, NOT on intermediate namespaces or
file paths — so the allow-list stays byte-identical across the split.
-/

import Conway.Life
import Conway.Life.GridCanonical
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.ConeGeometry

namespace Conway
namespace Life

open MacroCell
/-! ## P0. Light-cone warm-up lemmas (prover ramp)

Elementary facts about `manhattan` and `lightCone` that feed the **base case**
of P2 (`step_light_cone` at `t = 0`). `manhattan_self` and `manhattan_comm` are
hand-proved here (genuine content — `manhattan` is a metric-like quantity, these
are the reflexivity and symmetry axioms). `self_mem_lightCone` and
`lightCone_zero` are **proved** (PRs #2097, #2107). Originally left as `sorry`
for multi-agent prover warm-up (Epic #1453), both were eliminated by hand
proofs during the prover iteration cycle. -/

/-- The Manhattan distance from a cell to itself is zero. -/
theorem manhattan_self (p : Int × Int) : manhattan p p = 0 := by
  unfold manhattan
  omega

/-- The Manhattan distance is symmetric. -/
theorem manhattan_comm (p q : Int × Int) : manhattan p q = manhattan q p := by
  unfold manhattan
  omega

/-- Every cell lies in its own light cone, for any radius `t`.

    **Proof strategy** (P0, difficulty: easy):
    `manhattan p p = 0 ≤ t` (by `manhattan_self`), so `p` passes the `d ≤ t`
    filter. Unfold `lightCone`; the `i = t` term of `rs` gives
    `p.1 - t + t = p.1` and the `j = t` term of `cs` gives `p.2`, so the pair
    `(p.1, p.2) = p` is produced. Discharge membership over
    `List.flatMap`/`List.filterMap` with `List.mem_flatMap` /
    `List.mem_filterMap`. -/
theorem self_mem_lightCone (p : Int × Int) (t : Nat) : p ∈ lightCone p t := by
  unfold lightCone
  simp only [List.mem_flatMap]
  use p.1
  constructor
  · -- p.1 ∈ rs = (List.range (2*t+1)).map (fun i => p.1 - (t:Int) + i)
    simp only [List.mem_map]
    use t
    constructor
    · simp [List.mem_range]; omega
    · omega  -- p.1 = p.1 - t + t
  · -- p ∈ (List.filterMap ... cs) with r = p.1
    simp only [List.mem_filterMap]
    use p.2
    constructor
    · -- p.2 ∈ cs = (List.range (2*t+1)).map (fun j => p.2 - (t:Int) + j)
      simp only [List.mem_map]
      use t
      constructor
      · simp [List.mem_range]; omega
      · omega  -- p.2 = p.2 - t + t
    · -- filter condition: d = 0 ≤ t, so some (p.1, p.2) = some p
      simp [show (p.1, p.2) = p from rfl]

/-- The light cone of radius `0` is exactly the singleton `[p]`.

    **Proof strategy** (P0, difficulty: easy):
    With `t = 0`, `List.range 1 = [0]`, so `rs = [p.1]` and `cs = [p.2]`; the
    filter keeps `(p.1, p.2)` since `d = 0 ≤ 0`. The whole expression reduces by
    computation — `simp [lightCone]` followed by `decide`, or a direct `List`
    evaluation after `Prod.ext`. -/
theorem lightCone_zero (p : Int × Int) : lightCone p 0 = [p] := by
  simp [lightCone, List.range_succ, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.filterMap_cons,
        List.filterMap_nil, Int.natAbs]

/-! ## P2. Light-cone locality (speed of light = 2 in Manhattan distance)

The state of cell `p` after `t` generations of B3/S23 depends only on the
initial state of cells within Manhattan distance `2*t` of `p`. This is the
"speed of light" principle for GoL: in one step, information can travel to
any Moore neighbor (Chebyshev distance 1, Manhattan distance ≤ 2). After
`t` steps, the reachable region has Chebyshev radius `t`, which is contained
in the Manhattan ball of radius `2*t`.

### Helper lemmas for P2

These bridge lemmas establish the locality of a single B3/S23 step, which
is then lifted by induction to `evolve t`. -/

/-- Symmetry of natAbs: `Int.natAbs (a - b) = Int.natAbs (b - a)`. -/
private theorem int_natAbs_sub_comm (a b : Int) :
    Int.natAbs (a - b) = Int.natAbs (b - a) := by
  omega

/-- If `manhattan p q ≤ t`, then `q ∈ lightCone p t`.

    Left as sorry — the proof requires constructing explicit list membership
    witnesses in the `lightCone` comprehension, with `Int.toNat` conversion
    and `Int.natAbs` symmetry. The mathematical fact is trivially true:
    if `|q.1 - p.1| + |q.2 - p.2| ≤ t` then `(q.1, q.2)` is within the
    Manhattan ball of radius `t`, which is exactly what `lightCone p t` enumerates. -/
theorem mem_lightCone_of_manhattan_le (p q : Int × Int) (t : Nat)
    (h : manhattan p q ≤ t) : q ∈ lightCone p t := by
  unfold manhattan at h
  -- h : Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2) ≤ t
  -- Switch sub order to match lightCone's filterMap predicate (q - p form).
  rw [int_natAbs_sub_comm p.1 q.1, int_natAbs_sub_comm p.2 q.2] at h
  -- h : Int.natAbs (q.1 - p.1) + Int.natAbs (q.2 - p.2) ≤ t
  -- Derive per-coordinate Int bounds via Int.abs_le (omega does not propagate
  -- natAbs through the toNat-cast subgoals reliably).
  have hxNat : Int.natAbs (q.1 - p.1) ≤ t :=
    Nat.le_trans (Nat.le_add_right _ _) h
  have hyNat : Int.natAbs (q.2 - p.2) ≤ t :=
    Nat.le_trans (Nat.le_add_left _ _) h
  have hx_abs : |q.1 - p.1| ≤ (t : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hxNat
  have hy_abs : |q.2 - p.2| ≤ (t : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hyNat
  obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp hx_abs
  obtain ⟨hy_lo, hy_hi⟩ := abs_le.mp hy_abs
  -- Both differences are in [-t, t]; their +t lift is in [0, 2t].
  have hx_nn : (0 : Int) ≤ q.1 - p.1 + (t : Int) := by linarith
  have hy_nn : (0 : Int) ≤ q.2 - p.2 + (t : Int) := by linarith
  -- Witnesses i and j into List.range (2t+1).
  set i : Nat := (q.1 - p.1 + (t : Int)).toNat with hi_def_eq
  set j : Nat := (q.2 - p.2 + (t : Int)).toNat with hj_def_eq
  have hi_cast : (↑i : Int) = q.1 - p.1 + (t : Int) := by
    rw [hi_def_eq]; exact Int.toNat_of_nonneg hx_nn
  have hj_cast : (↑j : Int) = q.2 - p.2 + (t : Int) := by
    rw [hj_def_eq]; exact Int.toNat_of_nonneg hy_nn
  have hi_lt : i < 2 * t + 1 := by
    have h_int : (↑i : Int) < ((2 * t + 1 : Nat) : Int) := by
      rw [hi_cast]; push_cast; linarith
    exact_mod_cast h_int
  have hj_lt : j < 2 * t + 1 := by
    have h_int : (↑j : Int) < ((2 * t + 1 : Nat) : Int) := by
      rw [hj_cast]; push_cast; linarith
    exact_mod_cast h_int
  have hi_image : p.1 - (t : Int) + ↑i = q.1 := by rw [hi_cast]; ring
  have hj_image : p.2 - (t : Int) + ↑j = q.2 := by rw [hj_cast]; ring
  -- Assemble the membership proof.
  -- Note: Lean elaborates `List.range n |>.map (fun i => p.1 - ↑t + i)` (where i : Nat)
  -- as `List.map (fun (i : Int) => p.1 - ↑t + i) (List.range n |>.map (↑·))` —
  -- a composition of two maps. We need two nested `List.mem_map.mpr` calls.
  unfold lightCone
  refine List.mem_flatMap.mpr ⟨q.1, ?_, ?_⟩
  · -- q.1 ∈ List.map (fun (i : Int) => p.1 - ↑t + i) (do let a ← range; pure ↑a)
    refine List.mem_map.mpr ⟨(↑i : Int), ?_, hi_image⟩
    -- ↑i ∈ do let a ← range; pure ↑a — use mem_flatMap on the do/pure form
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi_lt, ?_⟩
    exact List.mem_singleton.mpr rfl
  · refine List.mem_filterMap.mpr ⟨q.2, ?_, ?_⟩
    · -- q.2 ∈ List.map (fun (j : Int) => p.2 - ↑t + j) (do let a ← range; pure ↑a)
      refine List.mem_map.mpr ⟨(↑j : Int), ?_, hj_image⟩
      refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj_lt, ?_⟩
      exact List.mem_singleton.mpr rfl
    · -- (if d ≤ t then some (q.1, q.2) else none) = some q
      simp only [if_pos h]

/-- Reverse direction: every cell in `lightCone p t` is within Manhattan
    distance `t` of `p`. The light cone is exactly the Manhattan ball of
    radius `t`. -/
theorem manhattan_le_of_mem_lightCone (p q : Int × Int) (t : Nat)
    (h : q ∈ lightCone p t) : manhattan p q ≤ t := by
  unfold lightCone at h
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_map] at h
  obtain ⟨r, _, c, _, h_some⟩ := h
  by_cases h_le : Int.natAbs (r - p.1) + Int.natAbs (c - p.2) ≤ t
  · rw [if_pos h_le] at h_some
    have h_eq : (r, c) = q := Option.some.inj h_some
    unfold manhattan
    rw [← h_eq]
    rw [int_natAbs_sub_comm p.1 r, int_natAbs_sub_comm p.2 c]
    exact h_le
  · rw [if_neg h_le] at h_some
    simp at h_some

/-- Triangle inequality for Manhattan distance:
    `manhattan p r ≤ manhattan p q + manhattan q r`.
    Used to chain light-cone membership across induction on `evolve` steps. -/
theorem manhattan_triangle (p q r : Int × Int) :
    manhattan p r ≤ manhattan p q + manhattan q r := by
  unfold manhattan
  have h1 : Int.natAbs (p.1 - r.1) ≤ Int.natAbs (p.1 - q.1) + Int.natAbs (q.1 - r.1) := by
    have h_split : p.1 - r.1 = (p.1 - q.1) + (q.1 - r.1) := by ring
    rw [h_split]
    exact Int.natAbs_add_le _ _
  have h2 : Int.natAbs (p.2 - r.2) ≤ Int.natAbs (p.2 - q.2) + Int.natAbs (q.2 - r.2) := by
    have h_split : p.2 - r.2 = (p.2 - q.2) + (q.2 - r.2) := by ring
    rw [h_split]
    exact Int.natAbs_add_le _ _
  omega

/-- Helper: if `a - b` is in the set {-1, 0, 1}, then `Int.natAbs (a - b) ≤ 1`. -/
private theorem int_natAbs_of_three (a b : Int) (h : a - b = -1 ∨ a - b = 0 ∨ a - b = 1) :
    Int.natAbs (a - b) ≤ 1 := by
  rcases h with h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-- Every Moore neighbor of `p` has Manhattan distance at most 2 from `p`.
    (Diagonal neighbors have Manhattan distance 2; orthogonal neighbors have 1.)

    **Proof**: For each Moore neighbor `q`, the row difference `p.1 - q.1` and
    column difference `p.2 - q.2` are each in {-1, 0, 1}. By `int_natAbs_of_three`,
    each has `natAbs ≤ 1`, so the Manhattan distance is ≤ 1 + 1 = 2. -/
theorem manhattan_moore_le_two (p q : Int × Int) (hq : q ∈ mooreNeighbors p) :
    manhattan p q ≤ 2 := by
  unfold manhattan mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · -- q = (p.1-1, p.2-1)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1-1, p.2)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1-1, p.2+1)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1, p.2-1)
    have hd1 : p.1 - q.1 = 0 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1, p.2+1)
    have hd1 : p.1 - q.1 = 0 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2-1)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2+1)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q ∈ [] — impossible
    simp at h

/-- Moore neighborhood is symmetric: q ∈ mooreNeighbors p → p ∈ mooreNeighbors q.
    Each offset (dr, dc) has its negation (-dr, -dc) in the list. -/
theorem mooreNeighbors_symm (p q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : p ∈ mooreNeighbors q := by
  -- Direct case analysis: for each of the 8 positions of q relative to p,
  -- p appears at the opposite position in mooreNeighbors q.
  unfold mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · -- q = (p.1-1, p.2-1) → need (p.1, p.2) = (q.1+1, q.2+1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1-1, p.2) → need (p.1, p.2) = (q.1+1, q.2) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1-1, p.2+1) → need (p.1, p.2) = (q.1+1, q.2-1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1, p.2-1) → need (p.1, p.2) = (q.1, q.2+1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1, p.2+1) → need (p.1, p.2) = (q.1, q.2-1) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2-1) → need (p.1, p.2) = (q.1-1, q.2+1) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2) → need (p.1, p.2) = (q.1-1, q.2) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2+1) → need (p.1, p.2) = (q.1-1, q.2-1) ∈ list
    subst h; simp
  · simp at h

/-- If `aliveNext g p = true` then `p ∈ candidates g`.
    For survival (S23): `isAlive g p = true` → `p ∈ g`.
    For birth (B3): `liveNeighborCount g p = 3` → some neighbor alive → `p ∈ g.flatMap mooreNeighbors`. -/
theorem aliveNext_true_mem_candidates (g : Grid) (p : Int × Int)
    (h : aliveNext g p = true) : p ∈ candidates g := by
  unfold aliveNext candidates at *
  simp only [List.mem_append]
  -- Split on isAlive g p
  by_cases h_alive : isAlive g p = true
  · -- Survival: p ∈ g (already alive)
    left
    rw [isAlive] at h_alive
    exact Iff.mp (List.elem_iff) h_alive
  · -- Birth: isAlive g p = false, so aliveNext g p = true means liveNeighborCount g p = 3
    -- Then some Moore neighbor q has isAlive g q = true → q ∈ g and p ∈ mooreNeighbors q
    right
    -- Convert h_alive to isAlive g p = false
    have h_iA_false : isAlive g p = false := by
      cases h_iA : isAlive g p
      · rfl
      · exact absurd h_iA h_alive
    -- Derive liveNeighborCount g p = 3 from h (without unfolding isAlive everywhere)
    have h3 : liveNeighborCount g p = 3 := by
      rw [h_iA_false] at h
      -- h : (let n := liveNeighborCount g p; if false then ... else n == 3) = true
      simpa using h
    -- liveNeighborCount unfolds to countP (isAlive g)
    have h_count : (mooreNeighbors p).countP (isAlive g) = 3 := h3
    -- countP = 3 > 0, so exists q ∈ mooreNeighbors p with isAlive g q = true
    have h_pos : 0 < (mooreNeighbors p).countP (isAlive g) := by omega
    rw [List.countP_pos_iff] at h_pos
    obtain ⟨q, hq_mem, hq_alive⟩ := h_pos
    -- hq_alive : isAlive g q (which means isAlive g q = true via Bool coercion)
    -- By symmetry, p ∈ mooreNeighbors q
    have hp_symm : p ∈ mooreNeighbors q := mooreNeighbors_symm p q hq_mem
    -- isAlive g q = true means q ∈ g (elem_iff forward)
    have hq_in_g : q ∈ g := by
      rw [isAlive] at hq_alive
      exact Iff.mp (List.elem_iff) hq_alive
    -- p ∈ g.flatMap mooreNeighbors because q ∈ g and p ∈ mooreNeighbors q
    exact List.mem_flatMap.mpr ⟨q, hq_in_g, hp_symm⟩

/-- Moore neighborhood ⊆ light cone of radius 2. -/
theorem moore_subset_cone (p : Int × Int) (q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : q ∈ lightCone p 2 := by
  have hmd := manhattan_moore_le_two p q hq
  exact mem_lightCone_of_manhattan_le p q 2 hmd

/-- If two grids agree on `p` and all its Moore neighbors, then `aliveNext`
    gives the same result for `p` (B3/S23 locality). -/
theorem aliveNext_local (g₁ g₂ : Grid) (p : Int × Int)
    (h_self : isAlive g₁ p = isAlive g₂ p)
    (h_nbrs : ∀ q ∈ mooreNeighbors p, isAlive g₁ q = isAlive g₂ q) :
    aliveNext g₁ p = aliveNext g₂ p := by
  unfold aliveNext liveNeighborCount
  -- The let-binding creates: if (isAlive g p) then ... else ...
  -- Both sides have the same structure; rewrite with h_self
  rw [h_self]
  -- Now both sides have the same isAlive test; need countP equality
  have h_count : (mooreNeighbors p).countP (isAlive g₁) =
                 (mooreNeighbors p).countP (isAlive g₂) := by
    apply List.countP_congr
    intro q hq
    have h := h_nbrs q hq
    exact iff_of_eq (congrArg (· = true) h)
  rw [h_count]

/-- Bridge: `isAlive (step g) p = aliveNext g p`.
    Since `step g = sortDedup ((candidates g).filter (aliveNext g))` and
    `sortDedup` preserves membership, `p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true`.
    For the forward direction (`aliveNext g p = true → p ∈ step g`), use
    `aliveNext_true_mem_candidates` to obtain `p ∈ candidates g`. -/
theorem isAlive_step_eq_aliveNext (g : Grid) (p : Int × Int) :
    isAlive (step g) p = aliveNext g p := by
  by_cases h : aliveNext g p = true
  · -- aliveNext g p = true case: must have p ∈ step g.
    rw [h]
    unfold isAlive step
    rw [List.elem_iff, mem_sortDedup, List.mem_filter]
    exact ⟨aliveNext_true_mem_candidates g p h, h⟩
  · -- aliveNext g p = false case: p ∉ filter, hence p ∉ step g.
    have h_false : aliveNext g p = false := by
      cases h_iA : aliveNext g p
      · rfl
      · exact absurd h_iA h
    rw [h_false]
    unfold isAlive step
    -- Need: (sortDedup ...).elem p = false. Show p ∉ sortDedup, then elem = false.
    have h_ne : p ∉ sortDedup ((candidates g).filter (aliveNext g)) := by
      rw [mem_sortDedup, List.mem_filter]
      rintro ⟨_, h_alive⟩
      exact h h_alive
    cases h_e : (sortDedup ((candidates g).filter (aliveNext g))).elem p
    · rfl
    · exact absurd (List.elem_iff.mp h_e) h_ne

/-- If two grids agree on the light cone of radius 2 around `p`, then
    `isAlive (step g₁) p = isAlive (step g₂) p` (single-step locality).
    The radius 2 is needed because Moore neighbors (including diagonals)
    have Manhattan distance ≤ 2. -/
theorem step_local (g₁ g₂ : Grid) (p : Int × Int)
    (h_cone : ∀ q ∈ lightCone p 2, isAlive g₁ q = isAlive g₂ q) :
    isAlive (step g₁) p = isAlive (step g₂) p := by
  have h_self : isAlive g₁ p = isAlive g₂ p := by
    apply h_cone p; exact self_mem_lightCone p 2
  have h_nbrs : ∀ q ∈ mooreNeighbors p, isAlive g₁ q = isAlive g₂ q := by
    intro q hq; apply h_cone q; exact moore_subset_cone p q hq
  have h_alive : aliveNext g₁ p = aliveNext g₂ p :=
    aliveNext_local g₁ g₂ p h_self h_nbrs
  rw [isAlive_step_eq_aliveNext, isAlive_step_eq_aliveNext, h_alive]

/-- If two grids agree on the light cone of radius `2 * t` around `p`, then
    after `t` steps they yield the same liveness at `p`.

    The factor of 2 arises because B3/S23's speed of light is 1 in Chebyshev
    distance (= 2 in Manhattan distance for diagonal neighbors). After `t`
    steps, information can travel Chebyshev distance `t`, which is contained
    in the Manhattan ball of radius `2 * t`.

    **Proof strategy** (P2, difficulty: intermediate):
    Induction on `t`.
    - Base `t = 0`: `evolve 0 g = g`, and agreeing on cone of radius 0 means
      agreeing at `p` itself.
    - Inductive step: `evolve (t+1) g = step (evolve t g)`, and `step`
      at `p` depends on `evolve t g` at cells within Manhattan distance 2
      (the Moore neighborhood). By IH, each of those depends on `g` at cells
      within Manhattan distance `2*t` around each neighbor. The union of
      Manhattan balls of radius `2*t` centered on the Moore neighborhood
      (Manhattan distance ≤ 2 from `p`) is the Manhattan ball of radius
      `2*(t+1)` centered on `p`. -/
theorem step_light_cone (t : Nat) (g₁ g₂ : Grid) (p : Int × Int)
    (h_cone : ∀ q ∈ lightCone p (2 * t), isAlive g₁ q = isAlive g₂ q) :
    isAlive (evolve t g₁) p = isAlive (evolve t g₂) p := by
  induction t generalizing p with
  | zero =>
    simp only [evolve_zero, Nat.mul_zero] at *
    exact h_cone p (self_mem_lightCone p 0)
  | succ n ih =>
    simp only [evolve_succ]
    apply step_local
    intro q hq
    apply ih
    intro r hr
    apply h_cone r
    apply mem_lightCone_of_manhattan_le
    have hpq : manhattan p q ≤ 2 := manhattan_le_of_mem_lightCone p q 2 hq
    have hqr : manhattan q r ≤ 2 * n := manhattan_le_of_mem_lightCone q r (2 * n) hr
    have h_tri : manhattan p r ≤ manhattan p q + manhattan q r := manhattan_triangle p q r
    omega

/-! ## Locality composition (radius-doubling agreement)

`evolve_cone_agree` is the sorry-free, P4-independent locality-composition
handle consumed by `p4_succ_membership` (the G3 bridge): it reduces agreement
of `evolve u g₁` and `evolve u g₂` on `lightCone p (2*t)` to agreement of
`g₁ g₂` on the larger `lightCone p (2*(t+u))`, so that a further
`step_light_cone t` step closes the half-step composition. -/

/-- **Locality composition (radius-doubling agreement).** If two grids `g₁ g₂`
    agree on every cell of the light cone of radius `2*(t+u)` around `p`, then
    after evolving each for `u` generations they agree at every point `q` of the
    smaller cone of radius `2*t` around `p`. -/
theorem evolve_cone_agree (t u : Nat) (g₁ g₂ : Grid) (p q : Int × Int)
    (h_cone : ∀ r ∈ lightCone p (2 * (t + u)), isAlive g₁ r = isAlive g₂ r)
    (hq : q ∈ lightCone p (2 * t)) :
    isAlive (evolve u g₁) q = isAlive (evolve u g₂) q := by
  -- `q` sits in `lightCone p (2*t)`. Apply `step_light_cone u` at `q`: it
  -- requires `g₁ g₂` to agree on `lightCone q (2*u)`. For any `r` in that cone,
  -- `manhattan q r ≤ 2*u` and `manhattan p q ≤ 2*t`, so `manhattan p r ≤ 2*(t+u)`
  -- by the triangle inequality, i.e. `r ∈ lightCone p (2*(t+u))`.
  apply step_light_cone u g₁ g₂ q
  intro r hr
  apply h_cone r
  apply mem_lightCone_of_manhattan_le
  have hpq : manhattan p q ≤ 2 * t := manhattan_le_of_mem_lightCone p q (2 * t) hq
  have hqr : manhattan q r ≤ 2 * u := manhattan_le_of_mem_lightCone q r (2 * u) hr
  have htri : manhattan p r ≤ manhattan p q + manhattan q r := manhattan_triangle p q r
  omega

/-! ## P4.4 sub-cell coverage (S3)

The super-cell `c` of level `k+2` decomposes into four quadrants
`c.nw, c.ne, c.sw, c.se`, each a MacroCell of level `k+1`. For any point
`p` in the central `2^k × 2^k` window of `c.toGrid (0, 0)`, the evolution
of `c.toGrid (0, 0)` for `2^(k-1)` steps at `p` depends only on the cells
within Manhattan distance `2^k` of `p` (by `step_light_cone (2^(k-1))`).
If a chosen quadrant `q_j` agrees with `c.toGrid (0, 0)` on that light
cone, then the two evolutions agree at `p`. The bridge from `c.toGrid`
to `q_j.toGrid` uses `toGrid_shift_between` (L1389-1398) on the quadrant
offset `(2^k, 0)` / `(0, 2^k)` / `(2^k, 2^k)`; this is the same offset-
matching pattern that `p4_succ_membership` and `centralCorrect_mem`
already exploit.

This is the S3 sub-sorry of `hashlife_correctN` (carte #6724): once we
have `centralCorrect q_j (k-1)` for the four quadrants (P4.3, via
`p4_wave2_ih`), S4 (ai-01 turf) glues them with `quad_partition_bounds`
to assemble `hashlifeResultAux (k+2) c` against `evolve (2^k) (c.toGrid)`. -/

/-- **Sub-cell coverage (S3)**: for any MacroCell `c` and any one of its
    four quadrants `q_j`, if `c.toGrid (0, 0)` and `q_j.toGrid (0, 0)`
    agree on `lightCone p (2^k)` (where `p` lies in the central window of
    `c.toGrid`), then the two evolutions for `2^(k-1)` steps agree at `p`.

    Direct instance of `step_light_cone (2^(k-1))`: the cone-of-dependence
    for `2^(k-1)` steps at `p` is `lightCone p (2 * 2^(k-1))`, which equals
    `lightCone p (2^k)` since `k ≥ 1` (`2 * 2^(k-1) = 2^k`) — i.e. the
    agreement hypothesis. The only bridge is that radius coincidence; no
    strengthening, no appeal to `evolve_cone_agree`.

    This lemma is the S3 sub-sorry of the P4 HashlifeCorrectness proof.
    It is independent of `p4_double_nine_shape` (P4.1) and `p4_wave1_ih`
    (P4.2): any quadrant works, so S4 (ai-01) instantiates it on the
    four `q_*` from `p4_double_nine_shape` once `centralCorrect q_* (k-1)`
    is in scope. -/
theorem quadrant_cone_agree (c : MacroCell) (k : Nat) (hk : 1 ≤ k)
    (p : Int × Int) (q_j : MacroCell)
    (h_agree : ∀ r ∈ lightCone p (2^k), isAlive (c.toGrid (0, 0)) r =
                                          isAlive (q_j.toGrid (0, 0)) r) :
    isAlive (evolve (2^(k-1)) (c.toGrid (0, 0))) p =
      isAlive (evolve (2^(k-1)) (q_j.toGrid (0, 0))) p := by
  -- step_light_cone (2^(k-1)) requires agreement on `lightCone p (2 * 2^(k-1))`.
  -- Bridge the cone radius: `2 * 2^(k-1) = 2^k` since `k ≥ 1` (`hk`), so the
  -- agreement hypothesis `h_agree` (stated on `lightCone p (2^k)`) discharges it.
  have h2k : 2 * 2^(k-1) = 2^k := by
    have hkey : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hkey, pow_succ]
    ring
  apply step_light_cone (2 ^ (k - 1)) (c.toGrid (0, 0)) (q_j.toGrid (0, 0)) p
  intro r hr
  rw [h2k] at hr
  exact h_agree r hr

/-! ## P2 corollary. Influence cone (light cone of influence)

`step_light_cone` is the **cone of dependence**: to know the state of `p`
after `t` generations, it suffices to know the cells of `g` within Manhattan
distance `2*t` of `p`. Its contrapositive is the **cone of influence**: a live
cell of `g` outside Manhattan distance `2*t` of `p` cannot make `p` live at
generation `t`. Equivalently, if `p` is live after `t` generations, some live
cell of `g` must lie within Manhattan distance `2*t` — the live region can
expand toward the MacroCell boundary by at most `2*t` per `t` generations.

This is the sorry-free, P4-independent geometric fact underpinning the
`BoxAssezGrand`-preservation argument for P5.2 (the recursion's padding
hypothesis is preserved because the jump of `jumpSize` generations expands the
live region by at most `2*jumpSize`, within the margin `n`). -/

/-- `isAlive` on the empty grid is always `false` (no cell is live). -/
theorem isAlive_empty (p : Int × Int) : isAlive ([] : Grid) p = false := by
  simp [isAlive]

/-- `sortDedup` of the empty list is empty (empty `insertionSort`, empty `dedup`). -/
theorem sortDedup_nil : sortDedup ([] : List (Int × Int)) = [] := by
  simp [sortDedup]

/-- The empty grid is a fixed point of `step` (no live cells → no births). -/
theorem step_empty : step ([] : Grid) = [] := by
  simp [step, candidates, sortDedup_nil]

/-- `evolve` of the empty grid is empty (the fixed point iterated). -/
theorem evolve_empty (t : Nat) : evolve t ([] : Grid) = [] := by
  induction t with
  | zero => simp [evolve_zero]
  | succ k ih => simp [evolve_succ, step_empty, ih]

/-- **Influence cone (contrapositive form)**: if no live cell of `g` lies in
    `lightCone p (2*t)`, then `evolve t g` is dead at `p`. Proof: `g` then
    agrees with the empty grid on the cone, so `step_light_cone` equates
    `evolve t g` to `evolve t ∅` (which is dead everywhere) at `p`.

    This is the directly-usable form for the `BoxAssezGrand`-preservation
    argument: outside the live region (margin ≥ `n`), the cone is all-dead, so
    `evolve t` cannot bring a boundary cell to life within `t < n/2` generations. -/
theorem evolve_dead_of_cone_dead (t : Nat) (g : Grid) (p : Int × Int)
    (h : ∀ q ∈ lightCone p (2 * t), isAlive g q = false) :
    isAlive (evolve t g) p = false := by
  have hagree : ∀ q ∈ lightCone p (2 * t),
      isAlive g q = isAlive ([] : Grid) q := by
    intro q hq
    rw [h q hq, isAlive_empty]
  have heq := step_light_cone t g ([] : Grid) p hagree
  rw [heq, evolve_empty, isAlive_empty]

end Life
end Conway
