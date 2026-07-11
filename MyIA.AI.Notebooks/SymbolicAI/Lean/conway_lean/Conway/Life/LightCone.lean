/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Light-cone geometry (Conway Game of Life)

Sorry-free geometric lemmas about `manhattan` and `lightCone` (defined in
`Conway.Life.HashlifeCorrectness`). These bridge facts make the light-cone
machinery composable: they are NOT new locality results (the fundamental
locality theorem `step_light_cone` is proven in `HashlifeCorrectness`), but
the elementary set/arithmetic relationships between cones of different radii
and between Manhattan and per-coordinate bounds, which future correctness
proofs chain across the `evolve` recursion.

The central fact formalized here is the **Game-of-Life speed-of-light
principle** (commented in `HashlifeCorrectness` P2 §, L497-504, but not
previously stated as a theorem): over `t` generations information travels at
Chebyshev radius `t` (one Moore-neighborhood step per generation), and the
Chebyshev ball of radius `t` is contained in the Manhattan ball of radius
`2*t` (the corner cell `(p.1 ± t, p.2 ± t)` is at Manhattan distance `2*t`).
This containment is exactly why `step_light_cone` demands agreement on
`lightCone p (2 * t)` — that radius is the *tight* GoL influence bound, not a
loose over-approximation.

Epic #3846 (Hashlife correctness infrastructure). All `sorry`s eliminated at
creation.
-/

import Conway.Life.HashlifeCorrectness

namespace Conway
namespace Life

/-! ## Monotonicity: larger radius → larger cone

A light cone of radius `t₁` is contained in the light cone of any larger
radius `t₂ ≥ t₁`. This follows directly from the membership characterization
(`mem_lightCone_of_manhattan_le` / `manhattan_le_of_mem_lightCone`): a cell in
the smaller cone is at Manhattan distance `≤ t₁ ≤ t₂`, hence in the larger
cone. -/
theorem lightCone_subset_of_le (p : Int × Int) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    lightCone p t₁ ⊆ lightCone p t₂ := by
  intro q hq
  exact mem_lightCone_of_manhattan_le p q t₂
    ((manhattan_le_of_mem_lightCone p q t₁ hq).trans h)

/-! ## Per-coordinate bound: membership bounds each coordinate

A cell in `lightCone p t` has each coordinate within `t` of `p`'s
corresponding coordinate. This is the "Manhattan-`t` ⊆ Chebyshev-`t`"
direction (each coordinate's displacement is bounded by the total Manhattan
distance). -/
theorem coord_bound_of_mem_lightCone (p q : Int × Int) (t : Nat)
    (h : q ∈ lightCone p t) :
    Int.natAbs (p.1 - q.1) ≤ t ∧ Int.natAbs (p.2 - q.2) ≤ t := by
  have hm : manhattan p q ≤ t := manhattan_le_of_mem_lightCone p q t h
  unfold manhattan at hm
  refine ⟨?_, ?_⟩ <;> omega

/-! ## Speed-of-light principle: Chebyshev-`t` ⊆ Manhattan-`2*t`

The converse direction that makes `2*t` the **tight** GoL radius. If each
coordinate of `q` is within `t` of `p` (Chebyshev distance `≤ t`) — the exact
region a single B3/S23 step can reach in one generation, lifted to `t` steps
— then the Manhattan distance is `≤ 2*t`, so `q ∈ lightCone p (2 * t)`.

This is the formal justification for `step_light_cone`'s `2 * t` radius: the
Moore-neighborhood influence of one generation has Chebyshev radius `1`, so
`t` generations reach Chebyshev radius `t`, and that Chebyshev ball is
contained in the Manhattan ball of twice the radius. The factor `2` is
tight (the diagonal neighbor is at Manhattan distance `2`). -/
theorem mem_lightCone_of_chebyshev_le (p q : Int × Int) (t : Nat)
    (h1 : Int.natAbs (p.1 - q.1) ≤ t) (h2 : Int.natAbs (p.2 - q.2) ≤ t) :
    q ∈ lightCone p (2 * t) := by
  apply mem_lightCone_of_manhattan_le p q (2 * t)
  unfold manhattan
  omega

/-! ## Translation invariance: shifting the center shifts the cone

The light cone is translation-equivariant: membership of `q` in `lightCone p t`
depends only on the displacement `q - p`, not on the absolute position `p`. This
is the Grid-level counterpart of the `toGrid` offset-shift machinery in
`HashlifeCorrectness` (`toGrid_shift`, `toGrid_shift_between`), and is the
structural fact needed to relate the light cone before and after a `hashlifeJump`
shifts the grid by `jumpResultOff` in `evolveHashlifeFastAux`. The cone is an
isometry of the Manhattan metric, so its shape is preserved under translation. -/
theorem lightCone_translate (p q : Int × Int) (t : Nat) :
    q ∈ lightCone p t ↔ (q.1 - p.1, q.2 - p.2) ∈ lightCone (0, 0) t := by
  constructor
  · intro h
    apply mem_lightCone_of_manhattan_le (0, 0) _ t
    have hm := manhattan_le_of_mem_lightCone p q t h
    unfold manhattan at *; omega
  · intro h
    apply mem_lightCone_of_manhattan_le p q t
    have hm := manhattan_le_of_mem_lightCone (0, 0) _ t h
    unfold manhattan at *; omega

/-! ## Chebyshev (chessboard) distance and the tight locality cone

The *tight* Game-of-Life locality is governed by the Chebyshev (L∞) distance:
one B3/S23 generation reaches exactly the Moore neighborhood (Chebyshev radius
1), so `t` generations reach Chebyshev radius `t`. The `lightCone` machinery
above uses the Manhattan (L1) distance, which over-approximates the tight reach
by a factor of 2 — `step_light_cone` demands Manhattan radius `2 * t`. The
lemmas below formalize the Chebyshev cone structure that a *tight* single-jump
correctness proof chains through:

- the cone fits in a margin-`t` box (**margin sufficiency** — the geometric fact
  that makes the `padCenter2` margin `2^k` sufficient for a single jump of `2^k`
  generations: the tight Chebyshev reach `2^k` fits exactly in a margin-`2^k`
  box, whereas the loose Manhattan-`2^k` light cone would need `2^(k+1)`); and
- the tight cone is contained in the loose Manhattan-`2*t` light cone.

These are the elementary distance facts; they do not yet assert anything about
`evolve` (the locality statement `step_light_cone` lives in `HashlifeCorrectness`).
Epic #3846 (Hashlife correctness infrastructure, N2 tight-locality groundwork). -/

/-- Chebyshev (chessboard / L∞) distance between two cells: the larger of the
    absolute coordinate displacements. -/
def chebDist (p q : Int × Int) : Nat :=
  max (Int.natAbs (q.1 - p.1)) (Int.natAbs (q.2 - p.2))

/-- Reflexivity: a cell is at Chebyshev distance 0 from itself. -/
theorem chebDist_self (p : Int × Int) : chebDist p p = 0 := by
  unfold chebDist; omega

/-- Symmetry: the Chebyshev distance is invariant under swapping the two cells. -/
theorem chebDist_comm (p q : Int × Int) : chebDist p q = chebDist q p := by
  unfold chebDist; omega

/-- Monotonicity in the radius: a larger radius weakly contains the cone. -/
theorem chebDist_le_trans {t₁ t₂ : Nat} (h : t₁ ≤ t₂) {p q : Int × Int}
    (hd : chebDist p q ≤ t₁) : chebDist p q ≤ t₂ := hd.trans h

/-- Margin sufficiency: a cell within Chebyshev radius `t` of `p` lies in the
    margin-`t` box — each coordinate is within `t` of `p`'s coordinate. This is
    the geometric reason a box margin of `t` (e.g. `padCenter2`'s `2^k` margin
    at a level advancing `2^k` generations) covers the *tight* Chebyshev-`t`
    reach, even though that same margin `t` does not cover the *loose*
    Manhattan-`t` light cone (which reaches `2 * t`). -/
theorem coord_bound_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) :
    Int.natAbs (q.1 - p.1) ≤ t ∧ Int.natAbs (q.2 - p.2) ≤ t := by
  unfold chebDist at h
  omega

/-- Tight ⊆ loose (distance form): Chebyshev radius `t` is bounded by Manhattan
    radius `2 * t`, because each coordinate displacement is `≤ t` and the
    Manhattan distance is their sum. -/
theorem manhattan_le_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : manhattan p q ≤ 2 * t := by
  unfold chebDist at h
  unfold manhattan
  omega

/-- A cell within Chebyshev radius `t` lies in the Manhattan-`(2*t)` light cone.
    This is the bridge from the tight Chebyshev reach to the loose
    `lightCone p (2 * t)` radius that `step_light_cone` operates on. -/
theorem mem_lightCone_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : q ∈ lightCone p (2 * t) :=
  mem_lightCone_of_manhattan_le p q (2 * t) (manhattan_le_of_chebDist_le p q t h)

/-! ## Chebyshev triangle inequality and cone growth by a Moore step

The foundational metric fact (`chebDist_triangle`) and the **tight-cone growth
theorem** named by ai-01's N2 greenlight: a cell lies in the Chebyshev-`(t+1)`
cone of `p` iff one can reach it from the Chebyshev-`t` cone via a single Moore
neighborhood step. This is the inductive engine of the tight-locality statement
(after one B3/S23 generation, reach expands by exactly one Moore shell), and the
reason the tight Chebyshev reach grows linearly with `t` rather than as `2*t`.
-/

/-- Triangle inequality for the Chebyshev distance. -/
theorem chebDist_triangle (p q r : Int × Int) :
    chebDist p q ≤ chebDist p r + chebDist r q := by
  unfold chebDist
  omega

/-- The Chebyshev cone grows by exactly one Moore step: `q` is within Chebyshev
    radius `t+1` of `p` iff there is a cell `r` within Chebyshev radius `t` of `p`
    that is a Moore neighbor of `q` (Chebyshev radius `≤ 1`). Forward direction
    steps from `q` toward `p` by one unit in each nonzero coordinate; backward
    direction is the triangle inequality. This is the additive-growth lemma that
    underpins the tight `t`-step locality (one Moore shell per generation). -/
theorem chebDist_le_succ_iff (p q : Int × Int) (t : Nat) :
    chebDist p q ≤ t + 1 ↔
      ∃ r : Int × Int, chebDist p r ≤ t ∧ chebDist r q ≤ 1 := by
  constructor
  · -- forward: step from `q` toward `p` by one unit in each nonzero coordinate
    intro h
    unfold chebDist at h
    refine ⟨(q.1 - if q.1 - p.1 = 0 then 0 else if 0 < q.1 - p.1 then 1 else -1,
             q.2 - if q.2 - p.2 = 0 then 0 else if 0 < q.2 - p.2 then 1 else -1), ?_, ?_⟩
    all_goals unfold chebDist; omega
  · -- backward: triangle inequality
    rintro ⟨r, hr, hq⟩
    exact (chebDist_triangle p q r).trans (add_le_add hr hq)

/-- The tight Chebyshev cone is nested in its successor: radius `t` ⊆ radius
    `t+1`. Corollary of `chebDist_le_succ_iff` (or directly `Nat.le_succ`). -/
theorem chebDist_le_succ (p q : Int × Int) (t : Nat) (h : chebDist p q ≤ t) :
    chebDist p q ≤ t + 1 := h.trans (Nat.le_succ t)

/-! ## Tight Chebyshev reach — the Game-of-Life speed of light

The fundamental TIGHT locality result, stated as a *reach* theorem: after `t`
generations, a cell alive at `evolve t g` lies within Chebyshev distance `t` of
some initially alive cell of `g`. This is the speed-of-light bound — strictly
sharper than the Manhattan-`2*t` light cone demanded by `step_light_cone`. It
wires the set-level growth (`chebDist_le_succ_iff`, one Moore shell adds
Chebyshev-1) into the B3/S23 semantics: `candidates g = g ++ g.flatMap
mooreNeighbors` is exactly the Chebyshev-1 dilation of the alive set, so each
`step` grows the reachable region by exactly one Moore shell. Epic #3846, N2
step 2. Sorry-free. -/

/-- Bridge between `isAlive` (Boolean membership) and List membership. -/
theorem isAlive_true_iff_mem (g : Grid) (p : Int × Int) :
    isAlive g p = true ↔ p ∈ g := by
  rw [isAlive]; exact List.elem_iff

/-- A Moore neighbor of `p` is at Chebyshev distance at most 1 — the tight
    bound (vs `manhattan_moore_le_two`'s loose `≤ 2`). -/
theorem chebDist_le_one_of_moore (p q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : chebDist p q ≤ 1 := by
  unfold chebDist mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · simp at h

/-- **Tight GoL speed of light (reach form).** If `q` is alive after `t`
    generations of evolution from `g`, then `q` is within Chebyshev radius `t`
    of some initially-alive cell of `g`.

    Proof by induction on `t`:
    - Base `t = 0`: `evolve 0 g = g`, witness `p = q`, `chebDist q q = 0`.
    - Step `t = n + 1`: `isAlive (evolve (n+1) g) q = aliveNext (evolve n g) q`
      (by `isAlive_step_eq_aliveNext`), and `aliveNext … = true` puts
      `q ∈ candidates (evolve n g)`. Membership splits (`List.mem_append`) into:
      (a) `q ∈ evolve n g` — `q` alive at gen `n`, so the IH gives a witness
      within `chebDist ≤ n ≤ n+1`; or (b) `q ∈ (evolve n g).flatMap mooreNeighbors`
      — some `r` alive at gen `n` with `q ∈ mooreNeighbors r`, so the IH gives a
      witness within `chebDist p r ≤ n`, `chebDist_le_one_of_moore` gives
      `chebDist r q ≤ 1`, and the triangle inequality yields `≤ n+1`. -/
theorem evolve_reach_chebyshev (t : Nat) (g : Grid) (q : Int × Int)
    (h_alive : isAlive (evolve t g) q = true) :
    ∃ p, isAlive g p = true ∧ chebDist p q ≤ t := by
  induction t generalizing q with
  | zero =>
    simp only [evolve_zero] at h_alive
    exact ⟨q, h_alive, (chebDist_self q).le⟩
  | succ n ih =>
    simp only [evolve_succ] at h_alive
    rw [isAlive_step_eq_aliveNext] at h_alive
    have hmem : q ∈ candidates (evolve n g) :=
      aliveNext_true_mem_candidates (evolve n g) q h_alive
    unfold candidates at hmem
    rw [List.mem_append] at hmem
    rcases hmem with h_self | h_nbr
    · -- (a) q alive at gen n: IH directly
      have hq : isAlive (evolve n g) q = true :=
        (isAlive_true_iff_mem (evolve n g) q).mpr h_self
      obtain ⟨p, hp, hcheb⟩ := ih q hq
      exact ⟨p, hp, hcheb.trans (Nat.le_succ n)⟩
    · -- (b) q is a Moore neighbor of some r alive at gen n
      rw [List.mem_flatMap] at h_nbr
      obtain ⟨r, hr_mem, hrq⟩ := h_nbr
      have hr : isAlive (evolve n g) r = true :=
        (isAlive_true_iff_mem (evolve n g) r).mpr hr_mem
      obtain ⟨p, hp, hpr⟩ := ih r hr
      refine ⟨p, hp, ?_⟩
      have hrq_cheb : chebDist r q ≤ 1 := chebDist_le_one_of_moore r q hrq
      exact (chebDist_triangle p q r).trans (add_le_add hpr hrq_cheb)

/-! ## N2 step 3 capstone: tight Chebyshev reach ⊆ padCenter2 margin

Composing the tight reach theorem (`evolve_reach_chebyshev`, one Moore shell
per generation) with the margin-arithmetic lemma
(`padCenter2_margin_ge_jumpReach`, `2^k ≤ 3·2^(k-1)`, proven in
`HashlifeCorrectness` L1102) yields the full sorry-free bridge named by ai-01's
N2 greenlight: for a level-`k ≥ 1` MacroCell, a `2^k`-generation jump (the
Hashlife `jumpSize k = 2^k`) reaches only cells within the per-side `padCenter2`
margin `3·2^(k-1)` of some initially-alive cell. The **tight** Chebyshev-`2^k`
reach — not the loose Manhattan-`2^(k+1)` cone — is what makes the `2^k` margin
sufficient with 50% headroom (the diagonal of the reach is `2^k`, the margin is
`3·2^(k-1) = 1.5·2^k`).

Evaluation of the three MacroCell-layer ingredients ai-01 flagged (these govern
the eventual wire into `p5_large_n_jump`, which remains P4-gated and out of
scope here):
- `padCenter2 c = padToLevelPlus1 (padToLevelPlus1 c)` (`Hashlife.lean` L260):
  lifts a level-`k` cell into a level-`(k+2)` frame of side `2^(k+2) = 4·2^k`,
  giving per-side margin `(4·2^k − 2^k)/2 = 3·2^(k-1)`.
- `level_padCenter2` (`HashlifeCorrectness` L1638): `(padCenter2 c).level =
  c.level + 2` — the level companion certifying the frame lift.
- `hashlifeResult_central_correct` (`HashlifeCorrectness` L2753): the P4
  decompose-compose theorem; its `succ` arm carries one of the two residual
  sorries (L2734), so the MacroCell offset-wire is blocked on the P4 inductive
  step (`p4_succ_membership`).

This capstone is the **Grid-level / set-distance half** of the bridge — proved
from already-sorry-free ingredients, so it is itself sorry-free and additive
(anti-regression §D: the two residual sorries of `HashlifeCorrectness` are
untouched). EPIC #3846, N2 step 3. -/

/-- **Reach ⊆ padCenter2 margin** (N2 step 3, sorry-free capstone).
    After `2^k` generations of evolution, every alive cell `q` has each
    coordinate within the `padCenter2` per-side margin `3·2^(k-1)` of some
    initially-alive cell `p`. This composes the tight Chebyshev reach
    (`evolve_reach_chebyshev`, giving `chebDist p q ≤ 2^k`), the per-coordinate
    bound (`coord_bound_of_chebDist_le`, giving `|q.i − p.i| ≤ 2^k`), and the
    margin arithmetic (`padCenter2_margin_ge_jumpReach`, `2^k ≤ 3·2^(k-1)`). -/
theorem evolve_reach_within_padCenter2_margin (k : Nat) (hk : 1 ≤ k)
    (g : Grid) (q : Int × Int)
    (h_alive : isAlive (evolve ((2 : Nat)^k) g) q = true) :
    ∃ p : Int × Int,
      isAlive g p = true ∧
      Int.natAbs (q.1 - p.1) ≤ 3 * (2 : Nat)^(k - 1) ∧
      Int.natAbs (q.2 - p.2) ≤ 3 * (2 : Nat)^(k - 1) := by
  obtain ⟨p, hp, hcheb⟩ := evolve_reach_chebyshev ((2 : Nat)^k) g q h_alive
  have ⟨hb1, hb2⟩ := coord_bound_of_chebDist_le p q ((2 : Nat)^k) hcheb
  have hmargin := padCenter2_margin_ge_jumpReach k hk
  exact ⟨p, hp, hb1.trans hmargin, hb2.trans hmargin⟩

/-! ## W3 tight cone-in-domain: Chebyshev-tight locality stays in the domain

The tight Chebyshev analog of `window_cone_in_domain` (the **S2** closed lemma in
`HashlifeCorrectness`, which used the *loose* Manhattan cone `manhattan p q ≤ 2^k`).
For a point `p` in the centered window `[2^k, 2^k + 2^(k+1))²` (the region a
Hashlife result covers), any cell `q` within **Chebyshev** radius `2^k` — the
*tight* GoL speed-of-light cone, strictly smaller than the loose Manhattan-`2^k`
cone (a Chebyshev-`t` ball fits in a Manhattan-`2t` ball, not the reverse) — stays
inside the full MacroCell domain `[0, 2^(k+2))²`.

This is the missing tight locality bound for the N2 redesign arc (EPIC #3846, W3).
The loose `window_cone_in_domain` demanded Manhattan-`2^k` agreement, over-
approximating the real reach by a factor of 2; the tight version demands only
Chebyshev-`2^k` agreement (the actual one-Moore-shell-per-generation reach
formalized by `evolve_reach_chebyshev`). Because Chebyshev distance bounds each
coordinate directly, the proof is **simpler** than the loose analog: it consumes
`coord_bound_of_chebDist_le` (per-coordinate bound immediately) rather than
bridging through `manhattan_deviation`. No `hashlifeResultAux`, no whnf wall —
pure `Int` window arithmetic. Sorry-free.

Wiring note (architectural): `LightCone` imports `HashlifeCorrectness`, so the
reverse import needed for the P5 `p5_large_n_jump` path to consume this lemma is
**circular** as-is. The lemma is stated over plain `Int × Int` precisely so it can
be extracted to a shared geometry module when the P5 wire is done (a dependency-
cycle break = architectural step, ai-01's call). The proof substance is delivered
here, independent of the P4 mono-verrou. -/
theorem window_cheb_cone_in_domain (k : Nat) (p q : Int × Int)
    (hp1_lo : (2^k : Int) ≤ p.1) (hp1_hi : p.1 < 2^k + 2^(k+1))
    (hp2_lo : (2^k : Int) ≤ p.2) (hp2_hi : p.2 < 2^k + 2^(k+1))
    (hc : chebDist p q ≤ 2^k) :
    (0 : Int) ≤ q.1 ∧ q.1 < 2^(k+2) ∧ (0 : Int) ≤ q.2 ∧ q.2 < 2^(k+2) := by
  -- Chebyshev radius bounds each coordinate directly (no manhattan bridge).
  obtain ⟨hq1, hq2⟩ := coord_bound_of_chebDist_le p q (2^k) hc
  -- `coord_bound_of_chebDist_le` types its bounds as `Nat` (`Int.natAbs ... ≤
  -- 2^k`); the window hypotheses below use native-Int `(2^k : Int)` (`HPower`).
  -- Bridge the Nat-bound to an `Int.abs`-typed bound (mirroring the loose
  -- analog's `manhattan_deviation` output, which is already Int-typed), then
  -- unify the atoms via `Nat.cast_pow`.
  have hk_pow : (↑((2:Nat)^k) : Int) = (2^k : Int) := Nat.cast_pow 2 k
  have hq1' : |q.1 - p.1| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq1
  have hq2' : |q.2 - p.2| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq2
  -- Power facts in pure `Nat`, lifted to `Int` (linarith reads the atoms).
  have hpe1 : (2^(k+1) : Int) = 2 * (2^k : Int) := by
    have h : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    exact_mod_cast h
  have hpe2 : (2^(k+2) : Int) = 4 * (2^k : Int) := by
    have h1 : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    have h2 : (2 : Nat)^(k+2) = 2 * (2 : Nat)^(k+1) := by
      rw [show (k + 2 : Nat) = Nat.succ (k + 1) from rfl, Nat.pow_succ, Nat.mul_comm]
    have h : (2 : Nat)^(k+2) = 4 * (2 : Nat)^k := by rw [h2, h1]; ring
    exact_mod_cast h
  -- `Int.abs` bound unpacked into a two-sided `Int` clamp on `q.i - p.i`.
  obtain ⟨hq1lo, hq1hi⟩ := abs_le.mp hq1'
  obtain ⟨hq2lo, hq2hi⟩ := abs_le.mp hq2'
  -- Rewrite every power occurrence into a multiple of the single atom `2^k`.
  rw [hpe1] at hp1_hi hp2_hi
  rw [hpe2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
