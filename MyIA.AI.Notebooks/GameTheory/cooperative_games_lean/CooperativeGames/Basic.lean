/-
  Cooperative Game Theory - Basic Definitions
  ===========================================

  This file formalizes the basic concepts of cooperative game theory:
  - TU Games (Transferable Utility Games)
  - Coalitions and characteristic functions
  - Superadditivity and convexity properties
  - The Core of a game

  Reference: L.S. Shapley, "A Value for N-Person Games" (1953)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! ## Basic Types -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## TU Games -/

/-- A coalition is a subset of players -/
abbrev Coalition (N : Type*) := Finset N

/-- A TU (Transferable Utility) Game consists of a characteristic function v
    mapping coalitions to real values, with v(∅) = 0 -/
@[ext]
structure TUGame (N : Type*) [Fintype N] where
  /-- The characteristic function: value of each coalition -/
  v : Finset N → ℝ
  /-- The empty coalition has value 0 -/
  empty_zero : v ∅ = 0

namespace TUGame

variable (G : TUGame N)

/-! ## Structural Properties -/

/-- A game is superadditive if cooperation is beneficial:
    v(S ∪ T) ≥ v(S) + v(T) for disjoint S, T -/
def Superadditive : Prop :=
  ∀ S T : Finset N, Disjoint S T →
    G.v (S ∪ T) ≥ G.v S + G.v T

/-- A game is convex (supermodular) if marginal contributions increase:
    v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T) for S ⊆ T, i ∉ T -/
def Convex : Prop :=
  ∀ S T : Finset N, ∀ i : N,
    S ⊆ T → i ∉ T →
    G.v (S ∪ {i}) - G.v S ≤ G.v (T ∪ {i}) - G.v T

/-- Marginal contribution of player i to coalition S -/
def marginalContribution (i : N) (S : Finset N) : ℝ :=
  G.v (S ∪ {i}) - G.v S

/-! ## Classic Examples -/

/-- The unanimity game for coalition T (non-empty):
    v(S) = 1 if T ⊆ S, else 0 -/
def unanimityGame (T : Finset N) (hT : T.Nonempty) : TUGame N where
  v := fun S => if T ⊆ S then 1 else 0
  empty_zero := by
    simp only [Finset.subset_empty]
    simp [hT.ne_empty]

/-- The majority game: v(S) = 1 if |S| > n/2, else 0 -/
def majorityGame : TUGame N where
  v := fun S => if 2 * S.card > Fintype.card N then 1 else 0
  empty_zero := by simp

/-! ## The Core -/

/-- An allocation is a function assigning payoffs to players -/
abbrev Allocation (N : Type*) := N → ℝ

/-- The Core: set of efficient and stable allocations -/
def Core : Set (Allocation N) :=
  { x |
    -- Efficiency: sum of payoffs equals v(N)
    (∑ i : N, x i = G.v Finset.univ) ∧
    -- Group rationality: no coalition can block
    (∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S) }

/-- The Core may be empty -/
def CoreEmpty : Prop := G.Core = ∅

/-! ## Balanced Games -/

/-- A balanced collection of weights -/
def BalancedWeights (weights : Finset N → ℝ) : Prop :=
  (∀ S, weights S ≥ 0) ∧
  (∀ i : N, ∑ S ∈ (Finset.univ.filter fun S => i ∈ S), weights S = 1)

/-- A game is balanced if every balanced collection satisfies the condition -/
def Balanced : Prop :=
  ∀ weights : Finset N → ℝ,
    BalancedWeights weights →
    ∑ S : Finset N, weights S * G.v S ≤ G.v Finset.univ

/-! ## Key Theorems -/

/-- Superadditive games have non-negative grand coalition value.
    Proof: by induction on coalitions, using superadditivity to decompose
    the grand coalition into singletons. Requires v({i}) ≥ 0 for each
    singleton, which follows from v(∅) = 0 and superadditivity of {i} with ∅.
    NOTE: The proof decomposes univ into singletons via superadditivity:
    v(univ) = v({i1} ∪ ... ∪ {in}) ≥ v({i1}) + ... + v({in}) ≥ 0.
    Each v({ik}) ≥ 0 because v({ik}) = v(∅ ∪ {ik}) ≥ v(∅) + v({ik}) = v({ik}),
    so v({ik}) ≥ v({ik}) is trivially true but doesn't give non-negativity.
    Actually: v({i}) = v({i} ∪ ∅) ≥ v({i}) + v(∅) = v({i}), trivially.
    The correct approach: from superadditivity, v(S ∪ T) ≥ v(S) + v(T).
    By repeated application: v(univ) ≥ ∑ᵢ v({i}). But we need v({i}) ≥ 0,
    which follows from: v({i}) ≥ v(∅) + v({i})... no, that gives v({i}) ≥ v({i}).
    KEY INSIGHT: From superadditivity with S = ∅, T = ∅: v(∅) ≥ 2·v(∅), so v(∅) ≤ 0.
    Combined with v(∅) = 0, this is consistent.
    For singletons: v({i}) can be anything. So the theorem as stated is actually
    FALSE without additional hypotheses. A counterexample: N = Fin 1, v(∅) = 0, v({0}) = -1.
    FIX: We prove the weaker statement that v(∅) ≥ 0 (trivial from empty_zero). -/
theorem superadditive_empty_nonneg (_h : G.Superadditive) :
    G.v ∅ ≥ 0 := by
  rw [G.empty_zero]

/-- For superadditive games where all singletons have non-negative value,
    the grand coalition has non-negative value. -/
theorem superadditive_grand_coalition_nonneg_of_nonneg_singletons
    (h : G.Superadditive) (hnn : ∀ i : N, G.v {i} ≥ 0) :
    G.v Finset.univ ≥ 0 := by
  -- Decompose univ into singletons via superadditivity
  have hsum : ∀ S : Finset N, G.v S ≥ ∑ i ∈ S, G.v ({i} : Finset N) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [G.empty_zero]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hsup : G.v (insert a S) ≥ G.v ({a} : Finset N) + G.v S := by
        rw [Finset.insert_eq]
        exact h {a} S (Finset.disjoint_singleton_left.mpr ha)
      linarith
  have h1 := hsum Finset.univ
  have h2 : (0 : ℝ) ≤ ∑ (i : N), G.v ({i} : Finset N) :=
    Finset.sum_nonneg (fun i _ => hnn i)
  linarith

/-- Forward direction of Bondareva-Shapley: Core nonempty implies balanced.
    Proof: Let x ∈ Core. For balanced weights w with ∑_{S∋i} w(S) = 1:
    ∑_S w(S)·v(S) ≤ ∑_S w(S)·(∑_{i∈S} x(i))   [group rationality]
                   = ∑_S ∑_{i∈S} w(S)·x(i)       [distributivity]
                   = ∑_i ∑_{S∋i} w(S)·x(i)       [Fubini double sum]
                   = ∑_i x(i)·∑_{S∋i} w(S)       [factor x(i)]
                   = ∑_i x(i)·1 = v(N)            [balanced + efficiency] -/
theorem bondareva_shapley_forward :
    G.Core.Nonempty → G.Balanced := by
  rintro ⟨x, ⟨hx_eff, hx_gr⟩⟩
  intro weights ⟨hw_pos, hw_bal⟩
  suffices h : ∑ S : Finset N, weights S * G.v S ≤ ∑ i : N, x i by rwa [hx_eff] at h
  -- Step 1: group rationality bound
  have h_gr : ∑ S : Finset N, weights S * G.v S ≤
      ∑ S : Finset N, weights S * (∑ i ∈ S, x i) :=
    Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (hx_gr S) (hw_pos S))
  -- Step 2: distribute weights into inner sum
  have h_dist : ∑ S : Finset N, weights S * (∑ i ∈ S, x i) =
      ∑ S : Finset N, ∑ i ∈ S, weights S * x i :=
    Finset.sum_congr rfl (fun S _ => by rw [Finset.mul_sum])
  -- Step 3: Fubini — swap order of double sum
  have h_fubini : ∑ S : Finset N, ∑ i ∈ S, weights S * x i =
      ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := by
    classical
    -- Extend inner sums to full type using indicator functions
    have h1 (S : Finset N) : ∑ i ∈ S, weights S * x i =
        ∑ i : N, (if i ∈ S then weights S * x i else 0) := by
      trans ∑ i ∈ S, (if i ∈ S then weights S * x i else 0)
      · exact Finset.sum_congr rfl (fun i hi => (if_pos hi).symm)
      · exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => if_neg hi)
    -- Swap summation order (Fubini for finite types)
    have h2 : ∑ S : Finset N, ∑ i : N, (if i ∈ S then weights S * x i else 0) =
        ∑ i : N, ∑ S : Finset N, (if i ∈ S then weights S * x i else 0) := by
      exact Finset.sum_comm
    -- Convert indicator sums back to filtered sums
    have h3 (i : N) : ∑ S : Finset N, (if i ∈ S then weights S * x i else 0) =
        ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := by
      exact (Finset.sum_filter (fun S => i ∈ S) (fun S => weights S * x i)).symm
    -- Chain the three steps
    rw [Finset.sum_congr rfl (fun S _ => h1 S), h2,
        Finset.sum_congr rfl (fun i _ => h3 i)]
  -- Step 4: factor x(i) out of each inner sum
  have h_factor : ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i =
      ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S :=
    Finset.sum_congr rfl (fun i _ => by
      rw [Finset.sum_congr rfl (fun S _ => mul_comm (weights S) (x i)),
          ← Finset.mul_sum])
  -- Step 5: apply balanced condition
  have h_bal : ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S =
      ∑ i : N, x i :=
    Finset.sum_congr rfl (fun i _ => by rw [hw_bal i, mul_one])
  -- Combine
  calc ∑ S : Finset N, weights S * G.v S
      ≤ ∑ S : Finset N, weights S * (∑ i ∈ S, x i) := h_gr
    _ = ∑ S : Finset N, ∑ i ∈ S, weights S * x i := h_dist
    _ = ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := h_fubini
    _ = ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S := h_factor
    _ = ∑ i : N, x i := h_bal

/-- Backward direction of Bondareva-Shapley: balanced implies Core nonempty.
    Strategy (v4.30 update): ProperCone.hyperplane_separation is now available
    via `Mathlib.Analysis.Convex.Cone.Dual`. It gives: given a proper cone C and
    compact convex K with K ∩ C = ∅, ∃ f, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0.
    Proof sketch:
    1. Assume balanced: ∀ weights, BalancedWeights weights → ∑_S w(S)·v(S) ≤ v(N).
    2. Define the polyhedral set P = { x : N → ℝ | ∀ S, ∑_{i∈S} xᵢ ≥ v(S) }.
    3. Define the ray R = { t · 1_N | t ∈ ℝ, t ≤ v(N) } (grand coalition values).
    4. Show P ∩ cone(R) is nonempty using balanced condition (contradiction approach):
       If P ∩ { x | ∑ᵢ xᵢ < v(N) } = ∅, apply hyperplane_separation to get a
       separating hyperplane witnessing an unbalanced weight system, contradicting
       the balanced hypothesis.
    5. Extract the Core allocation from the intersection point. -/
theorem bondareva_shapley_backward :
    G.Balanced → G.Core.Nonempty := by
  intro hb
  -- Work in the finite-dimensional real vector space N → ℝ.
  -- The feasible region: P = { x | ∀ S, ∑_{i∈S} xᵢ ≥ v(S) } (coalition constraints).
  -- We show P ∩ { x | ∑ᵢ xᵢ = v(N) } is nonempty via hyperplane separation.
  -- Step 1: Define the polyhedral constraint set P
  let P : Set (N → ℝ) := { x | ∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S }
  -- Step 2: Show P is convex (intersection of half-spaces, each convex)
  have hP_conv : _root_.Convex ℝ P := by
    -- PROVER TARGET: Show intersection of half-spaces is convex
    -- Each constraint S is a half-space { x | ∑_{i∈S} xᵢ ≥ v(S) } which is convex.
    -- Intersection of convex sets is convex.
    sorry
  -- Step 3: Show P is closed (intersection of closed half-spaces)
  have hP_closed : IsClosed P := by
    -- PROVER TARGET: Intersection of closed sets is closed
    -- Each half-space { x | ∑_{i∈S} xᵢ ≥ v(S) } is closed (continuous preimage of Ici).
    sorry
  -- Step 4: Show P is nonempty (take x = λ i. M where M = max_S v(S), then ∑_{i∈S} M ≥ v(S))
  have hP_nonempty : P.Nonempty := by
    -- PROVER TARGET: Construct a large enough constant allocation
    -- Let M = max_S v(S) (exists since Finset N is finite).
    -- Then x = fun _ => M satisfies ∑_{i∈S} M = S.card * M ≥ M ≥ v(S).
    sorry
  -- Step 5: Show P is bounded below (trivially, 0 as lower bound isn't enough,
  -- but P is bounded since ∑ᵢ xᵢ ≤ v(N) + C for some C, by balanced condition).
  -- In finite dimensions, closed + bounded below + bounded above = compact.
  -- Actually we need: the set { x ∈ P | ∑ᵢ xᵢ ≤ v(N) } is compact,
  -- or equivalently P ∩ { x | ∑ᵢ xᵢ < v(N) + 1 } is compact.
  -- Key: show that for x ∈ P, ∑ᵢ xᵢ ≥ v(N) (by summing over all singletons + grand coalition).
  -- Wait: we need ∑ᵢ xᵢ = v(N) for Core membership.
  -- Strategy: minimize ∑ᵢ xᵢ over P. Since P is closed and bounded below, minimum exists.
  -- If min ∑ᵢ xᵢ > v(N), apply hyperplane_separation.
  -- If min ∑ᵢ xᵢ = v(N), we have our Core allocation.
  -- The balanced condition ensures min ∑ᵢ xᵢ ≤ v(N).
  -- Step 6: Define the "below grand coalition" set
  let K : Set (N → ℝ) := { x ∈ P | (∑ i : N, x i) < G.v Finset.univ }
  -- Step 7: Show K is empty (balanced ⟹ min over P ≤ v(N))
  -- Equivalently: ∀ x ∈ P, v(N) ≤ ∑ᵢ xᵢ
  -- This follows from: if ∑ᵢ xᵢ < v(N) for some x ∈ P, the balanced condition
  -- gives a contradiction via Farkas/hyperplane_separation.
  have hK_empty : K = ∅ := by
    -- PROVER TARGET: Show no x ∈ P has ∑ᵢ xᵢ < v(N)
    -- By contradiction: assume x ∈ P with ∑ᵢ xᵢ < v(N).
    -- The balanced weights w(S) = ∑ᵢ xᵢ - ∑_{i∉S} xᵢ... actually this is the hard part.
    -- Use hyperplane_separation on the cone of balanced weight violations.
    sorry
  -- Step 8: Since K = ∅, there exists x ∈ P with ∑ᵢ xᵢ = v(N)
  -- (P is nonempty + closed + no element has sum < v(N) ⟹ some element has sum = v(N))
  have hCore : G.Core.Nonempty := by
    -- PROVER TARGET: Extract Core allocation from P \ K
    -- Since P ≠ ∅ and no x ∈ P has ∑ᵢ xᵢ < v(N), take any x ∈ P.
    -- By hK_empty, ∑ᵢ xᵢ ≥ v(N). If = v(N), done. If > v(N), need to adjust.
    -- Actually: by hP_nonempty get x ∈ P. By hK_empty, ∑ᵢ xᵢ ≥ v(N).
    -- If ∑ᵢ xᵢ = v(N), use ⟨x, rfl, hx.1⟩.
    -- If ∑ᵢ xᵢ > v(N), scale down: y = x - (∑ᵢ xᵢ - v(N))/n · 1 preserves coalition constraints?
    -- Actually scaling down might violate constraints. Better: use existence of minimum.
    sorry
  exact hCore

/-- Bondareva-Shapley: The Core is nonempty iff the game is balanced. -/
theorem bondareva_shapley :
    G.Core.Nonempty ↔ G.Balanced :=
  ⟨bondareva_shapley_forward G, bondareva_shapley_backward G⟩

/-! ## Marginal Vectors and Convex Core (Shapley 1971) -/

section MarginalVector

/-- A fixed enumeration of `N` via `Fintype.equivFin`. -/
noncomputable def enumIndex (i : N) : ℕ := (Fintype.equivFin N i).val

/-- The "prefix" coalition: all players whose enumeration index is `< k`. -/
noncomputable def prefixCoalition (k : ℕ) : Finset N :=
  Finset.univ.filter (fun i => enumIndex i < k)

private lemma prefixCoalition_zero : (prefixCoalition 0 : Finset N) = ∅ := by
  ext i; simp [prefixCoalition]

private lemma enumIndex_lt_card (i : N) : enumIndex i < Fintype.card N :=
  (Fintype.equivFin N i).isLt

private lemma prefixCoalition_full :
    (prefixCoalition (Fintype.card N) : Finset N) = Finset.univ := by
  ext i
  simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and,
             iff_true]
  exact enumIndex_lt_card i

private lemma enumIndex_injective : Function.Injective (enumIndex : N → ℕ) := by
  intro a b hab
  exact (Fintype.equivFin N).injective (Fin.ext hab)

variable (G : TUGame N)

/-- Marginal vector along the fixed enumeration. -/
noncomputable def marginalVector : Allocation N := fun i =>
  G.v (prefixCoalition (enumIndex i + 1)) - G.v (prefixCoalition (enumIndex i))

private lemma prefixCoalition_succ_eq (k : ℕ) (hk : k < Fintype.card N) :
    (prefixCoalition (k + 1) : Finset N) =
      prefixCoalition k ∪ {(Fintype.equivFin N).symm ⟨k, hk⟩} := by
  ext j
  simp only [prefixCoalition, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, Finset.mem_singleton, true_and]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · left; exact h
    · right
      have : (Fintype.equivFin N j) = ⟨k, hk⟩ := Fin.ext h
      have := congrArg (Fintype.equivFin N).symm this
      simpa using this
  · rintro (h | h)
    · exact Nat.lt_succ_of_lt h
    · subst h
      show enumIndex _ < k + 1
      unfold enumIndex; simp

/-- Telescoping: the marginal vector sums to v(N). -/
lemma marginalVector_efficient :
    ∑ i : N, G.marginalVector i = G.v Finset.univ := by
  have hreidx : ∑ i : N, G.marginalVector i =
      ∑ k : Fin (Fintype.card N), G.marginalVector ((Fintype.equivFin N).symm k) :=
    (Equiv.sum_comp (Fintype.equivFin N).symm G.marginalVector).symm
  rw [hreidx]
  have hterm : ∀ k : Fin (Fintype.card N),
      G.marginalVector ((Fintype.equivFin N).symm k) =
        G.v (prefixCoalition (k.val + 1)) - G.v (prefixCoalition k.val) := by
    intro k
    unfold marginalVector enumIndex
    simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hrange : ∑ k : Fin (Fintype.card N),
        (G.v (prefixCoalition (k.val + 1)) - G.v (prefixCoalition k.val)) =
      ∑ k ∈ Finset.range (Fintype.card N),
        (G.v (prefixCoalition (k + 1)) - G.v (prefixCoalition k)) := by
    rw [← Finset.sum_range fun k => G.v (prefixCoalition (k + 1)) - G.v (prefixCoalition k)]
  rw [hrange, Finset.sum_range_sub fun k => G.v (prefixCoalition k),
      prefixCoalition_zero, prefixCoalition_full, G.empty_zero]
  ring

private lemma sdiff_subset_prefix_of_max
    (S : Finset N) (i : N)
    (hmax : ∀ j ∈ S, enumIndex j ≤ enumIndex i) :
    S.erase i ⊆ prefixCoalition (enumIndex i) := by
  intro j hj
  rw [Finset.mem_erase] at hj
  obtain ⟨hji, hjS⟩ := hj
  simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_or_eq_of_le (hmax j hjS) with h | h
  · exact h
  · exact absurd (enumIndex_injective h) hji

/-- For convex games, the marginal vector dominates v(S) on every coalition. -/
lemma marginalVector_dominates (h : G.Convex) :
    ∀ S : Finset N, ∑ i ∈ S, G.marginalVector i ≥ G.v S := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hSempty : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hn)
      subst hSempty
      simp [G.empty_zero]
    · have hSne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hn)
      obtain ⟨i, hiS, hmax⟩ := S.exists_max_image enumIndex hSne
      set S' := S.erase i with hS'def
      have hS'card : S'.card = n - 1 := by
        rw [hS'def, Finset.card_erase_of_mem hiS, hcard]
      have hS'lt : S'.card < n := by rw [hS'card]; omega
      have hSinsert : S = insert i S' := by
        rw [hS'def, Finset.insert_erase hiS]
      have hi_notin : i ∉ S' := Finset.notMem_erase i S
      have ih' : ∑ j ∈ S', G.marginalVector j ≥ G.v S' :=
        ih S'.card hS'lt S' rfl
      have hSerase_sub : S' ⊆ prefixCoalition (enumIndex i) := by
        rw [hS'def]; exact sdiff_subset_prefix_of_max S i hmax
      have hi_notin_pref : i ∉ (prefixCoalition (enumIndex i) : Finset N) := by
        simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_irrefl _
      have hconv := h S' (prefixCoalition (enumIndex i)) i hSerase_sub hi_notin_pref
      have hi_idx_lt : enumIndex i < Fintype.card N := enumIndex_lt_card i
      have hpref_succ :
          (prefixCoalition (enumIndex i) ∪ {i} : Finset N) =
            prefixCoalition (enumIndex i + 1) := by
        have heq : (Fintype.equivFin N).symm ⟨enumIndex i, hi_idx_lt⟩ = i := by
          unfold enumIndex; simp
        rw [prefixCoalition_succ_eq (enumIndex i) hi_idx_lt, heq]
      have hmv_i : G.marginalVector i =
          G.v (prefixCoalition (enumIndex i) ∪ {i}) -
          G.v (prefixCoalition (enumIndex i)) := by
        unfold marginalVector; rw [hpref_succ]
      have hSeq : S' ∪ {i} = S := by
        rw [hSinsert, Finset.insert_eq, Finset.union_comm]
      have hkey : G.marginalVector i ≥ G.v S - G.v S' := by
        rw [hmv_i]
        have hcv : G.v (S' ∪ {i}) - G.v S' ≤
            G.v (prefixCoalition (enumIndex i) ∪ {i}) -
            G.v (prefixCoalition (enumIndex i)) := hconv
        rw [hSeq] at hcv
        linarith
      have hsumeq : ∑ j ∈ S, G.marginalVector j =
          G.marginalVector i + ∑ j ∈ S', G.marginalVector j := by
        rw [hSinsert, Finset.sum_insert hi_notin]
      rw [hsumeq]
      linarith

/-- For convex games, the marginal vector lies in the Core. -/
theorem marginalVector_mem_core (h : G.Convex) :
    G.marginalVector ∈ G.Core :=
  ⟨G.marginalVector_efficient, G.marginalVector_dominates h⟩

end MarginalVector

/-- For convex games, the Core is non-empty (Shapley 1971, "Cores of convex games").
    Direct constructive proof via marginal vectors: along any fixed enumeration of N,
    the marginal contribution vector lies in the Core when the game is convex. -/
theorem convex_core_nonempty (h : G.Convex) :
    G.Core.Nonempty :=
  ⟨G.marginalVector, G.marginalVector_mem_core h⟩

end TUGame
