import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import RepeatedGames.Stage_en
import RepeatedGames.Discounting_en
import RepeatedGames.GrimTrigger_en
import RepeatedGames.Folk_en

/-!
# Subgame perfection and the one-shot deviation principle

`GrimTrigger.lean` states the INCENTIVE condition of grim trigger
(`coopValue R δ ≥ deviateValue T P δ ↔ δ ≥ (T − R)/(T − P)`) and flags the
gap itself: without semantics for histories and strategy profiles, that
condition does not say the profile is a subgame-perfect equilibrium (SPE).
This module closes that gap.

## What is built

1. **Histories and strategies**: `Hist` is the list of joint actions already
   played (oldest first); a behavioural strategy `Strategy` reads the history
   and picks an action. `orbitAux` unfolds the successive histories;
   `contPayoff` is the discounted payoff from an arbitrary history — so it
   also evaluates subgames off the equilibrium path.

2. **One-shot deviation principle** (`oneShotDeviationPrinciple`): a profile
   is subgame-perfect as soon as no *one-shot* deviation (deviate at one
   history, then return to the profile) is profitable, **at every history**.

3. **Grim trigger is an SPE iff `δ ≥ (T − R)/(T − P)`** (`grim_isSPE_iff`),
   under `0 ≤ δ < 1`.

## The extra hypothesis, named

The one-shot deviation principle is not free. It requires that the gain from
a deviation dies out along the deviation orbit. Two hypotheses carry it, and
they appear **in the theorem signature**, not in a comment:

  **(H1) uniformly bounded stage payoffs** — `hK : ∀ a b, |u a b| ≤ K`.
  On a finite game it is automatic (`stagePayoff_abs_le`: four values), but it
  is still a hypothesis about the stage game, not a tautology. It is what
  gives `|V_h| ≤ K/(1 − δ)` for *every* history `h` (`abs_contPayoff_le`),
  hence a deviation gain uniformly bounded along the deviation orbit.

  **(H2) `δ < 1`** — it is what drives `δ^k · B` to `0`
  (`le_zero_of_forall_geometric_bound`), hence extinguishes the residual gain.

Without (H1) or (H2) the statement is false: a deviation can become
profitable only asymptotically. That is precisely the hypothesis
`GrimTrigger.lean` could not name, for lack of history semantics.

## The gain recursion, and why it is not an identity

The technical point that carries the whole module. Writing
`G(h) = OS(h) + δ·G(h')` would be false as an identity: the deviant profile
and the reference profile **do not stack the same joint action**, so their
payoffs do not decompose at the same successor. What is true — and
sufficient — is the **inequality** `G(h) ≤ δ·G(h')`, obtained by confronting
the first deviant move's gain with the non-profitability of the one-shot
deviation **at `h`**. The proof is `gainRow_le_step` / `gainCol_le_step`; the
identity `contPayoff_cons` they start from is purely algebraic.

## Why the game is parameterised by `u₁` and `u₂`

The theorem is stated for two abstract payoff tables `u₁ u₂` and two bounds
`K₁ K₂`, then instantiated on the Prisoner's Dilemma. This makes visible that
the principle depends on no property of the stage game beyond (H1).
-/

open scoped Topology
open Filter

namespace RepeatedGames_en
open PDAction

/-! ## Histories, strategies, orbits -/

/-- Finite history: the list of joint actions already played, oldest first. -/
abbrev Hist : Type := List (PDAction × PDAction)

/-- Behavioural strategy: what a player plays after a finite history. -/
abbrev Strategy : Type := Hist → PDAction

/-- The orbit: the sequence of histories met from `h` when both players follow
    `σ₁` and `σ₂`. Recursion on the number of steps; the history is a
    parameter that advances. -/
def orbitAux (σ₁ σ₂ : Strategy) : ℕ → Hist → Hist
  | 0, h => h
  | (n + 1), h => orbitAux σ₁ σ₂ n (h ++ [(σ₁ h, σ₂ h)])

/-- The joint action played at step `n` from history `h`. -/
def actionAt (σ₁ σ₂ : Strategy) (h : Hist) (n : ℕ) : PDAction × PDAction :=
  (σ₁ (orbitAux σ₁ σ₂ n h), σ₂ (orbitAux σ₁ σ₂ n h))

/-- Discounted payoff of a player with payoff table `u`, from history `h`: the
    subgame that starts at `h`. At `h = []` this is the payoff of the whole
    game. -/
noncomputable def contPayoff (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) : ℝ :=
  ∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2

/-! ## Orbit structure lemmas -/

lemma actionAt_zero (σ₁ σ₂ : Strategy) (h : Hist) :
    actionAt σ₁ σ₂ h 0 = (σ₁ h, σ₂ h) := rfl

lemma actionAt_succ (σ₁ σ₂ : Strategy) (h : Hist) (n : ℕ) :
    actionAt σ₁ σ₂ h (n + 1) = actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n := rfl

/-- Every orbit keeps the starting history as a prefix. -/
lemma orbitAux_exists_append (σ₁ σ₂ : Strategy) (n : ℕ) (h : Hist) :
    ∃ t : Hist, orbitAux σ₁ σ₂ n h = h ++ t := by
  induction n generalizing h with
  | zero => exact ⟨[], by simp [orbitAux]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (h ++ [(σ₁ h, σ₂ h)])
    exact ⟨(σ₁ h, σ₂ h) :: t, by rw [orbitAux, ht, List.append_assoc]; rfl⟩

/-- Corollary: an orbit is never shorter than its starting history. -/
lemma length_le_orbitAux (σ₁ σ₂ : Strategy) (n : ℕ) (h : Hist) :
    h.length ≤ (orbitAux σ₁ σ₂ n h).length := by
  obtain ⟨t, ht⟩ := orbitAux_exists_append σ₁ σ₂ n h
  rw [ht, List.length_append]
  omega

/-- Two profiles that agree on every history longer than `h₀` produce the same
    orbit from every history longer than `h₀`. This is what allows a one-shot
    deviation to become the original profile again once the history grows. -/
lemma orbitAux_congr {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    (n : ℕ) {h : Hist} (hl : h₀.length < h.length) :
    orbitAux σ₁ σ₂ n h = orbitAux σ₁' σ₂' n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    have hx : (σ₁ h, σ₂ h) = (σ₁' h, σ₂' h) := by rw [h₁ h hl, h₂ h hl]
    have hl' : h₀.length < (h ++ [(σ₁' h, σ₂' h)]).length := by
      rw [List.length_append]; simp; omega
    rw [orbitAux, orbitAux, hx]
    exact ih hl'

lemma actionAt_congr {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    (n : ℕ) {h : Hist} (hl : h₀.length < h.length) :
    actionAt σ₁ σ₂ h n = actionAt σ₁' σ₂' h n := by
  have ho := orbitAux_congr h₁ h₂ n hl
  have hlen : h₀.length < (orbitAux σ₁' σ₂' n h).length := by
    rw [← ho]
    exact lt_of_lt_of_le hl (length_le_orbitAux σ₁ σ₂ n h)
  simp only [actionAt, ho, h₁ _ hlen, h₂ _ hlen]

/-- Congruence of the discounted payoff for two profiles that agree beyond
    history `h₀`. -/
lemma contPayoff_congr_of_length {u : PDAction → PDAction → ℝ} {δ : ℝ}
    {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    {h : Hist} (hl : h₀.length < h.length) :
    contPayoff u δ σ₁ σ₂ h = contPayoff u δ σ₁' σ₂' h := by
  unfold contPayoff
  congr 1
  funext n
  rw [actionAt_congr h₁ h₂ n hl]

/-! ## Summability and uniform bound: (H1) at work -/

/-- The discounted payoff from any history is summable as soon as
    `0 ≤ δ < 1` and the stage payoffs are bounded by `K`. This is where (H1)
    enters: the geometric comparison needs a uniform bound, independent of the
    history. -/
lemma summable_contPayoff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    Summable (fun n : ℕ =>
      δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK cooperate cooperate)
  have hgeo : HasSum (fun n : ℕ => δ ^ n) ((1 - δ)⁻¹) :=
    hasSum_geometric_of_lt_one h0 h1
  refine Summable.of_norm_bounded
    ⟨(1 - δ)⁻¹ * K, HasSum.mul_right K hgeo⟩ ?_
  intro n
  have hp : (0 : ℝ) ≤ δ ^ n := pow_nonneg h0 n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left (hK _ _) hp

/-- Uniform bound `K/(1−δ)` on the discounted payoff from **every** history.
    It is this uniformity — not mere summability — that makes the deviation
    gain bounded along the orbit, hence extinguishable. -/
lemma abs_contPayoff_le (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    |contPayoff u δ σ₁ σ₂ h| ≤ K / (1 - δ) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK cooperate cooperate)
  have h1pos : 0 < 1 - δ := by linarith
  have hgeo : HasSum (fun n : ℕ => δ ^ n) ((1 - δ)⁻¹) :=
    hasSum_geometric_of_lt_one h0 h1
  have hbound : ∀ n : ℕ, ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
      (actionAt σ₁ σ₂ h n).2‖ ≤ δ ^ n * K := by
    intro n
    have hp : (0 : ℝ) ≤ δ ^ n := pow_nonneg h0 n
    calc ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2‖
        = δ ^ n * |u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      _ ≤ δ ^ n * K := mul_le_mul_of_nonneg_left (hK _ _) hp
  have hb : Summable (fun n : ℕ => δ ^ n * K) :=
    (HasSum.mul_right K hgeo).summable
  have hfn : Summable (fun n : ℕ => ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
      (actionAt σ₁ σ₂ h n).2‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hb
  have hmain : ‖∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1
        (actionAt σ₁ σ₂ h n).2‖ ≤ K / (1 - δ) := by
    calc ‖∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2‖
        ≤ ∑' n : ℕ, ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
            (actionAt σ₁ σ₂ h n).2‖ := norm_tsum_le_tsum_norm hfn
      _ ≤ ∑' n : ℕ, δ ^ n * K := Summable.tsum_le_tsum hbound hfn hb
      _ = K * (1 - δ)⁻¹ := by
        have hh := (HasSum.mul_right K hgeo).tsum_eq
        rw [hh]; ring
      _ = K / (1 - δ) := by rw [div_eq_mul_inv]
  simpa [contPayoff, Real.norm_eq_abs] using hmain

/-- **Extinction of the geometric residue** — this is (H2). Without `δ < 1`,
    a bound `x ≤ δ^k B` for all `k` does not rule out `x > 0`. -/
lemma le_zero_of_forall_geometric_bound {δ B x : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (_hB : 0 ≤ B) (h : ∀ k : ℕ, x ≤ δ ^ k * B) : x ≤ 0 := by
  by_contra hx
  rw [not_le] at hx
  have hpow : Tendsto (fun k : ℕ => δ ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hlim : Tendsto (fun k : ℕ => δ ^ k * B) atTop (nhds 0) := by
    simpa using hpow.mul_const B
  have hev : ∀ᶠ k : ℕ in atTop, δ ^ k * B < x := (tendsto_order.1 hlim).2 x hx
  obtain ⟨k, hk⟩ := eventually_atTop.1 hev
  have hk' : δ ^ k * B < x := hk k le_rfl
  linarith [h k]

/-! ## Decomposing the payoff: an algebraic identity -/

/-- Splitting identity: the payoff from `h` is the current move's gain plus `δ`
    times the payoff from the extended history. Purely algebraic once
    summability is available (H1).

    It is an identity — but it only links the deviant profile and the
    reference profile at **different** successors (each stacks its own joint
    action). Hence the inequality, not the identity, in `gainRow_le_step`. -/
lemma contPayoff_cons (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    contPayoff u δ σ₁ σ₂ h
      = u (σ₁ h) (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) := by
  have hsum := summable_contPayoff u hK h0 h1 σ₁ σ₂ h
  have hshift : ∀ n : ℕ,
      δ ^ (n + 1) * u (actionAt σ₁ σ₂ h (n + 1)).1 (actionAt σ₁ σ₂ h (n + 1)).2
        = δ * (δ ^ n * u (actionAt σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) n).1
            (actionAt σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) n).2) := by
    intro n
    rw [actionAt_succ]
    calc δ ^ (n + 1) * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
          (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2
        = (δ ^ n * δ) * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
            (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2 := by rw [pow_succ]
      _ = δ * (δ ^ n * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
            (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2) := by ring
  unfold contPayoff
  rw [Summable.tsum_eq_zero_add hsum, tsum_congr hshift, tsum_mul_left]
  simp [actionAt, orbitAux]

/-! ## One-shot deviation -/

/-- One-shot deviation: play `a` at history `h`, then return to the profile. -/
def oneShot (σ : Strategy) (h : Hist) (a : PDAction) : Strategy :=
  fun k => if k = h then a else σ k

@[simp] lemma oneShot_apply_self (σ : Strategy) (h : Hist) (a : PDAction) :
    oneShot σ h a h = a := by
  simp [oneShot]

lemma oneShot_agree (σ : Strategy) (h : Hist) (a : PDAction) :
    ∀ k : Hist, h.length < k.length → oneShot σ h a k = σ k := by
  intro k hk
  have hne : k ≠ h := by
    intro hh
    rw [hh] at hk
    exact lt_irrefl _ hk
  simp [oneShot, hne]

/-- First player: after a one-shot deviation at `h`, the payoff of the subgame
    starting right afterwards is again that of the original profile — the
    history has grown, the deviation is no longer active there. -/
lemma contPayoff_oneShot_tail_row (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ (h ++ [(a, σ₂ h)])
      = contPayoff u δ σ₁ σ₂ (h ++ [(a, σ₂ h)]) := by
  refine contPayoff_congr_of_length (h₀ := h) ?_ ?_ ?_
  · exact fun k hk => oneShot_agree σ₁ h a k hk
  · intro k _
    rfl
  · rw [List.length_append]
    simp

/-- Second player: same statement, the deviation acts on the column. -/
lemma contPayoff_oneShot_tail_col (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) (h ++ [(σ₁ h, b)])
      = contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, b)]) := by
  refine contPayoff_congr_of_length (h₀ := h) ?_ ?_ ?_
  · intro k _
    rfl
  · exact fun k hk => oneShot_agree σ₂ h b k hk
  · rw [List.length_append]
    simp

/-- Net first-move gain for the row player: deviate at `h` to `a`, collect,
    then return to the profile. -/
noncomputable def oneShotGainRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) : ℝ :=
  u a (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(a, σ₂ h)])
    - contPayoff u δ σ₁ σ₂ h

/-- Net first-move gain for the column player. -/
noncomputable def oneShotGainCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) : ℝ :=
  u (σ₁ h) b + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, b)])
    - contPayoff u δ σ₁ σ₂ h

/-- The payoff of a row deviation at `h` to `a` equals the profile's payoff
    plus the first-move gain. -/
lemma contPayoff_oneShot_row_eq (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ h
      = contPayoff u δ σ₁ σ₂ h + oneShotGainRow u δ σ₁ σ₂ h a := by
  rw [contPayoff_cons u hK h0 h1 (oneShot σ₁ h a) σ₂ h, oneShot_apply_self,
    contPayoff_oneShot_tail_row]
  unfold oneShotGainRow
  ring

/-- The payoff of a column deviation at `h` to `b`. -/
lemma contPayoff_oneShot_col_eq (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) h
      = contPayoff u δ σ₁ σ₂ h + oneShotGainCol u δ σ₁ σ₂ h b := by
  rw [contPayoff_cons u hK h0 h1 σ₁ (oneShot σ₂ h b) h, oneShot_apply_self,
    contPayoff_oneShot_tail_col]
  unfold oneShotGainCol
  ring

/-! ## The gain of an arbitrary deviation -/

/-- Gain of row strategy `σ₁'` against `σ₂`, at history `h`. -/
noncomputable def gainRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist) : ℝ :=
  contPayoff u δ σ₁' σ₂ h - contPayoff u δ σ₁ σ₂ h

/-- Gain of column strategy `σ₂'` against `σ₁`, at history `h`. -/
noncomputable def gainCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist) : ℝ :=
  contPayoff u δ σ₁ σ₂' h - contPayoff u δ σ₁ σ₂ h

/-- **No gain recursion, row player.** If the first move of an arbitrary
    deviation is not profitable (`hOS`), the total gain is bounded by `δ` times
    the residual gain at the **deviant profile's** successor.

    This is the inequality that carries the principle. The corresponding
    identity is false: the two profiles stack different joint actions. -/
lemma gainRow_le_step (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist)
    (hOS : oneShotGainRow u δ σ₁ σ₂ h (σ₁' h) ≤ 0) :
    gainRow u δ σ₁ σ₁' σ₂ h
      ≤ δ * gainRow u δ σ₁ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)]) := by
  -- the one-shot deviation to `σ₁' h` is not profitable
  have hkey : u (σ₁' h) (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁' h, σ₂ h)])
      ≤ contPayoff u δ σ₁ σ₂ h := by
    have hh := contPayoff_oneShot_row_eq u hK h0 h1 σ₁ σ₂ h (σ₁' h)
    unfold oneShotGainRow at hOS
    linarith
  -- and the deviant payoff splits at the same successor
  have hdev : contPayoff u δ σ₁' σ₂ h
      = u (σ₁' h) (σ₂ h)
        + δ * contPayoff u δ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)]) :=
    contPayoff_cons u hK h0 h1 σ₁' σ₂ h
  have hmul : δ * gainRow u δ σ₁ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)])
      = δ * contPayoff u δ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)])
        - δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁' h, σ₂ h)]) := by
    rw [gainRow]; ring
  rw [gainRow, hdev, hmul]
  linarith

/-- **No gain recursion, column player.** -/
lemma gainCol_le_step (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist)
    (hOS : oneShotGainCol u δ σ₁ σ₂ h (σ₂' h) ≤ 0) :
    gainCol u δ σ₁ σ₂ σ₂' h
      ≤ δ * gainCol u δ σ₁ σ₂ σ₂' (h ++ [(σ₁ h, σ₂' h)]) := by
  have hkey : u (σ₁ h) (σ₂' h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂' h)])
      ≤ contPayoff u δ σ₁ σ₂ h := by
    have hh := contPayoff_oneShot_col_eq u hK h0 h1 σ₁ σ₂ h (σ₂' h)
    unfold oneShotGainCol at hOS
    linarith
  have hdev : contPayoff u δ σ₁ σ₂' h
      = u (σ₁ h) (σ₂' h)
        + δ * contPayoff u δ σ₁ σ₂' (h ++ [(σ₁ h, σ₂' h)]) :=
    contPayoff_cons u hK h0 h1 σ₁ σ₂' h
  have hmul : δ * gainCol u δ σ₁ σ₂ σ₂' (h ++ [(σ₁ h, σ₂' h)])
      = δ * contPayoff u δ σ₁ σ₂' (h ++ [(σ₁ h, σ₂' h)])
        - δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂' h)]) := by
    rw [gainCol]; ring
  rw [gainCol, hdev, hmul]
  linarith

/-- **Gain iteration, row player.** The gain of an arbitrary deviation is
    bounded by `δⁿ` times the residual gain at step `n` of the deviation
    orbit. -/
lemma gainRow_le_iter (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist)
    (hOS : ∀ k : Hist, oneShotGainRow u δ σ₁ σ₂ k (σ₁' k) ≤ 0) (n : ℕ) :
    gainRow u δ σ₁ σ₁' σ₂ h
      ≤ δ ^ n * gainRow u δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ n h) := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
    have hb := gainRow_le_step u hK h0 h1 σ₁ σ₁' σ₂ h (hOS h)
    have hr := ih (h ++ [(σ₁' h, σ₂ h)])
    have hm := mul_le_mul_of_nonneg_left hr h0
    have hp : δ * (δ ^ n * gainRow u δ σ₁ σ₁' σ₂
        (orbitAux σ₁' σ₂ n (h ++ [(σ₁' h, σ₂ h)])))
        = δ ^ (n + 1) * gainRow u δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ (n + 1) h) := by
      rw [orbitAux, pow_succ]
      ring
    linarith [hb, hm, hp.le, hp.ge]

/-- **Gain iteration, column player.** -/
lemma gainCol_le_iter (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist)
    (hOS : ∀ k : Hist, oneShotGainCol u δ σ₁ σ₂ k (σ₂' k) ≤ 0) (n : ℕ) :
    gainCol u δ σ₁ σ₂ σ₂' h
      ≤ δ ^ n * gainCol u δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' n h) := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
    have hb := gainCol_le_step u hK h0 h1 σ₁ σ₂ σ₂' h (hOS h)
    have hr := ih (h ++ [(σ₁ h, σ₂' h)])
    have hm := mul_le_mul_of_nonneg_left hr h0
    have hp : δ * (δ ^ n * gainCol u δ σ₁ σ₂ σ₂'
        (orbitAux σ₁ σ₂' n (h ++ [(σ₁ h, σ₂' h)])))
        = δ ^ (n + 1) * gainCol u δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' (n + 1) h) := by
      rw [orbitAux, pow_succ]
      ring
    linarith [hb, hm, hp.le, hp.ge]

/-- A discounted payoff is bounded above by `K/(1−δ)`, once (H1) is available. -/
lemma contPayoff_le_bound (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    contPayoff u δ σ₁ σ₂ h ≤ K / (1 - δ) := by
  have hle : contPayoff u δ σ₁ σ₂ h ≤ |contPayoff u δ σ₁ σ₂ h| := le_abs_self _
  have habs := abs_contPayoff_le u hK h0 h1 σ₁ σ₂ h
  linarith

/-- The lower counterpart: `−(K/(1−δ))` bounds every discounted payoff from
    below. Both sides are needed to bound a **difference** of payoffs. -/
lemma neg_contPayoff_le_bound (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    -(K / (1 - δ)) ≤ contPayoff u δ σ₁ σ₂ h := by
  have hle : -|contPayoff u δ σ₁ σ₂ h| ≤ contPayoff u δ σ₁ σ₂ h := neg_abs_le _
  have habs := abs_contPayoff_le u hK h0 h1 σ₁ σ₂ h
  linarith

/-! ## One-shot deviation conditions and SPE -/

/-- No one-shot row deviation is profitable, **at every history** — including
    off the equilibrium path. -/
def NoProfitableOneShotRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  ∀ (h : Hist) (a : PDAction),
    contPayoff u δ (oneShot σ₁ h a) σ₂ h ≤ contPayoff u δ σ₁ σ₂ h

/-- No one-shot column deviation is profitable. -/
def NoProfitableOneShotCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  ∀ (h : Hist) (b : PDAction),
    contPayoff u δ σ₁ (oneShot σ₂ h b) h ≤ contPayoff u δ σ₁ σ₂ h

/-- One-shot deviation condition. -/
def NoProfitableOneShot (u₁ u₂ : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  NoProfitableOneShotRow u₁ δ σ₁ σ₂ ∧ NoProfitableOneShotCol u₂ δ σ₁ σ₂

/-- Subgame-perfect equilibrium: at every history, no player gains by changing
    strategy with the opponent held fixed. -/
def IsSPE (u₁ u₂ : PDAction → PDAction → ℝ) (δ : ℝ) (σ₁ σ₂ : Strategy) : Prop :=
  (∀ (h : Hist) (σ₁' : Strategy),
      contPayoff u₁ δ σ₁' σ₂ h ≤ contPayoff u₁ δ σ₁ σ₂ h) ∧
  (∀ (h : Hist) (σ₂' : Strategy),
      contPayoff u₂ δ σ₁ σ₂' h ≤ contPayoff u₂ δ σ₁ σ₂ h)

/-- Non-profitability of a one-shot row deviation ⟺ non-positive first-move
    gain. -/
lemma oneShotRow_le_iff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ h ≤ contPayoff u δ σ₁ σ₂ h
      ↔ oneShotGainRow u δ σ₁ σ₂ h a ≤ 0 := by
  rw [contPayoff_oneShot_row_eq u hK h0 h1 σ₁ σ₂ h a]
  constructor <;> intro hh <;> linarith

/-- Non-profitability of a one-shot column deviation ⟺ non-positive gain. -/
lemma oneShotCol_le_iff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) h ≤ contPayoff u δ σ₁ σ₂ h
      ↔ oneShotGainCol u δ σ₁ σ₂ h b ≤ 0 := by
  rw [contPayoff_oneShot_col_eq u hK h0 h1 σ₁ σ₂ h b]
  constructor <;> intro hh <;> linarith

/-- **One-shot deviation principle.** If no one-shot deviation is profitable at
    any history, the profile is a subgame-perfect equilibrium — under (H1)
    `∀ a b, |uᵢ a b| ≤ Kᵢ` and (H2) `δ < 1`.

    Argument: `G(h) ≤ δ·G(h')` where `h'` follows the first deviant move
    (`gainRow_le_step`), hence `G(h) ≤ δⁿ·G(hₙ)` along the deviation orbit;
    and `G(hₙ) ≤ 2K/(1−δ)` by (H1), while `δⁿ → 0` by (H2), hence
    `G(h) ≤ 0`. -/
theorem oneShotDeviationPrinciple (u₁ u₂ : PDAction → PDAction → ℝ) {K₁ K₂ : ℝ}
    (hK₁ : ∀ a b, |u₁ a b| ≤ K₁) (hK₂ : ∀ a b, |u₂ a b| ≤ K₂)
    {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) (σ₁ σ₂ : Strategy)
    (hNE : NoProfitableOneShot u₁ u₂ δ σ₁ σ₂) : IsSPE u₁ u₂ δ σ₁ σ₂ := by
  obtain ⟨hRow, hCol⟩ := hNE
  have hK₁0 : 0 ≤ K₁ := le_trans (abs_nonneg _) (hK₁ cooperate cooperate)
  have hK₂0 : 0 ≤ K₂ := le_trans (abs_nonneg _) (hK₂ cooperate cooperate)
  have h1pos : 0 < 1 - δ := by linarith
  constructor
  · intro h σ₁'
    have hOS : ∀ k : Hist, oneShotGainRow u₁ δ σ₁ σ₂ k (σ₁' k) ≤ 0 :=
      fun k => (oneShotRow_le_iff u₁ hK₁ h0 h1 σ₁ σ₂ k (σ₁' k)).1
        (hRow k (σ₁' k))
    have hB : 0 ≤ 2 * (K₁ / (1 - δ)) := by
      have hd : 0 ≤ K₁ / (1 - δ) := div_nonneg hK₁0 h1pos.le
      linarith
    have hforall : ∀ k : ℕ,
        gainRow u₁ δ σ₁ σ₁' σ₂ h ≤ δ ^ k * (2 * (K₁ / (1 - δ))) := by
      intro k
      have hi := gainRow_le_iter u₁ hK₁ h0 h1 σ₁ σ₁' σ₂ h hOS k
      have ha := contPayoff_le_bound u₁ hK₁ h0 h1 σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
      have hb := neg_contPayoff_le_bound u₁ hK₁ h0 h1 σ₁ σ₂ (orbitAux σ₁' σ₂ k h)
      have hgr : gainRow u₁ δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
          ≤ 2 * (K₁ / (1 - δ)) := by
        unfold gainRow
        linarith
      have h3 : δ ^ k * gainRow u₁ δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
          ≤ δ ^ k * (2 * (K₁ / (1 - δ))) :=
        mul_le_mul_of_nonneg_left hgr (pow_nonneg h0 k)
      linarith
    have hz := le_zero_of_forall_geometric_bound h0 h1 hB hforall
    unfold gainRow at hz
    linarith
  · intro h σ₂'
    have hOS : ∀ k : Hist, oneShotGainCol u₂ δ σ₁ σ₂ k (σ₂' k) ≤ 0 :=
      fun k => (oneShotCol_le_iff u₂ hK₂ h0 h1 σ₁ σ₂ k (σ₂' k)).1
        (hCol k (σ₂' k))
    have hB : 0 ≤ 2 * (K₂ / (1 - δ)) := by
      have hd : 0 ≤ K₂ / (1 - δ) := div_nonneg hK₂0 h1pos.le
      linarith
    have hforall : ∀ k : ℕ,
        gainCol u₂ δ σ₁ σ₂ σ₂' h ≤ δ ^ k * (2 * (K₂ / (1 - δ))) := by
      intro k
      have hi := gainCol_le_iter u₂ hK₂ h0 h1 σ₁ σ₂ σ₂' h hOS k
      have ha := contPayoff_le_bound u₂ hK₂ h0 h1 σ₁ σ₂' (orbitAux σ₁ σ₂' k h)
      have hb := neg_contPayoff_le_bound u₂ hK₂ h0 h1 σ₁ σ₂ (orbitAux σ₁ σ₂' k h)
      have hgr : gainCol u₂ δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' k h)
          ≤ 2 * (K₂ / (1 - δ)) := by
        unfold gainCol
        linarith
      have h3 : δ ^ k * gainCol u₂ δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' k h)
          ≤ δ ^ k * (2 * (K₂ / (1 - δ))) :=
        mul_le_mul_of_nonneg_left hgr (pow_nonneg h0 k)
      linarith
    have hz := le_zero_of_forall_geometric_bound h0 h1 hB hforall
    unfold gainCol at hz
    linarith

/-! ## C. Grim trigger as a subgame-perfect equilibrium

Sections A and B established the one-shot deviation principle for an abstract
stage game. This section instantiates it on the Prisoner's Dilemma: the
"grim trigger against grim trigger" profile is an SPE **iff**
`δ ≥ (T − R)/(T − P)`.

The organ of the proof is a single history boolean, `anyDefect`: a history is
"clean" if neither player has ever deviated in it. Grim cooperates on a clean
history and punishes otherwise — so this boolean is **invariant** along the
grim/grim orbit, and the profile's discounted payoff has only two possible
values, `R/(1−δ)` and `P/(1−δ)`. That is what makes the one-shot deviation
analysis computable. -/

/-- (H1) on the Prisoner's Dilemma: the four stage payoffs are uniformly
    bounded by the sum of their absolute values. On a finite game this is
    automatic — and it is still a hypothesis about the stage game, not a
    tautology: the one-shot deviation principle demands it explicitly. -/
lemma stagePayoff_abs_le (g : PrisonersDilemma) (a b : PDAction) :
    |stagePayoff g a b| ≤ |g.R| + |g.T| + |g.S| + |g.P| := by
  cases a <;> cases b <;>
    simp only [stagePayoff] <;>
    linarith [abs_nonneg g.R, abs_nonneg g.T, abs_nonneg g.S, abs_nonneg g.P]

/-- The column player's payoff, seen as a function of the actions: it is the
    row payoff with the arguments swapped. Naming it gives a stable rewrite
    key — an anonymous lambda does not unify from one goal to the next. -/
def colPayoff (g : PrisonersDilemma) : PDAction → PDAction → ℝ :=
  fun a b => stagePayoff g b a

/-- (H1) for `colPayoff`, which is the column player's payoff. -/
lemma colPayoff_abs_le (g : PrisonersDilemma) (a b : PDAction) :
    |colPayoff g a b| ≤ |g.R| + |g.T| + |g.S| + |g.P| :=
  stagePayoff_abs_le g b a

/-! ### The instrument: the boolean "has a defection occurred?" -/

/-- Does the history already contain a defection, on either side? -/
def anyDefect (h : Hist) : Bool :=
  h.any (fun p => decide (p.1 = defect ∨ p.2 = defect))

/-- Grim trigger strategy: cooperate as long as the history is clean, punish
    forever as soon as a defection appears in it. -/
def grimStrategy : Strategy := fun h => if anyDefect h then defect else cooperate

/-- Strategy "deviate at every move", used to exhibit a profitable deviation
    when the threshold is not reached. -/
def deviateAlways : Strategy := fun _ => defect

@[simp] lemma anyDefect_nil : anyDefect ([] : Hist) = false := by
  simp [anyDefect]

lemma anyDefect_append (h : Hist) (p : PDAction × PDAction) :
    anyDefect (h ++ [p]) =
      (anyDefect h || decide (p.1 = defect ∨ p.2 = defect)) := by
  simp [anyDefect, List.any_append]

lemma anyDefect_append_coop (h : Hist) :
    anyDefect (h ++ [(cooperate, cooperate)]) = anyDefect h := by
  rw [anyDefect_append]
  simp

lemma anyDefect_append_of_fst_defect (h : Hist) (b : PDAction) :
    anyDefect (h ++ [(defect, b)]) = true := by
  rw [anyDefect_append]
  cases hd : anyDefect h <;> cases b <;> simp

lemma anyDefect_append_of_snd_defect (h : Hist) (a : PDAction) :
    anyDefect (h ++ [(a, defect)]) = true := by
  rw [anyDefect_append]
  cases hd : anyDefect h <;> cases a <;> simp

lemma grimStrategy_of_no_defect (h : Hist) (hd : anyDefect h = false) :
    grimStrategy h = cooperate := by
  simp [grimStrategy, hd]

lemma grimStrategy_of_defect (h : Hist) (hd : anyDefect h = true) :
    grimStrategy h = defect := by
  simp [grimStrategy, hd]

/-- The boolean is **invariant** along the grim-against-grim orbit: both
    players always play the same action there, so neither adds a defection the
    other does not add. -/
lemma anyDefect_orbit_grim (h : Hist) (n : ℕ) :
    anyDefect (orbitAux grimStrategy grimStrategy n h) = anyDefect h := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
      rw [orbitAux, ih]
      cases hd : anyDefect h with
      | true =>
          rw [grimStrategy_of_defect h hd]
          exact anyDefect_append_of_snd_defect h defect
      | false =>
          rw [grimStrategy_of_no_defect h hd, anyDefect_append_coop]
          exact hd

/-- Under an already dirty history, a perpetual deviation stays in the
    punishment zone: the boolean stays true forever. -/
lemma anyDefect_orbit_deviate (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    anyDefect (orbitAux deviateAlways grimStrategy n h) = true := by
  induction n generalizing h with
  | zero => simpa [orbitAux] using hd
  | succ n ih =>
      rw [orbitAux]
      exact ih (h ++ [(deviateAlways h, grimStrategy h)])
        (anyDefect_append_of_fst_defect h (grimStrategy h))

/-! ### Discounted payoffs of the profile and of the deviation -/

/-- The column player's payoff coincides with the row player's on the
    grim/grim orbit: both components of the action there are the **same** term
    `grimStrategy (orbitAux …)`, so swapping the arguments is definitionally
    invisible. -/
lemma contPayoff_col_grim (g : PrisonersDilemma) (δ : ℝ) (h : Hist) :
    contPayoff (colPayoff g) δ grimStrategy grimStrategy h
      = contPayoff (stagePayoff g) δ grimStrategy grimStrategy h := by
  unfold contPayoff colPayoff actionAt
  exact tsum_congr (fun n => rfl)

/-- Discounted payoff of a profile whose stage payoff is constant. -/
lemma contPayoff_of_const_orbit (u : PDAction → PDAction → ℝ) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (σ₁ σ₂ : Strategy) (h : Hist) (c : ℝ)
    (hc : ∀ n : ℕ, u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2 = c) :
    contPayoff u δ σ₁ σ₂ h = c * (1 - δ)⁻¹ := by
  unfold contPayoff
  calc ∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2
      = ∑' n : ℕ, δ ^ n * c := tsum_congr (fun n => by rw [hc n])
    _ = c * ∑' n : ℕ, δ ^ n := by
          rw [← tsum_mul_left]
          exact tsum_congr (fun n => by ring)
    _ = c * (1 - δ)⁻¹ := by rw [geom_sum h0 h1]

lemma actionAt_grim_of_no_defect (h : Hist) (hd : anyDefect h = false) (n : ℕ) :
    actionAt grimStrategy grimStrategy h n = (cooperate, cooperate) := by
  unfold actionAt
  have h1 : anyDefect (orbitAux grimStrategy grimStrategy n h) = false := by
    rw [anyDefect_orbit_grim, hd]
  rw [grimStrategy_of_no_defect _ h1]

lemma actionAt_grim_of_defect (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    actionAt grimStrategy grimStrategy h n = (defect, defect) := by
  unfold actionAt
  have h1 : anyDefect (orbitAux grimStrategy grimStrategy n h) = true := by
    rw [anyDefect_orbit_grim, hd]
  rw [grimStrategy_of_defect _ h1]

lemma actionAt_deviate_of_defect (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    actionAt deviateAlways grimStrategy h n = (defect, defect) := by
  unfold actionAt
  have h1 := anyDefect_orbit_deviate h hd n
  rw [grimStrategy_of_defect _ h1]
  rfl

/-- On a clean history, the grim/grim profile is perpetual cooperation:
    `R/(1−δ)`. -/
lemma contPayoff_grim_of_no_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = false) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h = coopValue g.R δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt grimStrategy grimStrategy h n).1
        (actionAt grimStrategy grimStrategy h n).2 = g.R := by
    intro n
    rw [actionAt_grim_of_no_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 grimStrategy grimStrategy h g.R hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- On a dirty history, the grim/grim profile is perpetual punishment:
    `P/(1−δ)`. -/
lemma contPayoff_grim_of_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = true) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h = coopValue g.P δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt grimStrategy grimStrategy h n).1
        (actionAt grimStrategy grimStrategy h n).2 = g.P := by
    intro n
    rw [actionAt_grim_of_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 grimStrategy grimStrategy h g.P hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- A perpetual deviator facing grim collects perpetual punishment as soon as
    the history is dirty. -/
lemma contPayoff_deviate_of_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = true) :
    contPayoff (stagePayoff g) δ deviateAlways grimStrategy h = coopValue g.P δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt deviateAlways grimStrategy h n).1
        (actionAt deviateAlways grimStrategy h n).2 = g.P := by
    intro n
    rw [actionAt_deviate_of_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 deviateAlways grimStrategy h g.P hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- The payoff of a perpetual deviation from the empty history is exactly
    `deviateValue T P δ`: `T` on the first move, then `P` forever. -/
lemma contPayoff_deviate_root (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    contPayoff (stagePayoff g) δ deviateAlways grimStrategy ([] : Hist)
      = deviateValue g.T g.P δ := by
  have hstep := contPayoff_cons (stagePayoff g) (stagePayoff_abs_le g) h0 h1
    deviateAlways grimStrategy ([] : Hist)
  have hgr : grimStrategy ([] : Hist) = cooperate := grimStrategy_of_no_defect _ anyDefect_nil
  have htail : contPayoff (stagePayoff g) δ deviateAlways grimStrategy
      (([] : Hist) ++ [(deviateAlways ([] : Hist), grimStrategy ([] : Hist))])
      = coopValue g.P δ := by
    refine contPayoff_deviate_of_defect g h0 h1 _ ?_
    rw [hgr]
    exact anyDefect_append_of_fst_defect [] cooperate
  rw [hstep, htail, hgr]
  simp only [deviateAlways, stagePayoff]
  unfold coopValue deviateValue
  ring

/-! ### The algebra of a one-shot deviation gain

Two real identities suffice: `δ·x/(1−δ) − x/(1−δ) = −x`, and the threshold
`coopValue R δ ≥ deviateValue T P δ`. -/

private lemma gain_atom (x δ : ℝ) (h1 : δ < 1) :
    δ * (x / (1 - δ)) - x / (1 - δ) = -x := by
  have h : (1 : ℝ) - δ ≠ 0 := by intro hh; linarith
  field_simp
  ring

/-- No one-shot row deviation is profitable when the threshold is reached.
    Four cases, one per `(history, action)` pair: clean or dirty history,
    cooperate or deviate action.

    - clean + cooperate: gain `0` (the profile is replayed);
    - clean + deviate  : gain `deviateValue − coopValue ≤ 0`, this is the
      threshold;
    - dirty + cooperate: gain `S − P < 0`;
    - dirty + deviate  : gain `0` (punishment is already in place). -/
lemma oneShotGainRow_grim_nonpos (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) (h : Hist) (a : PDAction) :
    oneShotGainRow (stagePayoff g) δ grimStrategy grimStrategy h a ≤ 0 := by
  unfold oneShotGainRow
  have hδp : (0 : ℝ) < 1 - δ := by linarith
  cases hd : anyDefect h with
  | false =>
      have hg : grimStrategy h = cooperate := grimStrategy_of_no_defect h hd
      rw [hg, contPayoff_grim_of_no_defect g h0 h1 h hd]
      cases a with
      | cooperate =>
          have hd2 : anyDefect (h ++ [(cooperate, cooperate)]) = false := by
            rw [anyDefect_append_coop, hd]
          rw [contPayoff_grim_of_no_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.R δ h1
          unfold coopValue
          linarith
      | defect =>
          have hd2 : anyDefect (h ++ [(defect, cooperate)]) = true :=
            anyDefect_append_of_fst_defect h cooperate
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          -- Normalise the threshold onto the goal's shape: `δ * x / (1-δ)` and
          -- `δ * (x / (1-δ))` are equal but syntactically distinct, and
          -- `linarith` reasons on atoms, not on shapes.
          have hthr' : g.T + δ * (g.P / (1 - δ)) ≤ g.R / (1 - δ) := by
            unfold coopValue deviateValue at hthr
            rw [mul_div_assoc] at hthr
            linarith
          unfold coopValue
          linarith
  | true =>
      have hg : grimStrategy h = defect := grimStrategy_of_defect h hd
      rw [hg, contPayoff_grim_of_defect g h0 h1 h hd]
      cases a with
      | cooperate =>
          have hd2 : anyDefect (h ++ [(cooperate, defect)]) = true :=
            anyDefect_append_of_snd_defect h cooperate
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.P δ h1
          unfold coopValue
          linarith [g.hPS]
      | defect =>
          have hd2 : anyDefect (h ++ [(defect, defect)]) = true :=
            anyDefect_append_of_snd_defect h defect
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.P δ h1
          unfold coopValue
          linarith

/-- The grim/grim profile's payoff depends on the history only through its
    defection boolean: two histories with the same boolean give the same
    payoff. -/
lemma contPayoff_grim_congr_anyDefect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) {h₁ h₂ : Hist}
    (hd : anyDefect h₁ = anyDefect h₂) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h₁
      = contPayoff (stagePayoff g) δ grimStrategy grimStrategy h₂ := by
  cases ha : anyDefect h₁ with
  | false =>
      rw [contPayoff_grim_of_no_defect g h0 h1 h₁ ha,
        contPayoff_grim_of_no_defect g h0 h1 h₂ (by rw [← hd]; exact ha)]
  | true =>
      rw [contPayoff_grim_of_defect g h0 h1 h₁ ha,
        contPayoff_grim_of_defect g h0 h1 h₂ (by rw [← hd]; exact ha)]

/-- The column one-shot deviation gain coincides with the row one: the only
    difference is the order of the pair appended to the history, and the
    payoff does not see it (it depends only on `anyDefect`). -/
lemma oneShotGainCol_grim_eq_row (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (b : PDAction) :
    oneShotGainCol (colPayoff g) δ grimStrategy grimStrategy h b
      = oneShotGainRow (stagePayoff g) δ grimStrategy grimStrategy h b := by
  unfold oneShotGainCol oneShotGainRow
  rw [contPayoff_col_grim g δ, contPayoff_col_grim g δ]
  simp only [colPayoff]
  have hord : anyDefect (h ++ [(grimStrategy h, b)]) = anyDefect (h ++ [(b, grimStrategy h)]) := by
    rw [anyDefect_append, anyDefect_append]
    by_cases hx : grimStrategy h = defect <;> by_cases hb : b = defect <;> simp [hx, hb]
  rw [contPayoff_grim_congr_anyDefect g h0 h1 hord]

/-- Both players of the Prisoner's Dilemma have the same grim strategy, so the
    row result also holds for the column. -/
lemma oneShotGainCol_grim_nonpos (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) (h : Hist) (b : PDAction) :
    oneShotGainCol (colPayoff g) δ grimStrategy grimStrategy h b ≤ 0 := by
  rw [oneShotGainCol_grim_eq_row g h0 h1 h b]
  exact oneShotGainRow_grim_nonpos g h0 h1 hthr h b

/-- No one-shot deviation is profitable for either player. -/
lemma noProfitableOneShot_grim (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) :
    NoProfitableOneShot (stagePayoff g) (colPayoff g) δ
      grimStrategy grimStrategy := by
  constructor
  · intro h a
    rw [contPayoff_oneShot_row_eq (stagePayoff g) (stagePayoff_abs_le g) h0 h1
      grimStrategy grimStrategy h a]
    have hg := oneShotGainRow_grim_nonpos g h0 h1 hthr h a
    linarith
  · intro h b
    rw [contPayoff_oneShot_col_eq (colPayoff g)
      (colPayoff_abs_le g) h0 h1 grimStrategy grimStrategy h b]
    have hg := oneShotGainCol_grim_nonpos g h0 h1 hthr h b
    linarith

/-! ### The two directions of the equivalence -/

/-- **Forward direction.** Above the threshold, the grim trigger profile is a
    subgame-perfect equilibrium — a consequence of the one-shot deviation
    principle, with (H1) `stagePayoff_abs_le` and (H2) `δ < 1`. -/
theorem grim_isSPE_of_threshold (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : δ ≥ (g.T - g.R) / (g.T - g.P)) :
    IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy :=
  oneShotDeviationPrinciple (stagePayoff g) (colPayoff g)
    (stagePayoff_abs_le g) (colPayoff_abs_le g) h0 h1 grimStrategy grimStrategy
    (noProfitableOneShot_grim g h0 h1 ((coop_ge_deviate_iff g h0 h1).mpr hthr))

/-- **Converse direction.** Below the threshold, the profile is not an SPE:
    the strategy "deviate at every move" beats perpetual cooperation in the
    initial subgame. -/
theorem threshold_of_grim_isSPE (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hspe : IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy) :
    δ ≥ (g.T - g.R) / (g.T - g.P) := by
  obtain ⟨hrow, _⟩ := hspe
  have hdev := hrow ([] : Hist) deviateAlways
  rw [contPayoff_deviate_root g h0 h1] at hdev
  have hbase : contPayoff (stagePayoff g) δ grimStrategy grimStrategy ([] : Hist)
      = coopValue g.R δ :=
    contPayoff_grim_of_no_defect g h0 h1 [] anyDefect_nil
  rw [hbase] at hdev
  exact (coop_ge_deviate_iff g h0 h1).mp hdev

/-- **Main theorem.** The grim trigger profile of the discounted Prisoner's
    Dilemma is a subgame-perfect equilibrium **iff** the discount factor
    reaches the critical threshold `(T − R)/(T − P)`.

    The two hypotheses of section A are named explicitly here: (H1) is
    `stagePayoff_abs_le`, (H2) is `h1 : δ < 1`. `GrimTrigger.lean` stated the
    incentive condition; this theorem turns it into an equilibrium statement,
    quantified over histories and profiles. -/
theorem grim_isSPE_iff (g : PrisonersDilemma) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) :=
  ⟨threshold_of_grim_isSPE g h0 h1, grim_isSPE_of_threshold g h0 h1⟩

end RepeatedGames_en