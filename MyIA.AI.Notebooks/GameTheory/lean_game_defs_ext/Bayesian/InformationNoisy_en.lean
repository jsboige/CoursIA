/-
  Value of information for a noisy signal (finite joint tables)
  =============================================================

  `Information.lean` treats *deterministic* signals: a signal there is a map
  from states to realizations, hence a partition of the state space. A
  **noisy** signal does not partition: several states may produce the same
  realization, and a realization may remain compatible with several states.
  A joint table is then required.

  Representation retained: a table of **natural** joint weights
  `p : Fin nS → Fin (nX + 1) → Nat` (state × realization), with integer
  payoffs. This is the exact route announced by #22374: it avoids every
  conditional division.

  Hypotheses, written here because they carry the comparison:

  - `p s x` is a **weight**, not a probability: the total mass
    `Σ_(s,x) p s x` is not normalized to 1. The normalization factor is
    strictly positive as soon as the table is not zero. All values defined
    below are raw, on the scale of that mass; two proportional tables
    describe the same problem and give values in the same ratio.
  - the decision maker's prior is the **marginal** of the table,
    `priorMass s`: no separate prior is carried, which could contradict the
    table and make the two semantics diverge.
  - a realization of zero mass is not an error: its contributions are zero
    by construction (no division is taken), so an impossible signal produces
    neither `NaN` nor an exception.

  What is proved in this module (two tranches of #22374):

  - `valueNoisyNoInfo_le_valueNoisySignal` — the raw value of a decision
    maker who observes the signal dominates that of an uninformed maker,
    with the same joint weights (master lemma `maxFin_sumFin_le` applied to
    the signal realizations, plus commutation of sums);
  - `valueNoisySignal_le_valueNoisyPerfect` — perfect information dominates
    every noisy signal, even in raw unnormalized values (master lemma
    `sumFin_maxFin_mul_le`, the algebraic form of Blackwell, zero-mass case
    treated separately);
  - a zero-mass realization contributes **exactly** zero, by theorem
    (`valueNoisySignal_zero_mass_cell`) and not by absence of division;
  - `valueNoisyNoInfo_nonneg`, `valueNoisySignal_nonneg`,
    `valueNoisyPerfect_nonneg` — the three values are nonnegative **under
    the hypothesis** `NonnegPayouts`. The hypothesis is necessary:
    `NoisyProblem` does not constrain the sign of `u`, and a well-formed
    instance of strictly negative value exists (see the section "Sign of
    the values").

  What remains for later tranches, and is **not** claimed here: independent
  case with zero EVSI, bridge to the deterministic `Signal`, exact adapter
  to the JSON instances of the `voi` bench, re-executed companion notebook.

  See #22374 (extension of Bayesian phase 4 of #2610).
-/

import Bayesian.Information

/-- Finite single-decision-maker decision problem, with a noisy signal
    described by a table of joint weights state × realization. Payoffs are
    integers and weights natural: values are exact, without division. -/
structure NoisyProblem where
  /-- Number of states of the world. -/
  nS : Nat
  /-- Number of actions minus one (actions are `Fin (nA + 1)`). -/
  nA : Nat
  /-- Number of signal realizations minus one. -/
  nX : Nat
  /-- Unnormalized joint weight of state `s` and realization `x`. -/
  p : Fin nS → Fin (nX + 1) → Nat
  /-- Integer payoff of action `a` in state `s`. -/
  u : Fin nS → Fin (nA + 1) → Int

/-- Joint mass (unnormalized) of a signal realization. -/
def signalMass (D : NoisyProblem) (x : Fin (D.nX + 1)) : Int :=
  sumFin D.nS (fun s => (D.p s x : Int))

/-- Marginal weight of state `s` induced by the joint table: this is
    the prior the decision maker actually uses. -/
def priorMass (D : NoisyProblem) (s : Fin D.nS) : Int :=
  sumFin (D.nX + 1) (fun x => (D.p s x : Int))

/-- Joint payoff of action `a` in state `s` and realization `x`: the
    cell weight times the payoff. -/
def jointPayoff (D : NoisyProblem) (s : Fin D.nS) (x : Fin (D.nX + 1))
    (a : Fin (D.nA + 1)) : Int :=
  (D.p s x : Int) * D.u s a

/-- Raw value of the uninformed decision maker: a single action, chosen
    on the marginal prior of the joint table. -/
def valueNoisyNoInfo (D : NoisyProblem) : Int :=
  maxFin D.nA (fun a => sumFin D.nS (fun s => priorMass D s * D.u s a))

/-- Raw value of the decision maker who observes the signal realization:
    one action per realization, chosen on the cell weights. -/
def valueNoisySignal (D : NoisyProblem) : Int :=
  sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a =>
    sumFin D.nS (fun s => jointPayoff D s x a)))

/-- The payoff of an action, aggregated over realizations, is exactly
    the payoff weighted by the marginal prior: the joint table and the prior
    are a single datum. -/
theorem sumFin_jointPayoff (D : NoisyProblem) (s : Fin D.nS)
    (a : Fin (D.nA + 1)) :
    sumFin (D.nX + 1) (fun x => jointPayoff D s x a) =
    priorMass D s * D.u s a := by
  unfold jointPayoff priorMass
  rw [sumFin_congr (fun x => Int.mul_comm (D.p s x : Int) (D.u s a)),
    sumFin_mul_left, Int.mul_comm]

/-- **The raw value of a noisy signal dominates that of the uninformed
    decision maker.** Both values are on the scale of the table mass: the
    inequality concerns raw values, not a normalized EVSI. -/
theorem valueNoisyNoInfo_le_valueNoisySignal (D : NoisyProblem) :
    valueNoisyNoInfo D ≤ valueNoisySignal D := by
  unfold valueNoisyNoInfo valueNoisySignal
  have hswap : ∀ a : Fin (D.nA + 1),
      sumFin D.nS (fun s => priorMass D s * D.u s a) =
      sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s => jointPayoff D s x a)) := by
    intro a
    calc sumFin D.nS (fun s => priorMass D s * D.u s a)
        = sumFin D.nS (fun s => sumFin (D.nX + 1)
            (fun x => jointPayoff D s x a)) :=
          sumFin_congr (fun s => (sumFin_jointPayoff D s a).symm)
      _ = sumFin (D.nX + 1) (fun x => sumFin D.nS
            (fun s => jointPayoff D s x a)) := sumFin_comm _
  calc maxFin D.nA (fun a => sumFin D.nS (fun s => priorMass D s * D.u s a))
      = maxFin D.nA (fun a => sumFin (D.nX + 1) (fun x => sumFin D.nS
            (fun s => jointPayoff D s x a))) := by
        exact congrArg (maxFin D.nA) (funext hswap)
    _ ≤ sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a => sumFin D.nS
            (fun s => jointPayoff D s x a))) :=
        maxFin_sumFin_le (fun x a => sumFin D.nS (fun s => jointPayoff D s x a))

/-
  Concrete verification: the umbrella of `Information.lean`, this time with
  a **noisy** forecast. Two states (rain, sun), two actions (umbrella, leave
  it), two bulletins (announce rain, announce sun). The forecast is good but
  imperfect: joint weights (3, 1) then (1, 3), for a marginal prior of 4 in
  each state.
-/

/-- Umbrella with a noisy forecast: the bulletin is correct with a
    weight of 3 against 1 for the error. -/
def noisyUmbrella : NoisyProblem where
  nS := 2
  nA := 1
  nX := 1
  p := fun s x => if s.val = x.val then 3 else 1
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 2 else -3)
    else (if a.val = 0 then 0 else 3)

/-- Uninformed, the decision maker always takes the umbrella: raw value
    8, i.e. 2 per state for a marginal weight of 4. -/
theorem noisyUmbrella_valueNoisyNoInfo :
    valueNoisyNoInfo noisyUmbrella = 8 := by decide

/-- Informed, they follow the bulletin: 6 + 6, i.e. 12. The raw value of
    the signal therefore strictly exceeds that of the uninformed. -/
theorem noisyUmbrella_valueNoisySignal :
    valueNoisySignal noisyUmbrella = 12 := by decide

/-- The raw gain of the signal is strictly positive on this example: the
    bound of `valueNoisyNoInfo_le_valueNoisySignal` is attained strictly, it
    is not an artefact of the representation. -/
theorem noisyUmbrella_strict_gain :
    valueNoisyNoInfo noisyUmbrella < valueNoisySignal noisyUmbrella := by
  decide

/-- Raw value of perfect information: the state is revealed, the decision
    maker chooses one action per state on the marginal prior of the joint
    table. -/
def valueNoisyPerfect (D : NoisyProblem) : Int :=
  sumFin D.nS (fun s => maxFin D.nA (fun a => priorMass D s * D.u s a))

/-! ## Zero-mass signals

A realization of zero mass is an impossible signal. Since the representation
is exact (no conditional division), it cannot produce a division by zero:
what remains to be proved is that its contribution is exactly zero, and not
"almost zero" through rounding. -/

/-- A sum of nonnegative terms is nonnegative. -/
theorem sumFin_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumFin n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumFin_succ]
    have h0 := h 0
    have ht := ih (f := fun i => f i.succ) (fun i => h i.succ)
    omega

/-- If a sum of nonnegative terms is zero, every term is zero: this is
    what makes the zero mass of a realization transmissible to its cells. -/
theorem eq_zero_of_sumFin_nonneg {n : Nat} {f : Fin n → Int}
    (h : ∀ i, 0 ≤ f i) (hsum : sumFin n f = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    rw [sumFin_succ] at hsum
    have ht := sumFin_nonneg (f := fun j => f j.succ) (fun j => h j.succ)
    have h0nn := h 0
    have h0 : f 0 = 0 := by omega
    cases i using Fin.cases with
    | zero => exact h0
    | succ j =>
      exact ih (f := fun j => f j.succ) (fun j => h j.succ) (by omega) j

/-- A realization of zero mass has all its joint weights zero. -/
theorem p_eq_zero_of_signalMass_zero (D : NoisyProblem) (x : Fin (D.nX + 1))
    (h : signalMass D x = 0) (s : Fin D.nS) : D.p s x = 0 := by
  unfold signalMass at h
  have hz : (D.p s x : Int) = 0 :=
    eq_zero_of_sumFin_nonneg (f := fun s => (D.p s x : Int))
      (fun s => by omega) h s
  omega

/-- The aggregated payoff of an action on a realization of zero mass is
    exactly zero: an impossible signal produces no value. -/
theorem jointPayoff_zero_mass (D : NoisyProblem) (x : Fin (D.nX + 1))
    (h : signalMass D x = 0) (a : Fin (D.nA + 1)) :
    sumFin D.nS (fun s => jointPayoff D s x a) = 0 := by
  have hp := p_eq_zero_of_signalMass_zero D x h
  have hz : (fun s => jointPayoff D s x a) = (fun _ => (0 : Int)) := by
    funext s
    simp [jointPayoff, hp s]
  rw [hz]
  exact sumFin_zero_fun D.nS

/-- The best action on a realization of zero mass is worth zero, without
    division and without exception. -/
theorem valueNoisySignal_zero_mass_cell (D : NoisyProblem)
    (x : Fin (D.nX + 1)) (h : signalMass D x = 0) :
    maxFin D.nA (fun a => sumFin D.nS (fun s => jointPayoff D s x a)) = 0 := by
  have hfun : (fun a => sumFin D.nS (fun s => jointPayoff D s x a)) =
      (fun _ => (0 : Int)) :=
    funext (fun a => jointPayoff_zero_mass D x h a)
  rw [hfun, maxFin_zero_fun]

/-! ## Perfect information dominates every noisy signal

The decisive step is a factorization lemma: for nonnegative weights, the sum
of the per-realization maxima is at most the maximum of the sum. This is the
algebraic form of Blackwell's argument — a decision maker who knows the state
can always apply the policy the signal would have prescribed, so perfect
information cannot be worth less. -/

/-- **Factorization by state.** For nonnegative weights `w` and payoffs
    `v`, `Σ_x max_a (w x * v a) ≤ max_a ((Σ_x w x) * v a)`.

    This is the step that moves from "one action per realization" to "one
    action per state". The case `Σ w = 0` is treated separately (all weights
    are zero, both sides are zero); otherwise the index attaining the maximum
    of the sum dominates every payoff, and positivity of the mass allows the
    simplification. -/
theorem sumFin_maxFin_mul_le {m n : Nat} (w : Fin m → Int)
    (hw : ∀ x, 0 ≤ w x) (v : Fin (n + 1) → Int) :
    sumFin m (fun x => maxFin n (fun a => w x * v a)) ≤
    maxFin n (fun a => sumFin m w * v a) := by
  by_cases hzero : sumFin m w = 0
  · have hw0 : ∀ x, w x = 0 := eq_zero_of_sumFin_nonneg hw hzero
    have hL : sumFin m (fun x => maxFin n (fun a => w x * v a)) = 0 := by
      have hz : ∀ x : Fin m, maxFin n (fun a => w x * v a) = 0 := by
        intro x
        have hfun : (fun a => w x * v a) = (fun _ => (0 : Int)) := by
          funext a
          simp [hw0 x]
        rw [hfun, maxFin_zero_fun]
      rw [sumFin_congr hz, sumFin_zero_fun]
    have hR : maxFin n (fun a => sumFin m w * v a) = 0 := by
      have hfun : (fun a => sumFin m w * v a) = (fun _ => (0 : Int)) := by
        funext a
        simp [hzero]
      rw [hfun, maxFin_zero_fun]
    rw [hL, hR]
    omega
  · have hpos : 0 < sumFin m w := by
      have := sumFin_nonneg hw
      omega
    have hstar : ∀ a : Fin (n + 1), v a ≤ v (argmaxFin n (fun a => sumFin m w * v a)) := by
      intro a
      exact Int.le_of_mul_le_mul_left (le_argmaxFin (fun a => sumFin m w * v a) a) hpos
    have hbound : ∀ x : Fin m,
        maxFin n (fun a => w x * v a) ≤ w x * v (argmaxFin n (fun a => sumFin m w * v a)) := by
      intro x
      apply maxFin_le
      intro a
      exact Int.mul_le_mul_of_nonneg_left (hstar a) (hw x)
    calc sumFin m (fun x => maxFin n (fun a => w x * v a))
        ≤ sumFin m (fun x => w x * v (argmaxFin n (fun a => sumFin m w * v a))) :=
          sumFin_mono hbound
      _ = sumFin m w * v (argmaxFin n (fun a => sumFin m w * v a)) := by
          rw [sumFin_congr (fun x =>
                Int.mul_comm (w x) (v (argmaxFin n (fun a => sumFin m w * v a)))),
              sumFin_mul_left, Int.mul_comm]
      _ ≤ maxFin n (fun a => sumFin m w * v a) :=
          le_maxFin (fun a => sumFin m w * v a) _

/-- **Perfect information dominates every noisy signal.** Even in the
    unnormalized joint representation, where values are raw. -/
theorem valueNoisySignal_le_valueNoisyPerfect (D : NoisyProblem) :
    valueNoisySignal D ≤ valueNoisyPerfect D := by
  unfold valueNoisySignal valueNoisyPerfect
  have hstep : sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a =>
        sumFin D.nS (fun s => jointPayoff D s x a))) ≤
      sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s =>
        maxFin D.nA (fun a => jointPayoff D s x a))) :=
    sumFin_mono (fun x => maxFin_sumFin_le (fun s a => jointPayoff D s x a))
  have hcomm : sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s =>
        maxFin D.nA (fun a => jointPayoff D s x a))) =
      sumFin D.nS (fun s => sumFin (D.nX + 1) (fun x =>
        maxFin D.nA (fun a => jointPayoff D s x a))) :=
    sumFin_comm _
  have hper : sumFin D.nS (fun s => sumFin (D.nX + 1) (fun x =>
        maxFin D.nA (fun a => jointPayoff D s x a))) ≤
      sumFin D.nS (fun s => maxFin D.nA (fun a => priorMass D s * D.u s a)) := by
    apply sumFin_mono
    intro s
    have hw : ∀ x : Fin (D.nX + 1), 0 ≤ (D.p s x : Int) := fun x => by omega
    have := sumFin_maxFin_mul_le (m := D.nX + 1) (n := D.nA)
      (w := fun x => (D.p s x : Int)) hw (v := fun a => D.u s a)
    simpa [jointPayoff, priorMass] using this
  rw [hcomm] at hstep
  exact Int.le_trans hstep hper

/-! ## Sign of the values: what carries it, and what does not

The three values of this module are **raw**, and nothing in `NoisyProblem`
constrains the sign of the payoffs `u : Fin nS → Fin (nA + 1) → Int`. A
well-formed instance can therefore be worth strictly less than zero: with
`nS = 1`, `nA = 1`, `nX = 1`, `p ≡ 1`, `u ≡ -1`, we have `priorMass = 1`,
each realization has mass 1, the best action is worth -1 in each state, and
`valueNoisySignal = -2`.

Nonnegativity is therefore **not** a property of the type: it is a property
under hypothesis. It is stated and proved here, rather than left implicit in
a docstring. -/

/-- Payoffs are nonnegative everywhere: the hypothesis that carries the
    sign of the module's values. -/
def NonnegPayouts (D : NoisyProblem) : Prop :=
  ∀ (s : Fin D.nS) (a : Fin (D.nA + 1)), 0 ≤ D.u s a

/-- A marginal weight is nonnegative: it is a sum of natural weights. -/
theorem priorMass_nonneg (D : NoisyProblem) (s : Fin D.nS) :
    0 ≤ priorMass D s := by
  unfold priorMass
  exact sumFin_nonneg (fun x => Int.natCast_nonneg (D.p s x))

/-- A joint payoff is nonnegative as soon as payoffs are. -/
theorem jointPayoff_nonneg (D : NoisyProblem) (h : NonnegPayouts D)
    (s : Fin D.nS) (x : Fin (D.nX + 1)) (a : Fin (D.nA + 1)) :
    0 ≤ jointPayoff D s x a := by
  unfold jointPayoff
  exact Int.mul_nonneg (Int.natCast_nonneg (D.p s x)) (h s a)

/-- **The value of the uninformed decision maker is nonnegative** under
    nonnegative payoffs. -/
theorem valueNoisyNoInfo_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisyNoInfo D := by
  unfold valueNoisyNoInfo
  refine Int.le_trans ?_ (le_maxFin (fun a =>
    sumFin D.nS (fun s => priorMass D s * D.u s a)) 0)
  exact sumFin_nonneg (fun s => Int.mul_nonneg (priorMass_nonneg D s) (h s 0))

/-- **The raw value of a noisy signal is nonnegative** under nonnegative
    payoffs. -/
theorem valueNoisySignal_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisySignal D := by
  unfold valueNoisySignal
  apply sumFin_nonneg
  intro x
  refine Int.le_trans ?_ (le_maxFin (fun a =>
    sumFin D.nS (fun s => jointPayoff D s x a)) 0)
  exact sumFin_nonneg (fun s => jointPayoff_nonneg D h s x 0)

/-- **The value of perfect information is nonnegative** under nonnegative
    payoffs. -/
theorem valueNoisyPerfect_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisyPerfect D := by
  unfold valueNoisyPerfect
  apply sumFin_nonneg
  intro s
  refine Int.le_trans ?_ (le_maxFin (fun a => priorMass D s * D.u s a) 0)
  exact Int.mul_nonneg (priorMass_nonneg D s) (h s 0)

/-- Perfectly informed, the decision maker of the noisy umbrella is worth
    20 (marginal weight 4 in each state, best payoff 2 then 3). -/
theorem noisyUmbrella_valueNoisyPerfect :
    valueNoisyPerfect noisyUmbrella = 20 := by decide

/-- The complete chain on the example: uninformed (8) ≤ informed (12) ≤
    perfectly informed (20). -/
theorem noisyUmbrella_chain :
    valueNoisyNoInfo noisyUmbrella ≤ valueNoisySignal noisyUmbrella ∧
    valueNoisySignal noisyUmbrella ≤ valueNoisyPerfect noisyUmbrella := by
  constructor
  · exact valueNoisyNoInfo_le_valueNoisySignal noisyUmbrella
  · exact valueNoisySignal_le_valueNoisyPerfect noisyUmbrella

/-! ## Axiom anchors

The axioms of the module's theorems, printed by `lake build`: the claim
"neither `sorryAx`, nor `native_decide`, nor `Classical.choice`" becomes
replayable by the next reader, instead of living only in a PR body. -/

#print axioms sumFin_jointPayoff
#print axioms valueNoisyNoInfo_le_valueNoisySignal
#print axioms noisyUmbrella_valueNoisyNoInfo
#print axioms noisyUmbrella_valueNoisySignal
#print axioms noisyUmbrella_strict_gain
#print axioms sumFin_nonneg
#print axioms eq_zero_of_sumFin_nonneg
#print axioms p_eq_zero_of_signalMass_zero
#print axioms jointPayoff_zero_mass
#print axioms valueNoisySignal_zero_mass_cell
#print axioms sumFin_maxFin_mul_le
#print axioms valueNoisySignal_le_valueNoisyPerfect
#print axioms priorMass_nonneg
#print axioms jointPayoff_nonneg
#print axioms valueNoisyNoInfo_nonneg
#print axioms valueNoisySignal_nonneg
#print axioms valueNoisyPerfect_nonneg
#print axioms noisyUmbrella_valueNoisyPerfect
#print axioms noisyUmbrella_chain

