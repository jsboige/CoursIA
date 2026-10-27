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
`nS = 1`, `nA = 1`, `nX = 1`, `p ≡ 1`, `u ≡ -1` (two realizations, each of
mass 1 and marginal 2), the best action is worth -1 in each state and the
three values are -2; the raw gain of the signal is then zero, nonnegative but
not strictly positive.

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

/-! ## The independent case: a factorized table

A joint table **independent** of the state — the weight of cell `(s, x)`
is the product of the state weight `s` by a realization weight `q x`
that does not depend on the state — describes a signal that teaches
nothing: the posterior stays the prior, and the gross gain of the signal
is **exactly zero**. This is the negative control of the `voi` bench
(`forage-non-informatif`), and the only way to distinguish "a table
encoding information" from "a table encoding a prior".

The proof factors out a common measure: the factor `Σ_x q x` exits both
the sum over realizations and the maximum over actions, thanks to
`maxFin_mul_nonneg`. -/

/-- Total mass of the realization weights of an independent table: this is
    the scale factor common to both values. -/
def independentMass (nX : Nat) (q : Fin (nX + 1) → Nat) : Int :=
  sumFin (nX + 1) (fun x => (q x : Int))

/-- The total mass of an independent table is non-negative. -/
theorem independentMass_nonneg (nX : Nat) (q : Fin (nX + 1) → Nat) :
    0 ≤ independentMass nX q := by
  unfold independentMass
  exact sumFin_nonneg (fun x => Int.natCast_nonneg (q x))

/-- Joint table **independent** of the state: the weight of cell `(s, x)`
    is the product of the state weight `s` and a realization weight
    `q x` that does not depend on the state. -/
@[reducible]
def independentTable (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) : NoisyProblem where
  nS := nS
  nA := nA
  nX := nX
  p := fun s x => w s * q x
  u := u

/-- The number of states of the independent table is that of the parameter. -/
theorem independentTable_nS (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) :
    (independentTable nS nA nX w q u).nS = nS := rfl

/-- The number of actions of the independent table is that of the parameter. -/
theorem independentTable_nA (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) :
    (independentTable nS nA nX w q u).nA = nA := rfl

/-- The number of realizations of the independent table is that of the
    parameter. -/
theorem independentTable_nX (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) :
    (independentTable nS nA nX w q u).nX = nX := rfl

/-- The joint weight of the independent table is the product of the state
    weight and the realization weight. -/
theorem independentTable_p (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int)
    (s : Fin nS) (x : Fin (nX + 1)) :
    (independentTable nS nA nX w q u).p s x = w s * q x := rfl

/-- The payoffs of the independent table are those of the parameter. -/
theorem independentTable_u (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int)
    (s : Fin nS) (a : Fin (nA + 1)) :
    (independentTable nS nA nX w q u).u s a = u s a := rfl

/-- The marginal weight of a state in an independent table is the state
    weight times the total realization mass. -/
theorem priorMass_independent (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) (s : Fin nS) :
    priorMass (independentTable nS nA nX w q u) s =
      (w s : Int) * independentMass nX q := by
  unfold priorMass independentTable independentMass
  have h : ∀ x : Fin (nX + 1),
      (↑(w s * q x) : Int) = (↑(w s) : Int) * (↑(q x) : Int) := fun x => rfl
  rw [sumFin_congr h]
  exact sumFin_mul_left _ _

/-- The payoff aggregated over one realization of an independent table
    factors: the realization weight exits the sum over states. -/
theorem sumFin_independent_joint (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int)
    (x : Fin (nX + 1)) (a : Fin (nA + 1)) :
    sumFin nS (fun s => jointPayoff (independentTable nS nA nX w q u) s x a) =
      (q x : Int) * sumFin nS (fun s => (w s : Int) * u s a) := by
  have h : ∀ s : Fin nS,
      (↑(w s * q x) : Int) * u s a = (q x : Int) * ((w s : Int) * u s a) := by
    intro s
    change (↑(w s) * ↑(q x)) * u s a = (q x : Int) * ((w s : Int) * u s a)
    rw [Int.mul_assoc, Int.mul_left_comm]
  unfold jointPayoff independentTable
  rw [sumFin_congr h]
  exact sumFin_mul_left _ _

/-- The aggregated payoff of one action on the prior of an independent
    table factors the same way, through the total mass. -/
theorem sumFin_independent_prior (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int)
    (a : Fin (nA + 1)) :
    sumFin nS (fun s => priorMass (independentTable nS nA nX w q u) s * u s a) =
      independentMass nX q * sumFin nS (fun s => (w s : Int) * u s a) := by
  have h : ∀ s : Fin nS,
      priorMass (independentTable nS nA nX w q u) s * u s a =
        independentMass nX q * ((w s : Int) * u s a) := by
    intro s
    rw [priorMass_independent nS nA nX w q u s, Int.mul_assoc, Int.mul_left_comm]
  rw [sumFin_congr h]
  exact sumFin_mul_left _ _

/-- **No-signal value of an independent table.** It equals the total mass
    times the value of the corresponding deterministic problem. -/
theorem valueNoisyNoInfo_independent (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) :
    valueNoisyNoInfo (independentTable nS nA nX w q u) =
      independentMass nX q *
        maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a)) := by
  unfold valueNoisyNoInfo
  simp only [independentTable_nS, independentTable_nA]
  have h : (fun a => sumFin nS (fun s =>
        priorMass (independentTable nS nA nX w q u) s * u s a)) =
      (fun a => independentMass nX q * sumFin nS (fun s => (w s : Int) * u s a)) := by
    funext a
    exact sumFin_independent_prior nS nA nX w q u a
  rw [h]
  exact maxFin_mul_nonneg (independentMass nX q) (independentMass_nonneg nX q) nA _

/-- **Signal value of an independent table.** It equals the total mass
    times the same deterministic value: an independent signal brings
    nothing. -/
theorem valueNoisySignal_independent (nS nA nX : Nat) (w : Fin nS → Nat)
    (q : Fin (nX + 1) → Nat) (u : Fin nS → Fin (nA + 1) → Int) :
    valueNoisySignal (independentTable nS nA nX w q u) =
      independentMass nX q *
        maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a)) := by
  unfold valueNoisySignal
  simp only [independentTable_nS, independentTable_nA, independentTable_nX]
  have hcell : ∀ x : Fin (nX + 1),
      maxFin nA (fun a => sumFin nS (fun s =>
        jointPayoff (independentTable nS nA nX w q u) s x a)) =
        (q x : Int) * maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a)) := by
    intro x
    have h : (fun a => sumFin nS (fun s =>
          jointPayoff (independentTable nS nA nX w q u) s x a)) =
        (fun a => (q x : Int) * sumFin nS (fun s => (w s : Int) * u s a)) := by
      funext a
      exact sumFin_independent_joint nS nA nX w q u x a
    rw [h]
    exact maxFin_mul_nonneg (q x : Int) (Int.natCast_nonneg _) nA _
  rw [sumFin_congr hcell]
  have hswap : (fun x : Fin (nX + 1) => (q x : Int) *
      maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a))) =
      (fun x : Fin (nX + 1) => maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a)) *
        (q x : Int)) := by
    funext x
    exact Int.mul_comm _ _
  rw [hswap]
  rw [sumFin_mul_left (maxFin nA (fun a => sumFin nS (fun s => (w s : Int) * u s a)))
      (fun x => (q x : Int))]
  have hm : sumFin (nX + 1) (fun x => (q x : Int)) = independentMass nX q := by
    unfold independentMass
    rfl
  rw [hm]
  exact Int.mul_comm _ _

/-- **An independent table has exactly zero gross gain.** A decision maker
    who observes the signal is worth exactly what he is worth without
    observing it: the information is zero, not "small". -/
theorem valueNoisySignal_eq_valueNoisyNoInfo_independent (nS nA nX : Nat)
    (w : Fin nS → Nat) (q : Fin (nX + 1) → Nat)
    (u : Fin nS → Fin (nA + 1) → Int) :
    valueNoisySignal (independentTable nS nA nX w q u) =
      valueNoisyNoInfo (independentTable nS nA nX w q u) := by
  rw [valueNoisySignal_independent, valueNoisyNoInfo_independent]

/-- Explicit negative control: a signal **independent** of the state (the
    realization weight does not depend on the state) has exactly zero
    gross gain. This is the counterpart of `noisyUmbrella`, which is
    informative with strictly positive gain. -/
def independentUmbrella : NoisyProblem :=
  independentTable 2 1 1 (fun _ => 1) (fun x => if x.val = 0 then 3 else 1)
    (fun s a => if s.val = 0 then (if a.val = 0 then 2 else -3)
      else (if a.val = 0 then 0 else 3))

/-- Uninformed, the independent-signal umbrella is worth 8 (total mass 4,
    deterministic value 2). -/
theorem independentUmbrella_valueNoisyNoInfo :
    valueNoisyNoInfo independentUmbrella = 8 := by decide

/-- Informed by an independent signal, the umbrella is worth **still** 8:
    the signal brings nothing. -/
theorem independentUmbrella_valueNoisySignal :
    valueNoisySignal independentUmbrella = 8 := by decide

/-- The gross gain of the independent signal is exactly zero. -/
theorem independentUmbrella_zero_gain :
    valueNoisyNoInfo independentUmbrella = valueNoisySignal independentUmbrella := by
  decide

/-! ## The bridge to deterministic signals

A joint table whose support is the graph of a deterministic signal `σ` —
the weight of cell `(s, x)` is the state weight `s` if `σ s = x`, and
zero otherwise — must give **exactly** the same values as the
deterministic organ `Information.lean`. Without this bridge, the two
semantics could diverge; with it, they are sealed by a theorem. -/

/-- The joint table of the **deterministic** signal `σ`: the weight of
    cell `(s, x)` is the state weight `s` if `σ s = x`, and zero
    otherwise. This is the special case where the realization carries all
    the information. -/
@[reducible]
def noisyOfSignal (D : DecisionProblem) {m : Nat} (σ : Signal D m) : NoisyProblem where
  nS := D.nS
  nA := D.nA
  nX := m
  p := fun s x => if σ s = x then D.w s else 0
  u := D.u

/-- The number of states of the deterministic-signal table is that of the
    deterministic problem. -/
theorem noisyOfSignal_nS (D : DecisionProblem) {m : Nat} (σ : Signal D m) :
    (noisyOfSignal D σ).nS = D.nS := rfl

/-- The number of actions of the deterministic-signal table is that of the
    deterministic problem. -/
theorem noisyOfSignal_nA (D : DecisionProblem) {m : Nat} (σ : Signal D m) :
    (noisyOfSignal D σ).nA = D.nA := rfl

/-- The number of realizations of the deterministic-signal table is that
    of the signal. -/
theorem noisyOfSignal_nX (D : DecisionProblem) {m : Nat} (σ : Signal D m) :
    (noisyOfSignal D σ).nX = m := rfl

/-- The joint weight of the deterministic-signal table is concentrated on
    the graph of the signal. -/
theorem noisyOfSignal_p (D : DecisionProblem) {m : Nat} (σ : Signal D m)
    (s : Fin D.nS) (x : Fin (m + 1)) :
    (noisyOfSignal D σ).p s x = if σ s = x then D.w s else 0 := rfl

/-- The payoffs of the deterministic-signal table are those of the
    deterministic problem. -/
theorem noisyOfSignal_u (D : DecisionProblem) {m : Nat} (σ : Signal D m)
    (s : Fin D.nS) (a : Fin (D.nA + 1)) :
    (noisyOfSignal D σ).u s a = D.u s a := rfl

/-- The marginal weight of a state in the table of a deterministic signal
    is the state weight: the signal does not change the prior, it only
    reveals it. -/
theorem priorMass_noisyOfSignal (D : DecisionProblem) {m : Nat} (σ : Signal D m)
    (s : Fin D.nS) :
    priorMass (noisyOfSignal D σ) s = (D.w s : Int) := by
  unfold priorMass noisyOfSignal
  have h : (fun x : Fin (m + 1) => ((if σ s = x then D.w s else 0 : Nat) : Int)) =
      (fun x : Fin (m + 1) => if σ s = x then (D.w s : Int) else 0) := by
    funext x
    by_cases hxy : σ s = x <;> simp [hxy]
  rw [h]
  exact sumFin_single _ _

/-- **The bridge, no-information side.** The table of a deterministic
    signal is worth exactly the no-information value of the deterministic
    problem. -/
theorem valueNoisyNoInfo_noisyOfSignal (D : DecisionProblem) {m : Nat}
    (σ : Signal D m) :
    valueNoisyNoInfo (noisyOfSignal D σ) = valueNoInfo D := by
  unfold valueNoisyNoInfo valueNoInfo wu
  simp only [noisyOfSignal_nS, noisyOfSignal_nA]
  have h : (fun a => sumFin D.nS (fun s =>
        priorMass (noisyOfSignal D σ) s * D.u s a)) =
      (fun a => sumFin D.nS (fun s => (D.w s : Int) * D.u s a)) := by
    funext a
    rw [sumFin_congr (fun s => by rw [priorMass_noisyOfSignal D σ s])]
  rw [h]

/-- **The bridge, signal side.** The value of a deterministic signal,
    computed by the noisy organ, is **exactly** the value computed by the
    deterministic organ: the two semantics cannot diverge. -/
theorem valueNoisySignal_noisyOfSignal (D : DecisionProblem) {m : Nat}
    (σ : Signal D m) :
    valueNoisySignal (noisyOfSignal D σ) = valueSignal D σ := by
  unfold valueNoisySignal valueSignal wu
  simp only [noisyOfSignal_nS, noisyOfSignal_nA, noisyOfSignal_nX]
  have hper : ∀ (x : Fin (m + 1)) (a : Fin (D.nA + 1)) (s : Fin D.nS),
      jointPayoff (noisyOfSignal D σ) s x a =
        (if σ s = x then (D.w s : Int) * D.u s a else 0) := by
    intro x a s
    unfold jointPayoff
    by_cases hσ : σ s = x <;> simp [hσ] <;> omega
  have h : ∀ x : Fin (m + 1),
      maxFin D.nA (fun a => sumFin D.nS (fun s => jointPayoff (noisyOfSignal D σ) s x a)) =
      maxFin D.nA (fun a => sumFin D.nS (fun s => if σ s = x then (D.w s : Int) * D.u s a else 0)) := by
    intro x
    have ha : (fun a => sumFin D.nS (fun s => jointPayoff (noisyOfSignal D σ) s x a)) =
        (fun a => sumFin D.nS (fun s => if σ s = x then (D.w s : Int) * D.u s a else 0)) := by
      funext a
      rw [sumFin_congr (fun s => hper x a s)]
    rw [ha]
  exact sumFin_congr h

/-- **The bridge, perfect-information side.** The two semantics also agree
    on the value of perfect information. -/
theorem valueNoisyPerfect_noisyOfSignal (D : DecisionProblem) {m : Nat}
    (σ : Signal D m) :
    valueNoisyPerfect (noisyOfSignal D σ) = valuePerfect D := by
  unfold valueNoisyPerfect valuePerfect
  simp only [noisyOfSignal_nS, noisyOfSignal_nA]
  have h : (fun s => maxFin D.nA (fun a =>
        priorMass (noisyOfSignal D σ) s * D.u s a)) =
      (fun s => maxFin D.nA (fun a => (D.w s : Int) * D.u s a)) := by
    funext s
    rw [priorMass_noisyOfSignal D σ s]
  rw [h]
  rfl

/-- Concrete control of the bridge: the deterministic umbrella
    (`umbrella` from `Information.lean`) gives the same values under both
    semantics. -/
theorem umbrella_bridge :
    valueNoisyNoInfo (noisyOfSignal umbrella (fun _ => (0 : Fin 1))) = valueNoInfo umbrella ∧
    valueNoisySignal (noisyOfSignal umbrella (fun _ => (0 : Fin 1))) =
      valueSignal umbrella (fun _ => (0 : Fin 1)) := by
  constructor
  · exact valueNoisyNoInfo_noisyOfSignal umbrella (fun _ => (0 : Fin 1))
  · exact valueNoisySignal_noisyOfSignal umbrella (fun _ => (0 : Fin 1))

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
#print axioms valueNoisyNoInfo_independent
#print axioms valueNoisySignal_independent
#print axioms independentUmbrella_zero_gain
#print axioms valueNoisyNoInfo_noisyOfSignal
#print axioms valueNoisySignal_noisyOfSignal
#print axioms valueNoisyPerfect_noisyOfSignal

