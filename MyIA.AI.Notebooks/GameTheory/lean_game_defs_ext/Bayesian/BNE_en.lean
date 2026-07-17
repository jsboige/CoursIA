/-
  Bayesian Nash Equilibrium (interim formulation)
  ===============================================

  - `isBNE`: a strategy profile is a BNE when no type of either player
    has a profitable unilateral action deviation, in interim expected
    utility. Quantifiers range over `Fin` types and actions only, so
    the property is decidable (`decide` works on concrete games).
  - `exAnteU1_le_of_interim_best`: the one-shot deviation principle in
    this finite setting — interim optimality implies ex-ante optimality
    against arbitrary type-contingent deviations.
  - `isBNE_scaleW`: BNE is invariant under rescaling the prior weights
    by a positive constant (normalization-independence: the `Nat`
    weights stand in for any probability measure proportional to them).

  See #2610 (GT-Lean formalization, Bayesian phase 1).
-/

import Bayesian.Types_en

/-- Bayesian Nash equilibrium, interim formulation: for every type of
    each player, the prescribed action maximizes interim expected
    utility against the opponent's strategy.

    Reducible so that the `Decidable` instance is found by unfolding
    (conjunction of `∀` over `Fin` of decidable `Int` comparisons). -/
@[reducible] def isBNE (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Prop :=
  (∀ t1 : Fin g.nT1, ∀ a : Fin g.nA1,
      interimU1 g t1 a s2 ≤ interimU1 g t1 (s1 t1) s2) ∧
  (∀ t2 : Fin g.nT2, ∀ a : Fin g.nA2,
      interimU2 g t2 a s1 ≤ interimU2 g t2 (s2 t2) s1)

/-- One-shot deviation principle, player 1 side: if every type of
    player 1 plays an interim best response, then no type-contingent
    deviation `s1'` improves player 1's ex-ante expected utility. -/
theorem exAnteU1_le_of_interim_best (g : BayesGame2)
    {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : ∀ t1 a, interimU1 g t1 a s2 ≤ interimU1 g t1 (s1 t1) s2)
    (s1' : Strategy1 g) :
    exAnteU1 g s1' s2 ≤ exAnteU1 g s1 s2 :=
  sumFin_mono (fun t1 => h t1 (s1' t1))

/-- One-shot deviation principle, player 2 side. -/
theorem exAnteU2_le_of_interim_best (g : BayesGame2)
    {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : ∀ t2 a, interimU2 g t2 a s1 ≤ interimU2 g t2 (s2 t2) s1)
    (s2' : Strategy2 g) :
    exAnteU2 g s1 s2' ≤ exAnteU2 g s1 s2 :=
  sumFin_mono (fun t2 => h t2 (s2' t2))

/-- A BNE is also an ex-ante Nash equilibrium: no player gains from
    any type-contingent unilateral deviation. -/
theorem bne_exAnte (g : BayesGame2) {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : isBNE g s1 s2) :
    (∀ s1', exAnteU1 g s1' s2 ≤ exAnteU1 g s1 s2) ∧
    (∀ s2', exAnteU2 g s1 s2' ≤ exAnteU2 g s1 s2) :=
  ⟨exAnteU1_le_of_interim_best g h.1, exAnteU2_le_of_interim_best g h.2⟩

/-- The same game with all prior weights multiplied by `c`. -/
@[reducible] def scaleW (g : BayesGame2) (c : Nat) : BayesGame2 :=
  { g with w := fun t1 t2 => c * g.w t1 t2 }

theorem interimU1_scaleW (g : BayesGame2) (c : Nat)
    (t1 : Fin g.nT1) (a : Fin g.nA1) (s2 : Strategy2 g) :
    interimU1 (scaleW g c) t1 a s2 = (c : Int) * interimU1 g t1 a s2 := by
  unfold interimU1
  rw [← sumFin_mul_left]
  apply sumFin_congr
  intro t2
  rw [Int.natCast_mul, Int.mul_assoc]

theorem interimU2_scaleW (g : BayesGame2) (c : Nat)
    (t2 : Fin g.nT2) (a : Fin g.nA2) (s1 : Strategy1 g) :
    interimU2 (scaleW g c) t2 a s1 = (c : Int) * interimU2 g t2 a s1 := by
  unfold interimU2
  rw [← sumFin_mul_left]
  apply sumFin_congr
  intro t1
  rw [Int.natCast_mul, Int.mul_assoc]

/-- BNE is invariant under positive rescaling of the prior weights.
    This is what makes unnormalized `Nat` weights a faithful encoding
    of a common prior: only ratios of weights matter. -/
theorem isBNE_scaleW (g : BayesGame2) (c : Nat) (hc : 0 < c)
    (s1 : Strategy1 g) (s2 : Strategy2 g) :
    isBNE (scaleW g c) s1 s2 ↔ isBNE g s1 s2 := by
  have hc' : (0 : Int) < (c : Int) := by omega
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨fun t1 a => ?_, fun t2 a => ?_⟩
    · have := h1 t1 a
      rw [interimU1_scaleW, interimU1_scaleW] at this
      exact Int.le_of_mul_le_mul_left this hc'
    · have := h2 t2 a
      rw [interimU2_scaleW, interimU2_scaleW] at this
      exact Int.le_of_mul_le_mul_left this hc'
  · intro ⟨h1, h2⟩
    refine ⟨fun t1 a => ?_, fun t2 a => ?_⟩
    · rw [interimU1_scaleW, interimU1_scaleW]
      exact Int.mul_le_mul_of_nonneg_left (h1 t1 a) (Int.le_of_lt hc')
    · rw [interimU2_scaleW, interimU2_scaleW]
      exact Int.mul_le_mul_of_nonneg_left (h2 t2 a) (Int.le_of_lt hc')
