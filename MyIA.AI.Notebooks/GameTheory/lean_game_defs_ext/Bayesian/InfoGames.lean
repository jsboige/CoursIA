/-
  Information Can Hurt in Games (counterexample, kernel-checked)
  ==============================================================

  `Information.lean` proves that a *single* decision maker never loses
  by observing a signal (Blackwell monotonicity). This file shows the
  result is genuinely one-player: in a game, giving one player strictly
  more information can strictly *lower* their equilibrium payoff.

  The example (a classic two-state, 2x2 construction): a state
  θ ∈ {0, 1} is drawn with equal weights. Player 1 (row, actions T/B)
  never observes θ. We compare two scenarios for player 2 (column,
  actions l/r):

  - `gNoInfo`: player 2 does not observe θ either. Payoffs are the
    fold of the state-dependent tables over θ (an ex-ante reduction:
    one type per player, payoffs summed over states — see
    `infoHurts_reduction`).
  - `gInfo`: player 2 privately observes θ (two types).

  State-dependent payoffs (player 1, player 2):

            θ = 0:  l        r            θ = 1:  l        r
        T        (2, 3)   (0, 0)      T        (2, 2)   (0, 3)
        B        (0, 2)   (0, 0)      B        (0, 0)   (4, 1)

  Uninformed, `l` strictly dominates for player 2 (3+2 > 0+3 against T,
  2+0 > 0+1 against B), so the unique BNE is (T, l): player 2 collects
  weight-total 5. Informed, type θ=1 cannot commit to `l` anymore — `r`
  is strictly dominant for that type (3 > 2 against T, 1 > 0 against
  B), and type θ=0 keeps `l`. Player 2's action now reveals the state,
  and player 1's best response flips from T to B (2+0 < 0+4), leaving
  player 2 with 2+1 = 3 < 5. Knowledge destroys the ability to commit:
  player 2 would pay to NOT see the signal.

  Both games carry the same total prior weight scale (each value below
  is twice the true expectation), so the payoffs 3 and 5 are directly
  comparable.

  Equilibrium uniqueness is established for *all* strategy profiles by
  reducing an arbitrary strategy to a canonical constructor
  (`mkS1g`/`mkS2g`, an eta-expansion over `Fin` literals) and then
  deciding the resulting finite statement by kernel computation.

  See #2610 (GT-Lean formalization, Bayesian phase 4).
-/

import Bayesian.BNE

/-- The informed game: player 2 privately observes the state θ (their
    type), player 1 has a single type. Equal prior weights. -/
def gInfo : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      (if a1.val = 0 then (if a2.val = 0 then 2 else 0) else 0)
    else
      (if a1.val = 0 then (if a2.val = 0 then 2 else 0)
       else (if a2.val = 0 then 0 else 4))
  u2 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      (if a1.val = 0 then (if a2.val = 0 then 3 else 0)
       else (if a2.val = 0 then 2 else 0))
    else
      (if a1.val = 0 then (if a2.val = 0 then 2 else 3)
       else (if a2.val = 0 then 0 else 1))

/-- The uninformed benchmark: nobody observes θ, so both players have a
    single type and payoffs are summed over the two states (ex-ante
    reduction of `gInfo` for an uninformed player 2). -/
def gNoInfo : BayesGame2 where
  nT1 := 1
  nT2 := 1
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 =>
    if a1.val = 0 then (if a2.val = 0 then 4 else 0)
    else (if a2.val = 0 then 0 else 4)
  u2 := fun _ _ a1 a2 =>
    if a1.val = 0 then (if a2.val = 0 then 5 else 3)
    else (if a2.val = 0 then 2 else 1)

/-- Sanity check: `gNoInfo`'s payoffs are exactly `gInfo`'s summed over
    the two states — the uninformed game is the faithful ex-ante
    reduction, not an unrelated game. -/
theorem infoHurts_reduction :
    ∀ a1 a2 : Fin 2,
      gNoInfo.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gInfo.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 +
        gInfo.u1 ⟨0, by decide⟩ ⟨1, by decide⟩ a1 a2 ∧
      gNoInfo.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gInfo.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 +
        gInfo.u2 ⟨0, by decide⟩ ⟨1, by decide⟩ a1 a2 := by
  decide

/-! ### Canonical strategy constructors (informed game) -/

/-- Player 1's strategies in `gInfo` are constants (one type). -/
def mkS1g (x : Fin 2) : Strategy1 gInfo := fun _ => x

/-- Player 2's strategies in `gInfo`, from the two type-contingent
    actions. -/
def mkS2g (y z : Fin 2) : Strategy2 gInfo :=
  fun t2 => if t2.val = 0 then y else z

/-- Every strategy of player 1 is a canonical constant. -/
theorem s1g_eta (s1 : Strategy1 gInfo) : s1 = mkS1g (s1 ⟨0, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-- Every strategy of player 2 is determined by its two values. -/
theorem s2g_eta (s2 : Strategy2 gInfo) :
    s2 = mkS2g (s2 ⟨0, by decide⟩) (s2 ⟨1, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact j'.elim0

/-! ### Equilibrium analysis of the informed game -/

/-- (B, follow-the-state) is a BNE of the informed game. -/
theorem gInfo_bne :
    isBNE gInfo (mkS1g ⟨1, by decide⟩) (mkS2g ⟨0, by decide⟩ ⟨1, by decide⟩) := by
  decide

/-- Over canonical strategies, the BNE of `gInfo` is unique: player 1
    plays B and player 2 plays l on θ=0, r on θ=1. -/
theorem gInfo_unique_aux :
    ∀ x y z : Fin 2,
      isBNE gInfo (mkS1g x) (mkS2g y z) →
        x = ⟨1, by decide⟩ ∧ y = ⟨0, by decide⟩ ∧ z = ⟨1, by decide⟩ := by
  decide

/-- Over canonical strategies, every BNE of `gInfo` pays player 2
    exactly 3. -/
theorem gInfo_exAnteU2_aux :
    ∀ x y z : Fin 2,
      isBNE gInfo (mkS1g x) (mkS2g y z) →
        exAnteU2 gInfo (mkS1g x) (mkS2g y z) = 3 := by
  decide

/-- The informed game has an essentially unique BNE. -/
theorem gInfo_unique (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (h : isBNE gInfo s1 s2) :
    s1 = mkS1g ⟨1, by decide⟩ ∧ s2 = mkS2g ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  rw [s1g_eta s1, s2g_eta s2] at h
  have hu := gInfo_unique_aux _ _ _ h
  exact ⟨by rw [s1g_eta s1, hu.1], by rw [s2g_eta s2, hu.2.1, hu.2.2]⟩

/-- In every BNE of the informed game, player 2 earns 3. -/
theorem gInfo_bne_payoff (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (h : isBNE gInfo s1 s2) : exAnteU2 gInfo s1 s2 = 3 := by
  rw [s1g_eta s1, s2g_eta s2] at h ⊢
  exact gInfo_exAnteU2_aux _ _ _ h

/-! ### Equilibrium analysis of the uninformed game -/

/-- Player 1's strategies in `gNoInfo` are constants. -/
def mkS1n (x : Fin 2) : Strategy1 gNoInfo := fun _ => x

/-- Player 2's strategies in `gNoInfo` are constants. -/
def mkS2n (y : Fin 2) : Strategy2 gNoInfo := fun _ => y

theorem s1n_eta (s1 : Strategy1 gNoInfo) : s1 = mkS1n (s1 ⟨0, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

theorem s2n_eta (s2 : Strategy2 gNoInfo) : s2 = mkS2n (s2 ⟨0, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-- (T, l) is a BNE of the uninformed game. -/
theorem gNoInfo_bne :
    isBNE gNoInfo (mkS1n ⟨0, by decide⟩) (mkS2n ⟨0, by decide⟩) := by
  decide

/-- Over canonical strategies, every BNE of `gNoInfo` pays player 2
    exactly 5 (the BNE (T, l) is in fact unique, by strict dominance
    of l). -/
theorem gNoInfo_exAnteU2_aux :
    ∀ x y : Fin 2,
      isBNE gNoInfo (mkS1n x) (mkS2n y) →
        exAnteU2 gNoInfo (mkS1n x) (mkS2n y) = 5 := by
  decide

/-- In every BNE of the uninformed game, player 2 earns 5. -/
theorem gNoInfo_bne_payoff (s1 : Strategy1 gNoInfo) (s2 : Strategy2 gNoInfo)
    (h : isBNE gNoInfo s1 s2) : exAnteU2 gNoInfo s1 s2 = 5 := by
  rw [s1n_eta s1, s2n_eta s2] at h ⊢
  exact gNoInfo_exAnteU2_aux _ _ h

/-! ### Punchline -/

/-- **Information can hurt in games.** In every equilibrium, the
    informed player 2 earns strictly less (3) than in every equilibrium
    of the game where nobody observes the state (5): observing the
    signal destroys player 2's ability to commit to `l`, reveals the
    state through their action, and triggers a best-response switch by
    player 1 that costs more than the informational gain. Contrast with
    `valueNoInfo_le_valueSignal` (`Information.lean`): with a single
    decision maker, information never hurts. -/
theorem information_hurts
    (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (t1 : Strategy1 gNoInfo) (t2 : Strategy2 gNoInfo)
    (hI : isBNE gInfo s1 s2) (hN : isBNE gNoInfo t1 t2) :
    exAnteU2 gInfo s1 s2 < exAnteU2 gNoInfo t1 t2 := by
  rw [gInfo_bne_payoff s1 s2 hI, gNoInfo_bne_payoff t1 t2 hN]
  decide
