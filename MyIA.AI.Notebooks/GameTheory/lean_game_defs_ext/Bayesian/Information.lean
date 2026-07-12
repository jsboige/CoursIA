/-
  Valeur de l'information dans les problèmes de décision (Blackwell, cas déterministe)
  =========================================================================

  Un unique décideur fait face à un ensemble fini d'états avec une prior
  `Nat` non normalisée (même encodage que `BayesGame2`) et choisit une
  action parmi un ensemble fini non vide. Un *signal déterministe* est une
  application des états vers les réalisations du signal — de manière
  équivalente, une partition finie de l'espace d'états. On formalise trois
  valeurs de référence :

  - `valueNoInfo` : choisir une action avant d'apprendre quoi que ce soit ;
  - `valueSignal σ` : observer la réalisation de `σ`, puis choisir une action
    optimalement à l'intérieur de chaque cellule de la partition ;
  - `valuePerfect` : apprendre l'état exactement, puis choisir.

  Théorèmes principaux (tous via le lemme maître `maxFin_sumFin_le` plus
  l'identité de double-comptage `sumFin_partition`) :

  - `valueNoInfo_le_valueSignal` : l'information ne nuit jamais à un
    décideur seul (la valeur de tout signal est non négative) ;
  - `valueSignal_mono` : monotonie de Blackwell pour les partitions — si
    `σ` est un raspberry (coarsening) de `τ` (i.e. `σ = h ∘ τ`), alors `τ`
    vaut au moins autant que `σ` ;
  - `valueSignal_le_valuePerfect` : l'information parfaite est le meilleur
    signal déterministe.

  Le fichier compagnon `InfoGames.lean` montre par contraste que dans un
  *jeu*, plus d'information peut strictement nuire au joueur qui la reçoit
  — la monotonie est un phénomène à un seul joueur.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 4).

  ---
  English:
  Value of Information in Decision Problems (Blackwell, deterministic case)
  =========================================================================

  A single decision maker faces a finite set of states with an
  unnormalized `Nat` prior (same encoding as `BayesGame2`) and picks one
  action from a nonempty finite set. A *deterministic signal* is a map
  from states to signal realizations — equivalently, a finite partition
  of the state space. We formalize three benchmark values:

  - `valueNoInfo`:   choose one action before learning anything;
  - `valueSignal σ`: observe `σ`'s realization, then choose an action
    optimally inside each cell of the partition;
  - `valuePerfect`:  learn the state exactly, then choose.

  Main theorems (all by the master lemma `maxFin_sumFin_le` plus the
  double-counting identity `sumFin_partition`):

  - `valueNoInfo_le_valueSignal`: information never hurts a single
    decision maker (the value of any signal is nonnegative);
  - `valueSignal_mono`: Blackwell monotonicity for partitions — if `σ`
    is a coarsening of `τ` (i.e. `σ = h ∘ τ`), then `τ` is worth at
    least as much as `σ`;
  - `valueSignal_le_valuePerfect`: perfect information is the best
    deterministic signal.

  The companion file `InfoGames.lean` shows by contrast that in a
  *game*, more information can strictly hurt the player who receives
  it — monotonicity is a one-player phenomenon.

  See #2610 (GT-Lean formalization, Bayesian phase 4).
-/

import Bayesian.Max

/-- Problème de décision fini à un seul agent avec une prior non normalisée.
    English: A finite single-agent decision problem with an unnormalized prior.
    There are `nS` states and `nA + 1` actions (the `+ 1` keeps the
    action set nonempty without carrying a positivity hypothesis). -/
structure DecisionProblem where
  /-- Nombre d'états du monde. English: Number of states of the world -/
  nS : Nat
  /-- Nombre d'actions moins un (les actions sont `Fin (nA + 1)`). English: Number of actions minus one (actions are `Fin (nA + 1)`) -/
  nA : Nat
  /-- Poids de prior non normalisé de chaque état. English: Unnormalized prior weight of each state -/
  w : Fin nS → Nat
  /-- Paiement de l'action choisie dans un état. English: Payoff of taking an action in a state -/
  u : Fin nS → Fin (nA + 1) → Int

/-- Paiement pondéré par la prior de l'action `a` dans l'état `s`.
    English: Prior-weighted payoff of action `a` in state `s`. -/
def wu (D : DecisionProblem) (s : Fin D.nS) (a : Fin (D.nA + 1)) : Int :=
  (D.w s : Int) * D.u s a

/-- Un signal déterministe avec `m + 1` réalisations possibles : il
    English: A deterministic signal with `m + 1` possible realizations: it
    announces a realization in each state, i.e. partitions the state
    space into (at most) `m + 1` cells. -/
def Signal (D : DecisionProblem) (m : Nat) := Fin D.nS → Fin (m + 1)

/-- Paiement espéré (non normalisé) d'un décideur non informé :
    English: Expected payoff (unnormalized) of an uninformed decision maker:
    pick the single action with the best prior-weighted payoff. -/
def valueNoInfo (D : DecisionProblem) : Int :=
  maxFin D.nA (fun a => sumFin D.nS (fun s => wu D s a))

/-- Paiement espéré d'un décideur observant le signal `σ` : à l'intérieur
    English: Expected payoff of a decision maker observing signal `σ`: inside
    each cell `k` of the partition, pick the best action for the prior
    restricted to that cell, then add up over cells. -/
def valueSignal (D : DecisionProblem) {m : Nat} (σ : Signal D m) : Int :=
  sumFin (m + 1) (fun k => maxFin D.nA (fun a =>
    sumFin D.nS (fun s => if σ s = k then wu D s a else 0)))

/-- Paiement espéré d'un décideur pleinement informé : choisir la meilleure
    English: Expected payoff of a fully informed decision maker: pick the best
    action separately in every state. -/
def valuePerfect (D : DecisionProblem) : Int :=
  sumFin D.nS (fun s => maxFin D.nA (fun a => wu D s a))

/-- Le signal totalement non informatif (une seule réalisation) vaut
    exactement la valeur sans information.
    English: The totally uninformative signal (a single realization) is worth
    exactly the no-information value. -/
theorem valueSignal_const (D : DecisionProblem) :
    valueSignal D (fun _ => (0 : Fin 1)) = valueNoInfo D := by
  unfold valueSignal valueNoInfo
  simp

/-- Décomposition en fibres : sommer `f` sur les états classés par
    English: Fiber decomposition: summing `f` over the states classified by the
    composite map `h ∘ τ` into cell `k` equals summing, over the
    realizations `j` of `τ` that `h` sends to `k`, the `τ`-cell sums. -/
theorem sumFin_fiber {n m p : Nat} (τ : Fin n → Fin p) (h : Fin p → Fin m)
    (k : Fin m) (f : Fin n → Int) :
    sumFin n (fun s => if h (τ s) = k then f s else 0) =
    sumFin p (fun j => if h j = k then
      sumFin n (fun s => if τ s = j then f s else 0) else 0) := by
  have push : ∀ j : Fin p,
      (if h j = k then sumFin n (fun s => if τ s = j then f s else 0) else 0) =
      sumFin n (fun s => if h j = k then (if τ s = j then f s else 0) else 0) :=
    fun j => (sumFin_if_distrib _ _).symm
  rw [sumFin_congr push, sumFin_comm]
  apply sumFin_congr
  intro s
  have swap : ∀ j : Fin p,
      (if h j = k then (if τ s = j then f s else 0) else 0) =
      (if τ s = j then (if h j = k then f s else 0) else 0) := by
    intro j
    by_cases h1 : h j = k <;> by_cases h2 : τ s = j <;> simp [h1, h2]
  rw [sumFin_congr swap, sumFin_single (τ s) (fun j => if h j = k then f s else 0)]

/-- **Monotonie de Blackwell (cas déterministe).** Si le signal `σ` est
    English: **Blackwell monotonicity (deterministic case).** If the signal `σ`
    is a coarsening of `τ` — every realization of `σ` is computed from
    the realization of `τ` via `h` — then observing the finer signal
    `τ` is worth at least as much as observing `σ`. -/
theorem valueSignal_mono (D : DecisionProblem) {m p : Nat}
    (σ : Signal D m) (τ : Signal D p) (h : Fin (p + 1) → Fin (m + 1))
    (hfactor : ∀ s, σ s = h (τ s)) :
    valueSignal D σ ≤ valueSignal D τ := by
  unfold valueSignal
  -- Rewrite each σ-cell sum as a sum over the τ-cells it contains.
  have hcell : ∀ (k : Fin (m + 1)) (a : Fin (D.nA + 1)),
      sumFin D.nS (fun s => if σ s = k then wu D s a else 0) =
      sumFin (p + 1) (fun j => if h j = k then
        sumFin D.nS (fun s => if τ s = j then wu D s a else 0) else 0) := by
    intro k a
    rw [sumFin_congr (fun s => by rw [hfactor s]),
        sumFin_fiber τ h k (fun s => wu D s a)]
  -- Bound the max over each σ-cell by the sum of maxima over its τ-cells.
  have hk : ∀ k : Fin (m + 1),
      maxFin D.nA (fun a =>
        sumFin D.nS (fun s => if σ s = k then wu D s a else 0)) ≤
      sumFin (p + 1) (fun j => if h j = k then
        maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if τ s = j then wu D s a else 0)) else 0) := by
    intro k
    have step1 := maxFin_sumFin_le (fun j a => if h j = k then
      sumFin D.nS (fun s => if τ s = j then wu D s a else 0) else 0)
    have step2 : ∀ j : Fin (p + 1),
        maxFin D.nA (fun a => if h j = k then
          sumFin D.nS (fun s => if τ s = j then wu D s a else 0) else 0) =
        (if h j = k then maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if τ s = j then wu D s a else 0)) else 0) :=
      fun j => maxFin_if_distrib _ _
    calc maxFin D.nA (fun a =>
            sumFin D.nS (fun s => if σ s = k then wu D s a else 0))
        = maxFin D.nA (fun a =>
            sumFin (p + 1) (fun j => if h j = k then
              sumFin D.nS (fun s => if τ s = j then wu D s a else 0) else 0)) := by
          exact congrArg (maxFin D.nA) (funext (fun a => hcell k a))
      _ ≤ sumFin (p + 1) (fun j =>
            maxFin D.nA (fun a => if h j = k then
              sumFin D.nS (fun s => if τ s = j then wu D s a else 0) else 0)) := step1
      _ = sumFin (p + 1) (fun j => if h j = k then
            maxFin D.nA (fun a =>
              sumFin D.nS (fun s => if τ s = j then wu D s a else 0)) else 0) :=
          sumFin_congr step2
  -- Sum the per-cell bounds, then undo the double counting over k.
  calc sumFin (m + 1) (fun k => maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if σ s = k then wu D s a else 0)))
      ≤ sumFin (m + 1) (fun k => sumFin (p + 1) (fun j => if h j = k then
          maxFin D.nA (fun a =>
            sumFin D.nS (fun s => if τ s = j then wu D s a else 0)) else 0)) :=
        sumFin_mono hk
    _ = sumFin (p + 1) (fun j => maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if τ s = j then wu D s a else 0))) :=
        (sumFin_partition h (fun j => maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if τ s = j then wu D s a else 0)))).symm

/-- **L'information ne nuit jamais à un décideur seul** : tout signal vaut
    English: **Information never hurts a single decision maker**: any signal is
    worth at least the no-information value (every signal refines the
    trivial one). -/
theorem valueNoInfo_le_valueSignal (D : DecisionProblem) {m : Nat}
    (σ : Signal D m) :
    valueNoInfo D ≤ valueSignal D σ := by
  rw [← valueSignal_const D]
  exact valueSignal_mono D (fun _ => (0 : Fin 1)) σ (fun _ => 0) (fun _ => rfl)

/-- L'information parfaite domine tout signal : connaître l'état exactement
    English: Perfect information dominates any signal: knowing the state exactly
    is the finest deterministic signal. -/
theorem valueSignal_le_valuePerfect (D : DecisionProblem) {m : Nat}
    (σ : Signal D m) :
    valueSignal D σ ≤ valuePerfect D := by
  unfold valueSignal valuePerfect
  have hk : ∀ k : Fin (m + 1),
      maxFin D.nA (fun a =>
        sumFin D.nS (fun s => if σ s = k then wu D s a else 0)) ≤
      sumFin D.nS (fun s => if σ s = k then
        maxFin D.nA (fun a => wu D s a) else 0) := by
    intro k
    have step1 := maxFin_sumFin_le (fun s a => if σ s = k then wu D s a else 0)
    have step2 : ∀ s : Fin D.nS,
        maxFin D.nA (fun a => if σ s = k then wu D s a else 0) =
        (if σ s = k then maxFin D.nA (fun a => wu D s a) else 0) :=
      fun s => maxFin_if_distrib _ _
    exact Int.le_trans step1 (Int.le_of_eq (sumFin_congr step2))
  calc sumFin (m + 1) (fun k => maxFin D.nA (fun a =>
          sumFin D.nS (fun s => if σ s = k then wu D s a else 0)))
      ≤ sumFin (m + 1) (fun k => sumFin D.nS (fun s => if σ s = k then
          maxFin D.nA (fun a => wu D s a) else 0)) := sumFin_mono hk
    _ = sumFin D.nS (fun s => maxFin D.nA (fun a => wu D s a)) :=
        (sumFin_partition σ (fun s => maxFin D.nA (fun a => wu D s a))).symm

/-- Pas d'information est au plus l'information parfaite (composition des
    English: No information is at most perfect information (composition of the
    two comparisons, stated directly for convenience). -/
theorem valueNoInfo_le_valuePerfect (D : DecisionProblem) :
    valueNoInfo D ≤ valuePerfect D :=
  Int.le_trans (valueNoInfo_le_valueSignal D (fun _ => (0 : Fin 1)))
    (valueSignal_le_valuePerfect D _)

/-
  Concrete check: the umbrella problem. Two equally likely states
  (rain, sun), two actions (take the umbrella, leave it). Payoffs:
  umbrella = 2 in rain, 0 in sun; no umbrella = -3 in rain, 3 in sun.
-/

/-- Problème de décision pluie-ou-soleil utilisé comme exemple vérifié au noyau.
    English: Rain-or-sun decision problem used as a kernel-checked example. -/
def umbrella : DecisionProblem where
  nS := 2
  nA := 1
  w := fun _ => 1
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 2 else -3)
    else (if a.val = 0 then 0 else 3)

/-- Non informé, le meilleur plan (toujours prendre le parapluie) vaut 2.
    English: Uninformed, the best plan (always take the umbrella) is worth 2. -/
theorem umbrella_valueNoInfo : valueNoInfo umbrella = 2 := by decide

/-- Pleinement informé (parapluie ssi pluie), le plan vaut 5.
    English: Perfectly informed (umbrella iff rain), the plan is worth 5. -/
theorem umbrella_valuePerfect : valuePerfect umbrella = 5 := by decide

/-- La valeur de l'information parfaite est strictement positive ici.
    English: The value of perfect information is strictly positive here. -/
theorem umbrella_strict_gain : valueNoInfo umbrella < valuePerfect umbrella := by
  decide
