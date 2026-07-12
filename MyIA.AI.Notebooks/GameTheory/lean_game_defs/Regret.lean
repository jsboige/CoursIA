/-
  Minimisation du regret et définitions du CFR en Lean 4
  =====================================================

  Définit les structures pour l'apprentissage basé sur le regret dans les jeux :
  - Regret : écart entre le paiement obtenu et le meilleur paiement possible
  - RegretMatching : règle de mise à jour de stratégie à partir des regrets cumulés
  - CFR (Counterfactual Regret Minimization) : algorithme clé pour
    résoudre les jeux à information imparfaite

  Basé sur GameTheory-13-ImperfectInfo-CFR.ipynb

  Note : ce sont des définitions pédagogiques. Une formalisation complète
  nécessiterait la théorie de la mesure et des preuves de convergence
  (non abordées ici).

  ---
  English:
  Regret Minimization and CFR Definitions in Lean 4
  ==================================================

  Defines structures for regret-based learning in games:
  - Regret: Difference between achieved and best possible payoff
  - RegretMatching: Strategy update rule from cumulative regrets
  - CFR (Counterfactual Regret Minimization): Key algorithm for
    solving imperfect-information games

  Based on GameTheory-13-ImperfectInfo-CFR.ipynb

  Note: These are pedagogical definitions. A full formalization would
  require measure theory and convergence proofs (not attempted here).
-/

import Basic
import Bayesian

/-!
## Notions de regret

---
English:
## Regret Concepts
-/

/-- Regret instantané pour une action : de combien cette action
    aurait été meilleure que ce qui a réellement été joué.

    regret(a) = u(a) - u(a_played)

    English: Instantaneous regret for an action: how much better that action
    would have been compared to what was actually played.

    regret(a) = u(a) - u(a_played)
-/
def instantRegret (payoff : Fin n → Float) (played : Fin n) (action : Fin n) : Float :=
  payoff action - payoff played

/-- Regret cumulé pour chaque action sur T itérations.
    Stocké sous forme d'application de l'indice d'action vers le regret accumulé.
    English: Cumulative regret for each action over T iterations.
    Stored as a map from action index to accumulated regret. -/
def CumulativeRegret (n : Nat) := Fin n → Float

/-- Initialise un regret nul.
    English: Initialize zero regret -/
def zeroRegret (n : Nat) : CumulativeRegret n := fun _ => 0

/-- Met à jour le regret cumulé avec une nouvelle observation.
    English: Update cumulative regret with a new observation -/
def updateRegret {n : Nat} (regret : CumulativeRegret n)
    (payoff : Fin n → Float) (played : Fin n) : CumulativeRegret n :=
  fun a => regret a + instantRegret payoff played a

/-!
## Regret matching

---
English:
## Regret Matching
-/

/-- Regret matching : convertit les regrets cumulés positifs en une stratégie.

    Pour chaque action a : σ(a) = R+(a) / Σ_a' R+(a')
    où R+ est la partie positive du regret cumulé.

    Si tous les regrets sont non positifs, jouer uniformément.

    English: Regret matching: convert positive cumulative regrets to a strategy.

    For each action a: σ(a) = R+(a) / Σ_a' R+(a')
    where R+ is the positive part of cumulative regret.

    If all regrets are non-positive, play uniformly.
-/
def regretMatchingStrategy {n : Nat} (regret : CumulativeRegret n) : Fin n → Float :=
  let posRegret (a : Fin n) : Float := max 0 (regret a)
  let total := (List.finRange n).foldl (fun acc a => acc + posRegret a) 0
  if total > 0 then
    fun a => posRegret a / total
  else
    fun _ => (1.0 : Float) / n.toFloat  -- uniforme

/-!
## Regret externe (cohérence de Hannan)

---
English:
## External Regret (Hannan Consistency)
-/

/-- Regret externe : écart entre le paiement réalisé et la meilleure
    action fixe avec le recul.

    R_T = max_a Σ_t u_t(a) - Σ_t u_t(a_t)

    English: External regret: difference between realized payoff and best
    fixed action in hindsight.

    R_T = max_a Σ_t u_t(a) - Σ_t u_t(a_t)
-/
def externalRegret (T : Nat) (payoffs : Fin T → (Fin n → Float))
    (played : Fin T → Fin n) : Float :=
  let bestFixed := (List.finRange n).foldl
    (fun acc a => max acc ((List.finRange T).foldl
      (fun s t => s + payoffs t a) 0))
    0
  let realized := (List.finRange T).foldl
    (fun s t => s + payoffs t (played t)) 0
  bestFixed - realized

/-!
## Regret contrefactuel

---
English:
## Counterfactual Regret
-/

/-- Regret contrefactuel pour un joueur à un ensemble d'information.

    L'idée clé du CFR : minimiser le regret contrefactuel à chaque
    ensemble d'information indépendamment, et la stratégie moyenne converge
    vers un équilibre de Nash dans les jeux à somme nulle à deux joueurs.

    CFR(I, a) = Σ_z∈Z_I  π_{-i}(z) · (u_i(z, a) - u_i(z, σ(I)))

    où π_{-i} est la probabilité d'atteindre z en excluant le joueur i.

    English: Counterfactual regret for a player at an information set.

    The key insight of CFR: minimize counterfactual regret at each
    information set independently, and the average strategy converges
    to a Nash equilibrium in two-player zero-sum games.

    CFR(I, a) = Σ_z∈Z_I  π_{-i}(z) · (u_i(z, a) - u_i(z, σ(I)))

    where π_{-i} is the reach probability excluding player i.
-/
structure CounterfactualRegret where
  /-- L'identifiant de l'ensemble d'information.
      English: The information set identifier -/
  infoSet : String
  /-- Le joueur.
      English: The player -/
  player : Nat
  /-- Regret pour chaque action disponible.
      English: Regret for each available action -/
  actionRegrets : List (String × Float)  -- (nom_action, valeur_regret)
  deriving Repr

/-!
## État du solveur CFR

---
English:
## CFR Solver State
-/

/-- L'état maintenu par un solveur CFR au fil des itérations.
    English: The state maintained by a CFR solver across iterations -/
structure CFRState where
  /-- Regret contrefactuel cumulé par ensemble d'information et action.
      English: Cumulative counterfactual regret per information set and action -/
  cumulativeRegret : List (String × List (String × Float))
  /-- Stratégie cumulée (somme des stratégies pondérées par la probabilité d'atteinte).
      English: Cumulative strategy (sum of strategies weighted by reach) -/
  strategySum : List (String × List (String × Float))
  /-- Nombre d'itérations effectuées.
      English: Number of iterations completed -/
  iterations : Nat
  deriving Repr

/-- Initialise un état CFR vide.
    English: Initialize empty CFR state -/
def initCFRState : CFRState where
  cumulativeRegret := []
  strategySum := []
  iterations := 0

/-!
## Notions de convergence

---
English:
## Convergence Concepts
-/

/-- Le regret moyen tend vers zéro (ε-équilibre de Nash).
    English: Average regret approaches zero (ε-Nash equilibrium) -/
def epsilonNash (ε : Float) (externalReg : Float) : Prop :=
  externalReg <= ε

/-- Apprentissage sans regret : le regret externe moyen tend vers zéro.
    Les paiements et les coups sont indexés par `Nat` (horizon infini) ; le regret
    à l'horizon `t` est calculé sur le préfixe des `t` premières rondes.
    English: No-regret learning: average external regret goes to zero.
    Payoffs and plays are indexed by `Nat` (infinite horizon); the regret
    at horizon `t` is computed on the prefix of the first `t` rounds. -/
def noRegret (payoffs : Nat → (Fin n → Float))
    (played : Nat → Fin n) : Prop :=
  ∀ ε > 0, ∃ T0, ∀ t ≥ T0,
    externalRegret t (fun s => payoffs s.val) (fun s => played s.val) / t.toFloat < ε

/-!
## Fictitious play (tiré de GT-17 Section 3)

---
English:
## Fictitious Play (from GT-17 Section 3)
-/

/-- Fictitious play : chaque joueur joue la meilleure réponse face à la
    distribution empirique des coups passés de l'adversaire.

    Brown (1951) : converge vers l'équilibre de Nash pour :
    - les jeux à somme nulle à 2 joueurs
    - les jeux 2x2
    - les jeux à intérêts identiques

    English: Fictitious play: each player plays best response to the
    empirical distribution of opponent's past plays.

    Brown (1951): converges to Nash equilibrium in:
    - 2-player zero-sum games
    - 2x2 games
    - Games with identical interests
-/
structure FictitiousPlayState (n : Nat) where
  /-- Fréquence empirique des actions de chaque joueur.
      English: Empirical frequency of each player's actions -/
  actionCounts : Fin n → (Fin m → Nat)
  /-- Nombre de rondes jouées.
      English: Number of rounds played -/
  rounds : Nat
  -- pas de `deriving Repr` : `actionCounts` est un type fonctionnel, non dérivable

/-- Meilleure réponse face à la distribution empirique de l'adversaire.

    Conceptuellement : argmax_a Σ_{a_{-i}} empiricalDist(a_{-i}) · u_i(a, a_{-i}).
    Dans une formalisation complète, cela utiliserait l'argmax de Mathlib.

    English: Best response to empirical distribution of opponent.

    Conceptually: argmax_a Σ_{a_{-i}} empiricalDist(a_{-i}) · u_i(a, a_{-i}).
    In a full formalization this would use Mathlib's argmax.
-/
def isBestResponseToEmpirical {m : Nat}
    (payoff : Fin 2 → (Fin 2 → Fin m) → Float)
    (empiricalDist : Fin 2 → (Fin m → Float))
    (player : Fin 2) (action : Fin m) : Prop :=
  ∀ other : Fin m,
    let expected := fun a =>
      (List.finRange m).foldl
        (fun acc a' => acc + empiricalDist (if player.val = 0 then 1 else 0) a' *
                       payoff player (fun j => if j = player then a else a'))
        0
    expected action >= expected other
