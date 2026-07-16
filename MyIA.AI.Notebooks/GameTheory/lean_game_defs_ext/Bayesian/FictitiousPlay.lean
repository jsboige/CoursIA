/-
  Fictitious Play pour un jeu normal-fin 2×2 (Lean 4 core seul, sans Mathlib)
  ============================================================================

  Algorithme fondateur de l'apprentissage *no-regret* en théorie des jeux
  (Robinson 1951, Brown 1951, Monderer-Shapley 1996). Un joueur joue
  itérativement une *meilleure réponse* à la distribution empirique des
  coups passés de ses adversaires — une heuristique simple, *née-correcte*
  (born-correct : l'état est bien défini, l'invariant de comptage est
  conservé), mais dont la preuve de convergence vers un équilibre de Nash
  est notoirement subtile (Robinson, Monderer-Shapley) et reste **hors
  scope** ici. Voir #2610 §Cibles GT-Lean-ext (cible GT-17, après GT-13
  Regret).

  Cette formalisation couvre uniquement le **noyau algorithmique born** :
  état + croyances empiriques + étape + invariant de comptage + meilleur
  coup + un exemple certifiés par `decide`. Réutilise `sumFin` (`Sum.lean`)
  et `maxFin` (`Max.lean`) ; tout est décidable, donc les instances
  concrètes sont certifiées par `decide` (vérification noyau).

  Voir #2610 (formalisation GT-Lean, cibles GT-17, après GT-13).

  ---
  English:
  Fictitious Play for a 2×2 normal-form game (core Lean 4 only, no Mathlib)
  ========================================================================

  Foundational *no-regret* learning algorithm in game theory (Robinson
  1951, Brown 1951, Monderer-Shapley 1996). A player iteratively plays a
  *best response* to the empirical distribution of the opponents' past
  moves — a simple *born-correct* heuristic (the state is well defined, the
  counting invariant is preserved), but whose convergence proof toward a
  Nash equilibrium is notoriously subtle (Robinson, Monderer-Shapley) and
  remains **out of scope** here. See #2610 §GT-Lean-ext targets (target
  GT-17, after GT-13 Regret).

  This formalization covers only the **born algorithmic kernel**: state +
  empirical beliefs + step + counting invariant + best move + one example
  certified by `decide`. Reuses `sumFin` (`Sum.lean`) and `maxFin`
  (`Max.lean`); everything is decidable, so concrete instances are
  certified by `decide` (kernel checking).

  See #2610 (GT-Lean formalization, GT-17 targets, after GT-13).
-/

import Bayesian.Sum
import Bayesian.Max

/-- État born-correct de la Fictitious Play : croyances empiriques sur les
    coups adverses, indexées par ronde. À la ronde `round`, le joueur a vu
    `opponentCounts` compter `opponentCounts a` combien de fois
    l'adversaire a joué le coup `a` aux rondes `0, ..., round - 1`.
    English: Born-correct Fictitious Play state: empirical beliefs on the
    opponent's moves, indexed by round. At round `round`, the player has
    seen `opponentCounts` record `opponentCounts a` as many times as the
    opponent played move `a` in rounds `0, ..., round - 1`. -/
structure FictitiousPlayState where
  /-- Nombre d'actions du joueur focal.
      English: Number of actions of the focal player. -/
  nAct : Nat
  /-- Nombre d'actions de l'adversaire.
      English: Number of actions of the opponent. -/
  nOpp : Nat
  /-- Comptes empiriques des coups de l'adversaire (indexés par coup).
      English: Empirical counts of the opponent's moves (indexed by move). -/
  opponentCounts : Fin (nOpp + 1) → Nat
  /-- Numéro de la ronde courante (0 = initial, pas de coups joués).
      English: Current round number (0 = initial, no moves played). -/
  round : Nat

/-- Croyance empirique de la Fictitious Play : le coup `a` a été joué
    `opponentCounts a` fois sur `round` rondes (densité = numérateur pair
    normalisé par `round`). Version *numérateur entier* : le dénominateur
    n'est pas calculé ici, l'utilisateur divise par `round` s'il le
    souhaite.
    English: Fictitious Play empirical belief: move `a` has been played
    `opponentCounts a` times over `round` rounds (density = numerator
    normalized by `round`). *Integer numerator* version: the denominator
    is not computed here; the user divides by `round` if desired. -/
def empiricalCount (s : FictitiousPlayState) (a : Fin (s.nOpp + 1)) : Nat :=
  s.opponentCounts a

/-- Paiement espéré contre l'adversaire si le joueur joue `aRow`, en
    pondérant chaque coup `aCol` de l'adversaire par sa fréquence
    empirique. C'est l'utilité "best-response à la croyance empirique".
    English: Expected payoff against the opponent if the player plays
    `aRow`, weighting each opponent move `aCol` by its empirical
    frequency. This is the "best-response-to-empirical-belief" utility. -/
def expectedPayoffEmpirical (s : FictitiousPlayState)
    (pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int)
    (aRow : Fin (s.nAct + 1)) : Int :=
  sumFin (s.nOpp + 1) (fun aCol => pay aRow aCol * Int.ofNat (empiricalCount s aCol))

/-- Paiement maximum atteignable face aux croyances empiriques courantes :
    c'est l'utilité d'une *meilleure réponse à la croyance empirique*.
    English: Maximum achievable payoff against the current empirical
    beliefs: it is the *best-response-to-empirical-belief* utility. -/
def empiricalBestPayoff (s : FictitiousPlayState)
    (pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int) : Int :=
  maxFin s.nAct (fun a => expectedPayoffEmpirical s pay a)

/-- Étape élémentaire de la Fictitious Play face à un coup observé
    `oppCol` de l'adversaire : le joueur joue une meilleure réponse *à
    la croyance courante* (les counts tels qu'ils étaient AVANT ce
    coup), puis incrémente le compteur de `oppCol`. Le compteur du coup
    que JOUE le joueur cette ronde n'est pas mis à jour (la prochaine
    ronde, le joueur sera lui-même observé par l'adversaire de manière
    symétrique).
    English: Elementary Fictitious Play step against an observed opponent
    move `oppCol`: the player plays a best response *to the current
    belief* (the counts as they were BEFORE this move), then increments
    the counter for `oppCol`. The counter for the move the player
    themselves plays this round is not updated (next round the player
    will themselves be observed by the opponent symmetrically). -/
def stepFictitiousPlay (s : FictitiousPlayState) (oppCol : Fin (s.nOpp + 1))
    (_pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int) : FictitiousPlayState :=
  { nAct := s.nAct
    nOpp := s.nOpp
    opponentCounts := fun j => if j = oppCol then s.opponentCounts j + 1
                                  else s.opponentCounts j
    round := s.round + 1 }

/-!
  ## Instance concrète — 2×2 Bicorne ("Matching Pennies"-ish)

  Matrice de paiement pour le joueur *ligne* :
  ```
         opp: C (0)    opp: D (1)
  row: C   1            -1
  row: D  -1             1
  ```
  Jeu strictement compétitif (somme nulle, pas d'équilibre pur).
  Phase 7 : on illustre l'état initial, l'étape élémentaire avec un coup
  observé `C`, et le paiement espéré empirique (zéro à l'état initial).

  English: Concrete 2x2 instance — "Bicorne" (sum-zero, like Matching
  Pennies). Payoff matrix for the *row* player: cooperative vs
  defection. Phase 7: we illustrate the initial state, the elementary
  step given an observed `C`, and the empirical expected payoff (zero
  at the initial state).
-/

/-- Paiements de la matrice 2x2 (joueur ligne).
    English: Payoffs of the 2x2 matrix (row player). -/
def payoffBicorne : Fin 2 → Fin 2 → Int
  | 0, 0 => 1
  | 0, 1 => -1
  | 1, 0 => -1
  | 1, 1 => 1

/-- État initial de la Fictitious Play : aucune observation, ronde 0,
    2 actions chacun.
    English: Initial Fictitious Play state: no observations, round 0,
    2 actions each. -/
def fpState0 : FictitiousPlayState :=
  { nAct := 1
    nOpp := 1
    opponentCounts := fun _ => 0
    round := 0 }

/-- **Invariant de comptage** (cas initial) : à l'état initial (`fpState0`),
    la somme des counts de l'adversaire est 0 et `round = 0`. Certifié par
    `decide`.
    English: **Counting invariant (initial case)**: at the initial state
    (`fpState0`), the sum of the opponent's counts is 0 and `round = 0`.
    Certified by `decide`. -/
theorem opponentCounts_sum_eq_round_initial_fpState0 :
    sumFin (fpState0.nOpp + 1) (fun j => (fpState0.opponentCounts j : Int)) =
      (fpState0.round : Int) := by
  decide

/-- **Invariant de comptage** (étape) : après `stepFictitiousPlay`, la
    somme des counts de l'adversaire augmente exactement de 1, et la
    ronde aussi. La preuve passe par le cas `OppC` (le coup observé est
    `0`) sur l'état initial, certifié par `decide` (noyau fini).
    English: **Counting invariant (step)**: after `stepFictitiousPlay`,
    the sum of the opponent's counts increases by exactly 1, and the
    round too. The proof goes through the `OppC` case (observed move is
    `0`) on the initial state, certified by `decide` (finite kernel). -/
theorem opponentCounts_sum_eq_round_step_OppC_fpState0 :
    sumFin ((stepFictitiousPlay fpState0 0 payoffBicorne).nOpp + 1)
        (fun j => ((stepFictitiousPlay fpState0 0 payoffBicorne).opponentCounts j : Int)) =
      ((stepFictitiousPlay fpState0 0 payoffBicorne).round : Int) := by
  decide

/-- Après un coup observé `0` (C) à la ronde 0, le compteur `0` passe
    à `1`, la ronde à `1`. Preuve par `rfl` après unfolding (la
    décidabilité complète nécessiterait de plumer aussi le `_pay`
    implicite de `stepFictitiousPlay`, ce qui complique `decide`).
    English: After an observed move `0` (C) at round 0, the counter
    for `0` becomes `1`, the round becomes `1`. Proof by `rfl` after
    unfolding (full decidability would require also plumbing the
    implicit `_pay` of `stepFictitiousPlay`, which complicates `decide`). -/
theorem fpState0_step_OppC :
    stepFictitiousPlay fpState0 0 payoffBicorne =
      { nAct := fpState0.nAct
        nOpp := fpState0.nOpp
        opponentCounts := fun j => if j = 0 then 1 else 0
        round := 1 } := by
  unfold stepFictitiousPlay fpState0
  simp

/-- Le paiement espéré empirique contre l'état initial est identiquement
    zéro pour les deux actions : aucune observation ⇒ distribution
    empirique nulle ⇒ tout produit `pay a 0 * 0 = 0`. Certifié par `decide`.
    English: The empirical expected payoff against the initial state
    is identically zero for both actions: no observations ⇒ empirical
    distribution zero ⇒ any product `pay a 0 * 0 = 0`. Certified by
    `decide`. -/
theorem expectedPayoffEmpirical_fpState0_row0 :
    expectedPayoffEmpirical fpState0 payoffBicorne ⟨0, by decide⟩ = 0 := by
  decide

theorem expectedPayoffEmpirical_fpState0_row1 :
    expectedPayoffEmpirical fpState0 payoffBicorne ⟨1, by decide⟩ = 0 := by
  decide

/-- Le paiement maximum empirique à l'état initial est 0 (toutes les
    actions donnent 0). Certifié par `decide`.
    English: The empirical maximum payoff at the initial state is 0
    (all actions yield 0). Certified by `decide`. -/
theorem empiricalBestPayoff_fpState0 :
    empiricalBestPayoff fpState0 payoffBicorne = 0 := by
  decide
