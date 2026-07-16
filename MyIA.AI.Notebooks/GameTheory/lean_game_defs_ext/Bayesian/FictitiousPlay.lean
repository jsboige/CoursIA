/-
  Fictitious play — état, meilleure réponse empirique (Lean 4 core, sans Mathlib)
  ==============================================================================

  Le *fictitious play* (Brown 1951, Robinson 1951) est l'algorithme
  d'apprentissage no-regret le plus ancien : à chaque ronde, chaque joueur
  joue une meilleure réponse à la *distribution empirique* des actions passées
  de l'adversaire (la fréquence de chaque action observée jusqu'ici). Il est le
  successeur logique du regret externe de `Regret.lean` (phase 6, GT-13) vers la
  cible GT-17 (algorithmes de no-regret learning) de la table des lacunes #2610.

  Ce module formalise le noyau *born-correct* — c'est-à-dire les objets
  calculables et totaux dont la correction tient par construction, sans
  hypothèse de convergence :

  - `FictitiousPlayState` : la matrice des comptes de profils d'actions joués et
    le numéro de ronde ;
  - `empiricalDist` : la distribution empirique d'un vecteur de comptes, en poids
    `Int` non normalisés (comme le prior de `Types.lean`, l'argmax est invariant
    par remise à l'échelle donc la normalisation est superflue) ;
  - `bestResponseToEmpirical` : la meilleure réponse (argmax) à une distribution
    empirique adverse, avec sa garantie d'optimalité (`bestResponse_optimal`) ;
  - `stepFictitiousPlay` : la transition état → état d'une ronde de jeu simultané.

  La *preuve de convergence* (Robinson 1951, Monderer-Shapley 1996) est de
  niveau recherche et reste hors périmètre ; de même NFSP / PSRO / MARL. On livre
  ici l'appareil décidable, certifié au noyau par `decide` sur un Dilemme du
  Prisonnier 2×2.

  Voir #2610 (formalisation GT-Lean, cible GT-17 : no-regret learning /
  fictitious play, découpage born-correct — phase 7).

  ---
  English:
  Fictitious play — state and empirical best response (core Lean 4, no Mathlib)
  ============================================================================

  *Fictitious play* (Brown 1951, Robinson 1951) is the oldest no-regret
  learning algorithm: each round, every player plays a best response to the
  *empirical distribution* of the opponent's past actions (the observed
  frequency of each action so far). It is the logical successor of the external
  regret of `Regret.lean` (phase 6, GT-13) toward the GT-17 target (no-regret
  learning algorithms) of the #2610 gap table.

  This module formalizes the *born-correct* core — the computable, total objects
  whose correctness holds by construction, with no convergence assumption:

  - `FictitiousPlayState`: the matrix of played action-profile counts and the
    round number;
  - `empiricalDist`: the empirical distribution of a count vector, as
    unnormalized `Int` weights (like the prior of `Types.lean`; the argmax is
    invariant under rescaling, so normalization is superfluous);
  - `bestResponseToEmpirical`: the best response (argmax) to an opponent's
    empirical distribution, with its optimality guarantee
    (`bestResponse_optimal`);
  - `stepFictitiousPlay`: the state → state transition of one simultaneous-move
    round.

  The *convergence proof* (Robinson 1951, Monderer-Shapley 1996) is
  research-level and stays out of scope; likewise NFSP / PSRO / MARL. We deliver
  the decidable apparatus, kernel-certified by `decide` on a 2×2 Prisoner's
  Dilemma.

  See #2610 (GT-Lean formalization, GT-17 target: no-regret learning /
  fictitious play, born-correct slice — phase 7).
-/

import Bayesian.Sum
import Bayesian.Max

/-! ## Argmax fini — l'indice atteignant le maximum -/

/-- Indice atteignant le maximum de `f` sur `Fin (n + 1)` (domaine non vide,
    donc *born-correct* : renvoie toujours un indice, jamais d'échec). Miroir
    argmax de `maxFin` (`Max.lean`) : `maxFin` donne la valeur, `argmaxFin`
    donne le témoin. En cas d'égalité, le plus petit indice l'emporte.
    English: Index achieving the maximum of `f` over `Fin (n + 1)` (nonempty
    domain, hence *born-correct*: always returns an index, never fails). The
    argmax mirror of `maxFin` (`Max.lean`): `maxFin` gives the value,
    `argmaxFin` gives the witness. Ties break to the smaller index. -/
def argmaxFin : (n : Nat) → (Fin (n + 1) → Int) → Fin (n + 1)
  | 0, _ => 0
  | n + 1, f =>
    if f 0 ≥ f (argmaxFin n (fun i => f i.succ)).succ
    then 0
    else (argmaxFin n (fun i => f i.succ)).succ

/-- L'argmax atteint bien le maximum : `f (argmaxFin n f) = maxFin n f`.
    English: The argmax does achieve the maximum: `f (argmaxFin n f) = maxFin n f`. -/
theorem argmaxFin_spec : ∀ {n : Nat} (f : Fin (n + 1) → Int),
    f (argmaxFin n f) = maxFin n f
  | 0, _ => rfl
  | n + 1, f => by
    have ih : f (argmaxFin n (fun i => f i.succ)).succ
        = maxFin n (fun i => f i.succ) := argmaxFin_spec (fun i => f i.succ)
    simp only [argmaxFin, maxFin_succ]
    split <;> rename_i h <;> omega

/-- Garantie d'optimalité de l'argmax : aucune valeur ne dépasse celle de
    l'indice choisi (propriété de meilleure réponse).
    English: Optimality guarantee of the argmax: no value exceeds that of the
    chosen index (the best-response property). -/
theorem le_argmaxFin {n : Nat} (f : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    f i ≤ f (argmaxFin n f) := by
  rw [argmaxFin_spec f]
  exact le_maxFin f i

/-! ## État et dynamique du fictitious play -/

/-- État d'un fictitious play pour un jeu 2 joueurs à `n + 1` actions pour le
    joueur-ligne et `m + 1` pour le joueur-colonne. `count i j` est le nombre de
    fois que le profil d'actions `(i, j)` a été joué ; `round` est le numéro de
    ronde. Les distributions empiriques de chaque joueur s'obtiennent comme
    marginales de `count`.
    English: State of a fictitious play for a two-player game with `n + 1`
    actions for the row player and `m + 1` for the column player. `count i j` is
    how many times the action profile `(i, j)` has been played; `round` is the
    round number. Each player's empirical distribution is a marginal of `count`. -/
structure FictitiousPlayState (n m : Nat) where
  /-- Comptes des profils d'actions joués.
      English: Counts of played action profiles. -/
  count : Fin (n + 1) → Fin (m + 1) → Nat
  /-- Numéro de ronde.
      English: Round number. -/
  round : Nat

/-- État initial : aucun profil joué, ronde 0.
    English: Initial state: no profile played, round 0. -/
def FictitiousPlayState.empty (n m : Nat) : FictitiousPlayState n m :=
  { count := fun _ _ => 0, round := 0 }

/-- Distribution empirique (poids `Int` non normalisés) d'un vecteur de comptes
    sur `Fin (m + 1)`.
    English: Empirical distribution (unnormalized `Int` weights) of a count
    vector over `Fin (m + 1)`. -/
def empiricalDist {m : Nat} (counts : Fin (m + 1) → Nat) (j : Fin (m + 1)) : Int :=
  (counts j : Int)

/-- Croyance empirique du joueur-ligne sur les actions de la colonne : marginale
    de `count` sur les lignes (fréquence `Int` de chaque action `j`).
    English: Row player's empirical belief about the column's actions: marginal
    of `count` over rows (`Int` frequency of each action `j`). -/
def empiricalCol {n m : Nat} (s : FictitiousPlayState n m) (j : Fin (m + 1)) : Int :=
  sumFin (n + 1) (fun i => (s.count i j : Int))

/-- Croyance empirique du joueur-colonne sur les actions de la ligne : marginale
    de `count` sur les colonnes.
    English: Column player's empirical belief about the row's actions: marginal
    of `count` over columns. -/
def empiricalRow {n m : Nat} (s : FictitiousPlayState n m) (i : Fin (n + 1)) : Int :=
  sumFin (m + 1) (fun j => (s.count i j : Int))

/-- Paiement espéré de l'action `a` face à la distribution empirique adverse `d`
    (produit scalaire paiements × poids empiriques).
    English: Expected payoff of action `a` against the opponent's empirical
    distribution `d` (dot product of payoffs and empirical weights). -/
def expectedVsEmpirical {nA m : Nat} (payoff : Fin (nA + 1) → Fin (m + 1) → Int)
    (d : Fin (m + 1) → Int) (a : Fin (nA + 1)) : Int :=
  sumFin (m + 1) (fun j => payoff a j * d j)

/-- Meilleure réponse à une distribution empirique adverse : argmax du paiement
    espéré sur les actions propres.
    English: Best response to an opponent's empirical distribution: argmax of the
    expected payoff over one's own actions. -/
def bestResponseToEmpirical {nA m : Nat}
    (payoff : Fin (nA + 1) → Fin (m + 1) → Int) (d : Fin (m + 1) → Int) :
    Fin (nA + 1) :=
  argmaxFin nA (fun a => expectedVsEmpirical payoff d a)

/-- **Born-correct** : la meilleure réponse est optimale — aucune action ne fait
    mieux que `bestResponseToEmpirical` face à la même distribution empirique.
    English: **Born-correct**: the best response is optimal — no action does
    better than `bestResponseToEmpirical` against the same empirical
    distribution. -/
theorem bestResponse_optimal {nA m : Nat}
    (payoff : Fin (nA + 1) → Fin (m + 1) → Int) (d : Fin (m + 1) → Int)
    (a : Fin (nA + 1)) :
    expectedVsEmpirical payoff d a
      ≤ expectedVsEmpirical payoff d (bestResponseToEmpirical payoff d) :=
  le_argmaxFin (fun a => expectedVsEmpirical payoff d a) a

/-- Une ronde de fictitious play : les deux joueurs jouent simultanément une
    meilleure réponse à la distribution empirique courante de l'adversaire, et le
    profil résultant est ajouté aux comptes (ronde incrémentée).
    English: One round of fictitious play: both players simultaneously play a
    best response to the opponent's current empirical distribution, and the
    resulting profile is added to the counts (round incremented). -/
def stepFictitiousPlay {n m : Nat}
    (payoffRow : Fin (n + 1) → Fin (m + 1) → Int)
    (payoffCol : Fin (n + 1) → Fin (m + 1) → Int)
    (s : FictitiousPlayState n m) : FictitiousPlayState n m :=
  let iStar : Fin (n + 1) :=
    bestResponseToEmpirical payoffRow (empiricalCol s)
  let jStar : Fin (m + 1) :=
    bestResponseToEmpirical (fun j i => payoffCol i j) (empiricalRow s)
  { count := fun i j =>
      s.count i j + (if i = iStar ∧ j = jStar then 1 else 0),
    round := s.round + 1 }

/-- Chaque ronde incrémente le compteur de ronde de 1 (fait born-correct).
    English: Each round increments the round counter by 1 (born-correct fact). -/
@[simp] theorem stepFictitiousPlay_round {n m : Nat}
    (payoffRow payoffCol : Fin (n + 1) → Fin (m + 1) → Int)
    (s : FictitiousPlayState n m) :
    (stepFictitiousPlay payoffRow payoffCol s).round = s.round + 1 := rfl

/-! ## Instance concrète — Dilemme du Prisonnier 2×2 (certifié noyau)

  Paiements du joueur-ligne : `(C,C) = 3`, `(C,D) = 0`, `(D,C) = 5`, `(D,D) = 1`
  (action `0` = coopérer, action `1` = trahir). Face à une croyance empirique où
  la colonne a coopéré 3 fois et trahi 1 fois, le paiement espéré de la ligne est
  `9` pour `C` (`3·3 + 0·1`) contre `16` pour `D` (`5·3 + 1·1`) : la meilleure
  réponse est de trahir (action `1`), la trahison dominante attendue.

  English: Concrete instance — 2×2 Prisoner's Dilemma (kernel-certified). Row
  player's payoffs: `(C,C) = 3`, `(C,D) = 0`, `(D,C) = 5`, `(D,D) = 1` (action
  `0` = cooperate, action `1` = defect). Against an empirical belief where the
  column cooperated 3 times and defected once, the row's expected payoff is `9`
  for `C` (`3·3 + 0·1`) versus `16` for `D` (`5·3 + 1·1`): the best response is
  to defect (action `1`), the expected dominant defection.
-/

/-- Matrice de paiements du joueur-ligne d'un Dilemme du Prisonnier.
    English: Row player's payoff matrix of a Prisoner's Dilemma. -/
def pdRow (i j : Fin 2) : Int :=
  match i.val, j.val with
  | 0, 0 => 3
  | 0, _ => 0
  | 1, 0 => 5
  | _, _ => 1

/-- Croyance empirique concrète : la colonne a coopéré 3 fois, trahi 1 fois.
    English: Concrete empirical belief: the column cooperated 3 times, defected
    once. -/
def pdEmpiricalCol : Fin 2 → Int := fun j => match j.val with
  | 0 => 3
  | _ => 1

/-- La meilleure réponse au Dilemme du Prisonnier face à cette croyance est de
    trahir — action `1` (certifié noyau).
    English: The best response to the Prisoner's Dilemma against this belief is to
    defect — action `1` (kernel-certified). -/
theorem pd_bestResponse_defect :
    bestResponseToEmpirical pdRow pdEmpiricalCol = 1 := by decide

/-- Coopérer rapporte strictement moins que la meilleure réponse face à cette
    croyance : `9 < 16` (certifié noyau).
    English: Cooperating yields strictly less than the best response against this
    belief: `9 < 16` (kernel-certified). -/
theorem pd_cooperate_suboptimal :
    expectedVsEmpirical pdRow pdEmpiricalCol 0
      < expectedVsEmpirical pdRow pdEmpiricalCol (bestResponseToEmpirical pdRow pdEmpiricalCol) := by
  decide
