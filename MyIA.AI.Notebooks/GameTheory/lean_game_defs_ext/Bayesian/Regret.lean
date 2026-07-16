/-
  Regret externe pour une suite finie de jeu (Lean 4 core seul, sans Mathlib)
  ===========================================================================

  Objet central de la *minimisation de regret* (apprentissage en ligne, base
  de CFR — Counterfactual Regret Minimization), listé comme cible GT-Lean-ext
  (GT-13, information imparfaite) dans la table des lacunes de #2610.

  Sur une suite finie de `T` rounds à `nA + 1` actions, chaque round révèle un
  vecteur de paiements `payoff t : Fin (nA + 1) → Int` et le joueur réalise une
  action `played t`. Le **regret externe** est l'écart entre le paiement de la
  meilleure action fixe *en rétrospective* et le paiement effectivement obtenu.
  Il quantifie « de combien une unique action fixe, choisie a posteriori, aurait
  fait mieux ». Réutilise l'infrastructure `sumFin` (`Sum.lean`) et `maxFin`
  (`Max.lean`) ; tout est décidable, donc les instances concrètes sont
  certifiées par `decide` (vérification noyau).

  Voir #2610 (formalisation GT-Lean, cible GT-13 : minimisation de regret).

  ---
  English:
  External regret for a finite play sequence (core Lean 4 only, no Mathlib)
  ========================================================================

  Central object of *regret minimization* (online learning, the foundation of
  CFR — Counterfactual Regret Minimization), listed as a GT-Lean-ext target
  (GT-13, imperfect information) in the gap table of #2610.

  Over a finite sequence of `T` rounds with `nA + 1` actions, each round reveals
  a payoff vector `payoff t : Fin (nA + 1) → Int` and the player realizes an
  action `played t`. The **external regret** is the gap between the payoff of
  the best fixed action *in hindsight* and the payoff actually obtained. It
  measures "how much better a single fixed action, chosen after the fact, would
  have done". Reuses the `sumFin` (`Sum.lean`) and `maxFin` (`Max.lean`)
  infrastructure; everything is decidable, so concrete instances are certified
  by `decide` (kernel checking).

  See #2610 (GT-Lean formalization, GT-13 target: regret minimization).
-/

import Bayesian.Sum
import Bayesian.Max

/-- Paiement total réellement obtenu : somme sur les rounds du paiement de
    l'action effectivement jouée à chaque round.
    English: Total payoff actually obtained: sum over rounds of the payoff of
    the action actually played each round. -/
def realizedTotal (T nA : Nat) (payoff : Fin T → Fin (nA + 1) → Int)
    (played : Fin T → Fin (nA + 1)) : Int :=
  sumFin T (fun t => payoff t (played t))

/-- Paiement total d'une action fixe `a` jouée à tous les rounds (candidat au
    meilleur choix en rétrospective).
    English: Total payoff of a single fixed action `a` played at every round
    (a candidate for the best-in-hindsight choice). -/
def fixedTotal (T nA : Nat) (payoff : Fin T → Fin (nA + 1) → Int)
    (a : Fin (nA + 1)) : Int :=
  sumFin T (fun t => payoff t a)

/-- Meilleure action fixe en rétrospective : maximum sur les actions du
    paiement fixe total.
    English: Best fixed action in hindsight: maximum over actions of the total
    fixed payoff. -/
def bestFixedTotal (T nA : Nat) (payoff : Fin T → Fin (nA + 1) → Int) : Int :=
  maxFin nA (fun a => fixedTotal T nA payoff a)

/-- Regret externe : écart entre la meilleure action fixe en rétrospective et
    le paiement réellement obtenu.
    English: External regret: gap between the best fixed action in hindsight and
    the payoff actually obtained. -/
def externalRegret (T nA : Nat) (payoff : Fin T → Fin (nA + 1) → Int)
    (played : Fin T → Fin (nA + 1)) : Int :=
  bestFixedTotal T nA payoff - realizedTotal T nA payoff played

/-- Lemme auxiliaire : soustraire une constante commute avec le maximum fini
    (`max (f · − c) = max f − c`), miroir de `sumFin_mul_left`.
    English: Auxiliary lemma: subtracting a constant commutes with the finite
    maximum (`max (f · − c) = max f − c`), mirror of `sumFin_mul_left`. -/
theorem maxFin_sub_const : ∀ {n : Nat} (f : Fin (n + 1) → Int) (c : Int),
    maxFin n (fun a => f a - c) = maxFin n f - c
  | 0, _, _ => rfl
  | n + 1, f, c => by
    simp only [maxFin_succ]
    rw [maxFin_sub_const (fun i => f i.succ) c]
    omega

/-- Garantie définissante du regret externe : aucune action fixe ne bat le jeu
    réalisé de plus que le regret externe (borne point par point sur les
    actions).
    English: Defining guarantee of external regret: no fixed action beats the
    realized play by more than the external regret (pointwise bound over
    actions). -/
theorem fixed_gap_le_externalRegret (T nA : Nat)
    (payoff : Fin T → Fin (nA + 1) → Int) (played : Fin T → Fin (nA + 1))
    (a : Fin (nA + 1)) :
    fixedTotal T nA payoff a - realizedTotal T nA payoff played
      ≤ externalRegret T nA payoff played := by
  have h : fixedTotal T nA payoff a ≤ bestFixedTotal T nA payoff :=
    le_maxFin (fun a => fixedTotal T nA payoff a) a
  show fixedTotal T nA payoff a - realizedTotal T nA payoff played
      ≤ bestFixedTotal T nA payoff - realizedTotal T nA payoff played
  omega

/-- Caractérisation : le regret externe est le maximum sur les actions de
    l'écart (paiement de l'action fixe − paiement réalisé).
    English: Characterization: external regret is the maximum over actions of
    the gap (fixed-action payoff − realized payoff). -/
theorem externalRegret_eq_maxFin_gap (T nA : Nat)
    (payoff : Fin T → Fin (nA + 1) → Int) (played : Fin T → Fin (nA + 1)) :
    externalRegret T nA payoff played
      = maxFin nA (fun a =>
          fixedTotal T nA payoff a - realizedTotal T nA payoff played) := by
  unfold externalRegret bestFixedTotal
  rw [maxFin_sub_const (fun a => fixedTotal T nA payoff a)
        (realizedTotal T nA payoff played)]

/-- Jouer constamment une même action donne un regret externe positif ou nul :
    le paiement réalisé est alors le paiement fixe de cette action, borné par le
    meilleur.
    English: Playing one and the same action throughout yields nonnegative
    external regret: the realized payoff is then that action's fixed payoff,
    bounded by the best. -/
theorem externalRegret_const_nonneg (T nA : Nat)
    (payoff : Fin T → Fin (nA + 1) → Int) (a : Fin (nA + 1)) :
    0 ≤ externalRegret T nA payoff (fun _ => a) := by
  have h : fixedTotal T nA payoff a ≤ bestFixedTotal T nA payoff :=
    le_maxFin (fun a => fixedTotal T nA payoff a) a
  have hreal : realizedTotal T nA payoff (fun _ => a) = fixedTotal T nA payoff a :=
    rfl
  show 0 ≤ bestFixedTotal T nA payoff - realizedTotal T nA payoff (fun _ => a)
  omega

/-!
  ## Instance concrète — 2 actions, 3 rounds (experts)

  Vecteurs de paiement : round 0 favorise l'action 0, round 1 l'action 1,
  round 2 l'action 0. La meilleure action fixe est l'action 0 (total 2 contre 1).

  English: Concrete instance — 2 actions, 3 rounds (experts). Payoff vectors:
  round 0 favors action 0, round 1 favors action 1, round 2 favors action 0.
  The best fixed action is action 0 (total 2 vs 1).
-/

/-- Paiements experts concrets (`Fin 3` rounds, `Fin 2` actions).
    English: Concrete experts payoffs (`Fin 3` rounds, `Fin 2` actions). -/
def payoffEx (t : Fin 3) (a : Fin 2) : Int :=
  match t.val, a.val with
  | 0, 0 => 1
  | 0, _ => 0
  | 1, 0 => 0
  | 1, _ => 1
  | _, 0 => 1
  | _, _ => 0

/-- Jeu optimal en rétrospective : toujours l'action 0.
    English: Hindsight-optimal play: always action 0. -/
def playedOpt : Fin 3 → Fin 2 := fun _ => 0

/-- Jeu sous-optimal : toujours l'action 1.
    English: Suboptimal play: always action 1. -/
def playedBad : Fin 3 → Fin 2 := fun _ => 1

/-- Jouer la meilleure action fixe donne un regret externe nul (certifié noyau).
    English: Playing the best fixed action yields zero external regret
    (kernel-certified). -/
theorem externalRegret_playedOpt : externalRegret 3 1 payoffEx playedOpt = 0 := by
  decide

/-- Un jeu sous-optimal a un regret externe strictement positif (certifié noyau).
    English: A suboptimal play has strictly positive external regret
    (kernel-certified). -/
theorem externalRegret_playedBad : externalRegret 3 1 payoffEx playedBad = 1 := by
  decide
