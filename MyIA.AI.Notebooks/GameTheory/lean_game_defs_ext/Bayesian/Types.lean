/-
  Espaces de types de Harsanyi — jeux bayésiens finis à deux joueurs
  =================================================================

  Formalise les jeux à information incomplète (Harsanyi 1967) pour le cas
  fini à deux joueurs, en Lean 4 core (sans Mathlib) :

  - `BayesGame2` : ensembles de types, ensembles d'actions, un prior commun
    non normalisé donné par des poids `Nat`, et des paiements dépendant du type
  - `Strategy1` / `Strategy2` : stratégies pures contingentes au type
  - `interimU1` / `interimU2` : utilité espérée interimaire (conditionnée par
    son propre type), comme une somme pondérée sur les types de l'adversaire
  - `exAnteU1` / `exAnteU2` : utilité espérée ex-ante

  Travailler avec des poids entiers plutôt qu'avec une mesure de probabilité
  normalisée garde toute quantité calculable et décidable ; `BNE.lean` prouve
  que les meilleures réponses sont invariantes par remise à l'échelle du prior,
  ce qui est exactement ce que signifie l'indépendance vis-à-vis de la
  normalisation.

  Basé sur GameTheory-11-BayesianGames.ipynb. Voir #2610 (phase 1 :
  jeux bayésiens — le rapport de recherche recommande les types finis d'abord).
-/

import Bayesian.Sum

/-- Un jeu bayésien fini à deux joueurs avec un prior non normalisé.

    Le joueur 1 a `nT1` types possibles et `nA1` actions ; le joueur 2 a
    `nT2` types et `nA2` actions. `w t1 t2` est le poids (non normalisé,
    `Nat`) du prior pour le profil de types `(t1, t2)`. Les paiements
    dépendent du profil de types complet et du profil d'actions. -/
structure BayesGame2 where
  /-- Nombre de types du joueur 1. -/
  nT1 : Nat
  /-- Nombre de types du joueur 2. -/
  nT2 : Nat
  /-- Nombre d'actions du joueur 1. -/
  nA1 : Nat
  /-- Nombre d'actions du joueur 2. -/
  nA2 : Nat
  /-- Prior commun sur les profils de types, comme poids non normalisés. -/
  w : Fin nT1 → Fin nT2 → Nat
  /-- Paiement du joueur 1. -/
  u1 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int
  /-- Paiement du joueur 2. -/
  u2 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int

/-- Une stratégie pure contingente au type du joueur 1 : son propre type → action. -/
def Strategy1 (g : BayesGame2) := Fin g.nT1 → Fin g.nA1

/-- Une stratégie pure contingente au type du joueur 2 : son propre type → action. -/
def Strategy2 (g : BayesGame2) := Fin g.nT2 → Fin g.nA2

/-- Utilité espérée interimaire du joueur 1 : de type `t1`, jouant l'action
    `a`, face à la stratégie `s2`, pondérée par la ligne du prior `w t1 ·`.

    (Avec des poids non normalisés, c'est l'espérance conditionnelle
    mise à l'échelle par la constante positive `Σ_{t2} w t1 t2` — les
    maximiseurs ne sont pas affectés, voir `BNE.lean`.) -/
def interimU1 (g : BayesGame2) (t1 : Fin g.nT1) (a : Fin g.nA1)
    (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => (g.w t1 t2 : Int) * g.u1 t1 t2 a (s2 t2))

/-- Utilité espérée interimaire du joueur 2 : de type `t2`, jouant l'action
    `a`, face à la stratégie `s1`, pondérée par la colonne du prior `w · t2`. -/
def interimU2 (g : BayesGame2) (t2 : Fin g.nT2) (a : Fin g.nA2)
    (s1 : Strategy1 g) : Int :=
  sumFin g.nT1 (fun t1 => (g.w t1 t2 : Int) * g.u2 t1 t2 (s1 t1) a)

/-- Utilité espérée ex-ante du joueur 1 sous un profil de stratégies :
    somme des utilités interimbaires sur les propres types du joueur 1. -/
def exAnteU1 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT1 (fun t1 => interimU1 g t1 (s1 t1) s2)

/-- Utilité espérée ex-ante du joueur 2 sous un profil de stratégies. -/
def exAnteU2 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => interimU2 g t2 (s2 t2) s1)
