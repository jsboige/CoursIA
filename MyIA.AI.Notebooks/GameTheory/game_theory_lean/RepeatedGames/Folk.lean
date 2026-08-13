/-
  Jeux répétés — Théorème de Folk (STRETCH)
  =========================================

  Le théorème de Folk (Folk années 1950, formalisé par Fudenberg–Maskin 1986,
  voir aussi Aumann–Shapley 1994 pour l'analogue en temps continu) énonce,
  dans sa version à paiement actualisé :

    Tout profil de paiement faisable et strictement individuellement
    rationnel peut être soutenu comme un équilibre de Nash sous-jeu-parfait
  à la limite quand le facteur d'actualisation δ → 1.

  Ceci est un module STRETCH, optionnel selon l'Issue #4880 (« Folk.lean —
  version minimale du Folk theorem... S'il est scaffoldé, le déclarer
  explicitement comme stretch avec ses sorries comptés — le 0-sorry n'est
  exigé que sur le théorème-phare »).

  La preuve requiert :
  - L'ensemble des paiements faisables est un polytope (fait géométrique sur
    les jeux à n étapes) ;
  - Pour chaque point faisable cible strictement à l'intérieur du polytope
    de rationalité individuelle, construire un profil de stratégies qui
    alterne entre l'action jointe cible et une phase de punition ;
  - Quand δ → 1, le poids sur la phase de punition s'évanouit, donc la
    moyenne actualisée converge vers le paiement cible.

  Ces preuves utilisent la topologie des polytopes, des arguments de points
  extrêmes et de l'optimisation sous contrainte de minmax — substantiellement
  plus difficiles que GrimTrigger. Plusieurs lemmes portent un `sorry` comme
  placeholder ; le harnais de preuve BG tentera de les résoudre lors
  d'itérations ultérieures mais ils sont marqués comme basse priorité.

  Définitions forcées par le type (leçon Lidman L39, PR #4899) :
  `IndividuallyRational` est bornée par `g.P` et `Feasible` est une contrainte
  convexe sur les quatre actions jointes, **de sorte que la correction est
  forcée par le système de types, pas par une quelconque donnée numérique
  citée** (pas de tables de type KnotInfo, pas d'étiquettes de source). Le
  `sorry` sur `folk_theorem_discounted` est la direction difficile authentique
  (topologie de polytope de Fudenberg–Maskin, HORS du périmètre du sprint
  GrimTrigger).
-/

import Mathlib.Tactic

import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger

namespace RepeatedGames

/-- Rationalité individuelle : un vecteur de paiement `u` est
    individuellement rationnel si chaque coordonnée excède le paiement de
    minmax du joueur (le pire qu'on puisse imposer à un joueur par les
    autres). Pour une DP à 2 joueurs, c'est simplement `g.P` (on peut forcer
    le joueur ligne à gagner `P` si la colonne fait toujours défaut).
    Forcé par le type via `≥ g.P` (aucune constante citée). -/
def IndividuallyRational (g : PrisonersDilemma) (u_row u_col : ℝ) : Prop :=
  u_row ≥ g.P ∧ u_col ≥ g.P

/-- Faisabilité : un vecteur de paiement est atteignable comme le paiement
    espéré d'une certaine distribution sur les actions jointes. Dans une DP
    2x2, l'ensemble faisable est l'enveloppe convexe des quatre profils de
    paiement `(R, R), (S, T), (T, S), (P, P)`, caractérisée par des poids
    non négatifs sommant à un. Forcé par le type : les formules `g.R`,
    `g.S`, `g.T`, `g.P` sont des projections de la structure
    `PrisonersDilemma`, pas des données numériques externes. -/
def Feasible (g : PrisonersDilemma) (u_row u_col : ℝ) : Prop :=
  ∃ pCC pCD pDC pDD : ℝ,  -- probability weights summing to 1
    pCC + pCD + pDC + pDD = 1 ∧
    pCC ≥ 0 ∧ pCD ≥ 0 ∧ pDC ≥ 0 ∧ pDD ≥ 0 ∧
    u_row = pCC * g.R + pCD * g.S + pDC * g.T + pDD * g.P ∧
    u_col = pCC * g.R + pCD * g.T + pDC * g.S + pDD * g.P

/-- Paiement actualisé du joueur de référence (ligne) sous une trajectoire
    d'actions conjointes `a` et facteur d'escompte `δ`. Généralise
    `coopValue` / `deviateValue` (cas particuliers stationnaires) à une
    trajectoire arbitraire : `Σ' n, δⁿ · stagePayoff g (a n).1 (a n).2`.
    Le paiement du joueur colonne sous la même trajectoire s'obtient en
    échangeant les composantes de l'action conjointe (voir
    `folk_theorem_discounted`). -/
noncomputable def discountedPayoff (g : PrisonersDilemma) (δ : ℝ)
    (a : ℕ → PDAction × PDAction) : ℝ :=
  ∑' n : ℕ, δ^n * stagePayoff g (a n).1 (a n).2

/-- Le théorème de Folk ACTUALISÉ (Fudenberg–Maskin 1986, simplifié pour 2x2) :

      Pour tout paiement faisable strictement individuellement rationnel
      `u = (u_row, u_col)`, il existe δ* < 1 tel que pour tout δ ≥ δ* le
      vecteur `u` est réalisé comme paiement actualisé d'une trajectoire
      d'actions conjointes.

    La conclusion est une **équation réelle** (`discountedPayoff … = u_row ∧
    … = u_col`), pas un `True` : le `sorry` porte donc la dette authentique
    (existence de la trajectoire réalisant le vecteur cible — construction de
    Fudenberg–Maskin par alternance action-cible / phase de punition, avec la
    convexité du polytope des paiements faisables). Ne PAS fermer sur `True` :
    la conclusion étant alors triviale, le `sorry` produirait un « −1 » sans
    mathématique (leçon #10188). La couche plus profonde — résistance à la
    déviation unilatérale en un coup (sustainment comme SPNE) — est le mur
    Fudenberg–Maskin complet, hors périmètre de ce grain (cf
    `grim_trigger_sustains_iff` pour le cas particulier grim trigger, prouvé).

    STRETCH authentique : priorité BG FAIBLE (cf critères de clôture Issue
    #4880 1). -/
theorem folk_theorem_discounted (g : PrisonersDilemma) :
    ∀ (u_row u_col : ℝ),
      IndividuallyRational g u_row u_col →
      Feasible g u_row u_col →
      u_row > g.P ∧ u_col > g.P →  -- strict IR
      ∃ (δ_star : ℝ), δ_star < 1 ∧
        ∀ (d : ℝ), d ≥ δ_star →
          ∃ (a : ℕ → PDAction × PDAction),
            discountedPayoff g d a = u_row ∧
            discountedPayoff g d (fun n => ((a n).2, (a n).1)) = u_col := by
  -- STRETCH (Fudenberg–Maskin 1986) : existence d'une trajectoire d'actions
  -- conjointes réalisant le vecteur de paiement cible (u_row, u_col) comme
  -- paiement actualisé, pour tout δ assez proche de 1. Requiert la convexité
  -- du polytope des paiements faisables et un argument de point extrême ;
  -- preuve de plusieurs pages, pas une seule tactique.
  sorry

/-- Cas limite δ = 0 : sans poids sur le futur, les valeurs actualisées se
    réduisent aux paiements de stage — le jeu répété collapse au jeu one-shot.
    C'est le cas frontière du théorème de Folk (le seul équilibre de Nash
    one-shot est (Défection, Défection) de paiement (P, P)) et il ancre la
    construction. Prouvé : formes closes de `coopValue` / `deviateValue` en
    δ = 0 (`coopValue R 0 = R / (1 − 0) = R`, `deviateValue T P 0 = T + 0 = T`). -/
theorem folk_theorem_boundary (g : PrisonersDilemma) :
    coopValue g.R 0 = g.R ∧ coopValue g.P 0 = g.P ∧ deviateValue g.T g.P 0 = g.T := by
  simp [coopValue, deviateValue]

end RepeatedGames
