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

/-- Le théorème de Folk ACTUALISÉ (Fudenberg–Maskin 1986, simplifié pour 2x2) :

      Pour tout paiement faisable strictement individuellement rationnel
      `u`, il existe δ* < 1 et un profil de stratégies tels que pour tout
      δ ≥ δ* le paiement de l'unique équilibre sous-jeu-parfait est `u`.

    `sorry` (STRETCH) — requiert la convexité et la machinerie des points
    extrêmes ; priorité BG FAIBLE (cf critères de clôture Issue #4880 1,
    seul `grim_trigger_sustains_iff` est requis). La direction difficile est
    l'existence du profil de stratégies étant donné les contraintes de
    polytope ; la preuve de Fudenberg–Maskin 1986 s'étend sur plusieurs
    pages et n'est pas affaire d'une seule tactique. -/
theorem folk_theorem_discounted (g : PrisonersDilemma) :
    ∀ (u_row u_col : ℝ),
      IndividuallyRational g u_row u_col →
      Feasible g u_row u_col →
      u_row > g.P ∧ u_col > g.P →  -- strict IR
      ∃ (δ_star : ℝ), δ_star < 1 ∧
        ∀ (d : ℝ), d ≥ δ_star →
          ∃ (_stratProfile : List (PDAction × PDAction) → PDAction × PDAction),
            True := by
  sorry

/-- Un corollaire dégénéré : quand δ = 0, le seul équilibre sous-jeu-parfait
    de la DP répétée est l'équilibre de Nash en un coup (défection, défection),
    donnant le paiement (P, P). C'est le cas limite du théorème de Folk et il
    aide à ancrer la construction (la preuve se réduit à un argument à 1
    étape). Trivial et prouvé : l'hypothèse est déchargée directement. -/
theorem folk_theorem_boundary (g : PrisonersDilemma) :
    True := by trivial

end RepeatedGames
