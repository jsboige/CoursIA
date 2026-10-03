/-
  Socle de définitions — Core d'approbation (Becker-Greger-Peters 2026)
  =====================================================================

  Ce fichier pose les structures et fonctions de base pour la formalisation
  du core d'approbation, conformément au résultat de Becker, Greger et
  Peters (2026), arXiv 2609.11912.

  Tranche 1 du plan d'exécution de l'issue #17988 :
  - `ApprovalBallot`     — sous-ensemble des candidats approuvés par un votant
  - `ApprovalProfile`    — collection de ballots indexée par votants + taille comité
  - `Committee`          — sous-ensemble de candidats de cardinalité fixée `k`
  - `Happiness`          — utilité additive (cardinal de l'intersection approbation × comité)
  - `PaymentFunction`    — vecteur de paiements aux votants, somme nulle
  - `ApprovalAggregateUtility` — somme pondérée des bonheurs (proxy sans logarithme)

  Les définitions de `Core` (Tranche 2) et le théorème principal (Tranche 3)
  vivent dans des fichiers séparés `ApprovalCore.lean` (Tranche 2) et
  `ApprovalBGP2026.lean` (Tranche 3).

  Convention i18n #4980 : ce fichier porte le namespace `ApprovalDefs` (FR).
  Le sibling `ApprovalDefs_en.lean` porte le namespace `ApprovalDefs_en` (EN).
  Préservation byte-identity hors docstrings — vérifiée par
  `scripts/lean/check_i18n_siblings.py`.
-/

import SocialChoice.Profile

namespace ApprovalDefs

/-- Un ballot d'approbation : sous-ensemble des candidats approuvés par un votant. -/
structure ApprovalBallot (A : Type) [Fintype A] where
  approved : Finset A

/-- Un profil d'approbation : collection de ballots indexée par votants,
    avec une taille de comité cible. -/
structure ApprovalProfile (V A : Type) [Fintype V] [Fintype A] where
  ballots : V → ApprovalBallot A
  committeeSize : ℕ

/-- Un comité : sous-ensemble de candidats de cardinalité fixée `k`. -/
def Committee (A : Type) [Fintype A] (k : ℕ) : Type :=
  { S : Finset A // S.card = k }

/-- Bonheur d'un votant `v` sous un comité `S` : nombre de candidats
    approuvés par `v` qui sont dans `S`. -/
def Happiness {V A : Type} [instV : Fintype V] [instA : Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (v : V) : ℕ :=
  (P.ballots v).approved ∩ S.val |>.card

/-- Fonction de paiement : vecteur de paiements aux votants, contraints à
    somme nulle (les paiements transfèrent de l'argent aux votants, financés
    par un budget total nul). -/
structure PaymentFunction (V : Type) [Fintype V] where
  payments : V → ℚ
  zero_sum : (∑ v, payments v) = 0

/-- Utilité agrégée d'approbation : somme pondérée des bonheurs individuels,
    où le coefficient de chaque votant est `1 / (1 + p.v)` (interprétation :
    un paiement positif réduit le poids du votant, un paiement négatif
    l'augmente — c'est la **base** de la fonction objectif de BGP 2026 sans
    le logarithme).

    Cette définition sert de **proxy** à `HarmonicEntropy` (qui introduira le
    logarithme via `Mathlib.Analysis.SpecialFunctions.Log` à la Tranche 3).
    Le proxy est suffisant pour exprimer les lemmes techniques de Tranche 2
    (monotonie) qui ne dépendent pas du log lui-même. La concavité de
    `ApprovalAggregateUtility` **n'est pas** une propriété généralement
    vraie : un contre-exemple exact la fait tomber (deux votants approuvent
    le même candidat, comité singleton, donc `Happiness=(1,1)` ; pour
    `p=(a,-a)`, `U(a) = 1/(1+a) + 1/(1-a)`, et `U(0)=2`, `U(±1/2)=8/3`, ce
    qui contredit `2 ≥ 8/3`). Le lemme de Tranche 2 portera sur une
    propriété mesurable (monotonie en `S` ou en `p`), pas sur la concavité
    en `a`.

    Les poids sont strictement positifs dès lors que `p.v > -1` (hypothèse
    que la Tranche 2 documentera comme standard pour les paiements
    budgétairement neutres). -/
def ApprovalAggregateUtility {V A : Type} [instV : Fintype V] [instA : Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (p : PaymentFunction V) : ℚ :=
  ∑ v, (1 : ℚ) / (1 + p.payments v) * (Happiness P S v : ℚ)

end ApprovalDefs