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

/-- Convexité de l'ensemble faisable (#14990) : toute combinaison convexe de
    deux vecteurs de paiements faisables est faisable. Première brique du
    théorème de Folk — la construction Fudenberg–Maskin interpole entre
    l'action jointe cible et une phase de punition, elle exige donc que
    l'ensemble des paiements réalisables soit stable par barycentre. Preuve
    directe sur l'existentiel `Feasible` (pas de `convexHull` de Mathlib) :
    les poids témoins se combinent en `lam * p + (1 - lam) * q`, qui reste
    non négatif (produits de non négatifs) et somme à un (combinaison affine
    des deux sommes unité). -/
theorem feasible_convex (g : PrisonersDilemma) (lam : ℝ)
    (u1_row u1_col u2_row u2_col : ℝ)
    (h1 : Feasible g u1_row u1_col) (h2 : Feasible g u2_row u2_col)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Feasible g (lam * u1_row + (1 - lam) * u2_row)
                (lam * u1_col + (1 - lam) * u2_col) := by
  obtain ⟨pCC1, pCD1, pDC1, pDD1, hs1, ha1, ha2, ha3, ha4, hr1, hc1⟩ := h1
  obtain ⟨pCC2, pCD2, pDC2, pDD2, hs2, hb1, hb2, hb3, hb4, hr2, hc2⟩ := h2
  have h1l : 0 ≤ 1 - lam := by nlinarith
  refine ⟨lam * pCC1 + (1 - lam) * pCC2, lam * pCD1 + (1 - lam) * pCD2,
    lam * pDC1 + (1 - lam) * pDC2, lam * pDD1 + (1 - lam) * pDD2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination lam * hs1 + (1 - lam) * hs2
  · exact add_nonneg (mul_nonneg hlam ha1) (mul_nonneg h1l hb1)
  · exact add_nonneg (mul_nonneg hlam ha2) (mul_nonneg h1l hb2)
  · exact add_nonneg (mul_nonneg hlam ha3) (mul_nonneg h1l hb3)
  · exact add_nonneg (mul_nonneg hlam ha4) (mul_nonneg h1l hb4)
  · linear_combination lam * hr1 + (1 - lam) * hr2
  · linear_combination lam * hc1 + (1 - lam) * hc2

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

/-- Témoin de réfutation (#15655) : le DP `T = 3, R = 2, P = 1, S = 0` —
lecture positionnelle de `(3, 2, 1, 0)` dans l'ordre des champs `(T, R, P, S)`.
Les quatre axiomes de `PrisonersDilemma` se vérifient par `norm_num` (aucune
donnée numérique citée en aval : tout est porté par la structure). Ce jeu
porte la cible faisable strictement IR `u = (2, 2)` (le sommet coopératif
`(R, R)`), qui réfute l'énoncé non normalisé du théorème de Folk actualisé —
voir `folk_theorem_discounted_unnormalized_refuted`. -/
def folkCounterexample : PrisonersDilemma where
  T := 3
  R := 2
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- Les hypothèses du théorème de Folk sont SATISFAITES par le témoin : pour
`folkCounterexample` (T3, R2, P1, S0), la cible `u = (2, 2)` est
individuellement rationnelle, faisable (le sommet coopératif `(R, R)` : poids
`pCC = 1`, autres nuls) et strictement individuellement rationnelle
(`2 > P`). La réfutation ci-dessous porte donc sur l'énoncé lui-même, pas sur
un artefact d'hypothèse. -/
theorem folkCounterexample_hypotheses :
    IndividuallyRational folkCounterexample 2 2 ∧
      Feasible folkCounterexample 2 2 ∧
      (2 > folkCounterexample.P ∧ 2 > folkCounterexample.P) := by
  refine ⟨⟨?_, ?_⟩, ⟨1, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [folkCounterexample]

/-- Somme des paiements de stage symétrisée sur le jeu témoin : toute paire
de coups rapporte au total au moins `2`. Les quatre cas possibles donnent
`R + R = 4` (coopération), `S + T = 3` et `T + S = 3` (exploitation),
`P + P = 2` (défection mutuelle) — le minimum est le niveau de défection. -/
lemma stage_sum_ge_two (x y : PDAction) :
    2 ≤ stagePayoff folkCounterexample x y + stagePayoff folkCounterexample y x := by
  cases x <;> cases y <;> simp only [stagePayoff, folkCounterexample] <;> norm_num

/-- **Réfutation de l'énoncé NON NORMALISÉ** (#15655). L'ancienne conclusion du
théorème de Folk actualisé — `discountedPayoff g d a = u_row ∧ … = u_col` sur
les séries BRUTES — est FAUSSE, et ce pour n'importe quel seuil `δ_star < 1` :
sur le jeu témoin `folkCounterexample` (T3, R2, P1, S0) et la cible faisable
strictement IR `u = (2, 2)`, aucune trajectoire ne peut réaliser le couple
`(2, 2)` dès que `d > 1/2`.

    Argument (par l'absurde) : chaque profil de stage rapporte au total au
    moins `2` (`stage_sum_ge_two`), donc la somme des deux séries vaut
    `Σ' dⁿ · (p_row + p_col) ≥ 2 · Σ' dⁿ = 2 / (1 - d)`. Si les deux paiements
    actualisés valaient `2` chacun, la somme vaudrait `4` — or `2 / (1 - d) > 4`
    dès que `d > 1/2`. Pour tout `δ_star < 1` on choisit `d = max δ_star (3/4)`
    (qui vérifie `δ_star ≤ d < 1` et `d > 1/2`) et la contradiction éclate.

    Détail technique : chaque série est sommable car sa somme vaut `2 ≠ 0`
    (`tsum_eq_zero_of_not_summable`), ce qui permet `Summable.tsum_add` puis la
    comparaison `Summable.tsum_le_tsum` avec la série géométrique (dé doublée
    `dⁿ + dⁿ` pour rester dans les lemmes de base des sommes infinies). L'énoncé
    corrigé `folk_theorem_discounted` normalise les deux équations par
    `1 - d` : la cible est le paiement MOYEN actualisé, dont la somme vaut
    `u_row + u_col`, compatible avec la minoration en `2`. -/
theorem folk_theorem_discounted_unnormalized_refuted :
    ¬ ∃ (δ_star : ℝ), δ_star < 1 ∧
      ∀ (d : ℝ), d ≥ δ_star → d < 1 →
        ∃ (a : ℕ → PDAction × PDAction),
          discountedPayoff folkCounterexample d a = 2 ∧
          discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) = 2 := by
  rintro ⟨δ_star, hδs, hall⟩
  have hdl : max δ_star (3 / 4) < 1 := max_lt_iff.mpr ⟨hδs, by norm_num⟩
  obtain ⟨a, ha1, ha2⟩ := hall (max δ_star (3 / 4)) (le_max_left _ _) hdl
  set d := max δ_star (3 / 4)
  have hd0 : (1 / 2 : ℝ) < d := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hdnn : 0 ≤ d := by linarith
  have hs1 : Summable fun n : ℕ =>
      d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2 := by
    by_contra hns
    simp only [discountedPayoff] at ha1
    rw [tsum_eq_zero_of_not_summable hns] at ha1
    norm_num at ha1
  have hs2 : Summable fun n : ℕ =>
      d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by
    by_contra hns
    simp only [discountedPayoff] at ha2
    rw [tsum_eq_zero_of_not_summable hns] at ha2
    norm_num at ha2
  have h4 : discountedPayoff folkCounterexample d a
      + discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) = 4 := by
    rw [ha1, ha2]; norm_num
  have hgeo : Summable fun n : ℕ => d ^ n := summable_geometric_of_lt_one hdnn hdl
  have hlb : ∀ n : ℕ, d ^ n + d ^ n
      ≤ d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
        + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by
    intro n
    have hp : 2 ≤ stagePayoff folkCounterexample (a n).1 (a n).2
        + stagePayoff folkCounterexample (a n).2 (a n).1 :=
      stage_sum_ge_two (a n).1 (a n).2
    have hdn : 0 ≤ d ^ n := pow_nonneg (by linarith) n
    calc d ^ n + d ^ n = d ^ n * 2 := by ring
      _ ≤ d ^ n * (stagePayoff folkCounterexample (a n).1 (a n).2
          + stagePayoff folkCounterexample (a n).2 (a n).1) :=
        mul_le_mul_of_nonneg_left hp hdn
      _ = d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by ring
  have hbound : 2 / (1 - d) ≤ discountedPayoff folkCounterexample d a
      + discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) := by
    have hgeo' : ∑' n : ℕ, (d ^ n + d ^ n) = 2 / (1 - d) := by
      rw [Summable.tsum_add hgeo hgeo, tsum_geometric_of_lt_one hdnn hdl]; ring
    rw [← hgeo']
    simp only [discountedPayoff]
    calc ∑' n : ℕ, (d ^ n + d ^ n)
        ≤ ∑' n : ℕ, (d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1) :=
        Summable.tsum_le_tsum hlb (hgeo.add hgeo) (hs1.add hs2)
      _ = ∑' n : ℕ, d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + ∑' n : ℕ, d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 :=
        Summable.tsum_add hs1 hs2
  rw [h4] at hbound
  have h1pos : 0 < 1 - d := by linarith
  rw [div_le_iff₀ h1pos] at hbound
  ring_nf at hbound
  have h4d : (2 : ℝ) < 4 * d := by
    have hmul := mul_lt_mul_of_pos_left hd0 (show (0 : ℝ) < 4 by norm_num)
    norm_num at hmul
    exact hmul
  linarith

/-- Le théorème de Folk ACTUALISÉ (Fudenberg–Maskin 1986, simplifié pour 2x2),
    forme NORMALISÉE (#15655) :

      Pour tout paiement faisable strictement individuellement rationnel
      `u = (u_row, u_col)`, il existe δ* < 1 tel que pour tout δ ∈ [δ*, 1) le
      vecteur `u` est réalisé comme paiement MOYEN actualisé d'une trajectoire
      d'actions conjointes — chaque équation porte le facteur `1 - d` :
      `(1 - d) · Σ' dⁿ · payoff = u`.

    La normalisation n'est pas décorative : l'énoncé BRUT
    (`discountedPayoff … = u` sans facteur) est réfuté formellement par
    `folk_theorem_discounted_unnormalized_refuted` ci-dessus — sur le jeu
    témoin (T3, R2, P1, S0) et la cible faisable strictement IR (2, 2), la
    somme des deux séries est minorée par `2 / (1 - d) > 4` dès que `d > 1/2`,
    donc aucune trajectoire ne peut réaliser le couple brut près de 1. Le
    paiement MOYEN, lui, échappe à la réfutation : sa somme vaut
    `u_row + u_col`, dans la plage permise par la minoration.

    La conclusion reste une **équation réelle** (`(1 - d) * discountedPayoff …
    = u_row ∧ … = u_col`), pas un `True` : le `sorry` porte donc la dette
    authentique
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
        ∀ (d : ℝ), d ≥ δ_star → d < 1 →
          ∃ (a : ℕ → PDAction × PDAction),
            (1 - d) * discountedPayoff g d a = u_row ∧
            (1 - d) * discountedPayoff g d (fun n => ((a n).2, (a n).1)) = u_col := by
  -- Énoncé normalisé (2026-09-13, #15655) : facteur `1 - d` sur les DEUX
  -- équations — c'est le paiement MOYEN actualisé, la conclusion standard de
  -- Fudenberg–Maskin. L'ancienne conclusion non normalisée était FAUSSE :
  -- réfutée formellement par `folk_theorem_discounted_unnormalized_refuted`
  -- (témoin T3/R2/P1/S0, u = (2, 2) : chaque stage rapporte au total ≥ 2,
  -- donc la somme des deux séries ≥ 2 / (1 - d) > 4 = u_row + u_col dès que
  -- d > 1/2 — aucune trajectoire ne réalise le couple brut près de 1).
  --
  -- STRETCH (Fudenberg–Maskin 1986) : existence d'une trajectoire d'actions
  -- conjointes réalisant le vecteur de paiement cible (u_row, u_col) comme
  -- paiement moyen actualisé, pour tout δ assez proche de 1. Requiert la
  -- convexité du polytope des paiements faisables et un argument de point
  -- extrême ; preuve de plusieurs pages, pas une seule tactique.
  --
  -- Bord d'énoncé réparé (2026-08-15) : l'ancien quantificateur « ∀ d ≥ δ* »
  -- (sans borne d < 1) rendait le théorème FAUX — à d ≥ 1 les séries
  -- ∑' d^n · payoff divergent et `tsum` vaut 0 (valeur junk), si bien qu'aucun
  -- u ≠ 0 n'est réalisable (témoin : g = ⟨3, 2, 1, 0⟩, u = (2, 2), d = 2).
  -- La borne « d < 1 » répare sans renforcer : le prouveur choisit δ* ≥ 0,
  -- donc d ∈ [δ*, 1) ⊆ [0, 1) et les séries convergent absolument.
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
