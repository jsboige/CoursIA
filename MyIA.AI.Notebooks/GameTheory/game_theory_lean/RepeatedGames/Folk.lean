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
  plus difficiles que GrimTrigger. Un seul théorème porte un `sorry`, le
  STRETCH authentique `folk_theorem_discounted` ; le harnais de preuve BG
  tentera de le résoudre lors d'itérations ultérieures mais il est marqué
  comme basse priorité. Tout le reste du module est intégralement prouvé, y
  compris la réfutation par contre-exemple concret de l'énoncé non
  normalisé (`folk_theorem_discounted_unnormalized_refuted`, #15655).

  Définitions forcées par le type (leçon Lidman L39, PR #4899) :
  `IndividuallyRational` est bornée par `g.P` et `Feasible` est une contrainte
  convexe sur les quatre actions jointes, **de sorte que la correction est
  forcée par le système de types, pas par une quelconque donnée numérique
  citée** (pas de tables de type KnotInfo, pas d'étiquettes de source). Le
  `sorry` sur `folk_theorem_discounted` est la direction difficile authentique
  (topologie de polytope de Fudenberg–Maskin, HORS du périmètre du sprint
  GrimTrigger).

  Convention normalisée (#15655) : la conclusion de `folk_theorem_discounted`
  porte le facteur `(1 - δ)` sur chaque équation de paiement — la somme
  géométrique `Σ' δⁿ = 1/(1-δ)` donne à `(1-δ)·V` une masse unité, la moyenne
  pondérée des paiements de stage. Sans ce facteur, l'énoncé serait FAUX même
  dans l'intervalle convergent `0 ≤ δ < 1` : c'est exactement ce qu'établit
  `folk_theorem_discounted_unnormalized_refuted` sur le PD canonique
  `(3, 2, 1, 0)` avec la cible `(2, 2)`.
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

/-- Le théorème de Folk ACTUALISÉ (Fudenberg–Maskin 1986, simplifié pour 2x2),
    en convention NORMALISÉE (#15655) :

      Pour tout paiement faisable strictement individuellement rationnel
      `u = (u_row, u_col)`, il existe δ* < 1 tel que pour tout δ ∈ [δ*, 1) le
      vecteur `u` est réalisé comme moyenne actualisée d'une trajectoire
      d'actions conjointes : `(1 - δ) · Σ' δⁿ · payoffₙ = u`.

    Le facteur `1 - δ` n'est pas décoratif : `Σ' δⁿ = 1/(1-δ)` (lemme
    `geom_sum`), donc `(1 - δ) · V` est la moyenne pondérée des paiements de
    stage — la seule convention sous laquelle l'énoncé est vrai. La version
    NON normalisée (`V = u` sans facteur) est FAUSSE même dans `0 ≤ δ < 1`,
    réfutée par le contre-exemple intégralement prouvé
    `folk_theorem_discounted_unnormalized_refuted` ci-dessous (PD canonique
    `⟨3, 2, 1, 0⟩`, cible `(2, 2)`).

    La conclusion est une **équation réelle** (`(1 - d) * discountedPayoff … =
    u_row ∧ … = u_col`), pas un `True` : le `sorry` porte donc la dette
    authentique (existence de la trajectoire réalisant le vecteur cible —
    construction de Fudenberg–Maskin par alternance action-cible / phase de
    punition, avec la convexité du polytope des paiements faisables). Ne PAS
    fermer sur `True` : la conclusion étant alors triviale, le `sorry`
    produirait un « −1 » sans mathématique (leçon #10188). La couche plus
    profonde — résistance à la déviation unilatérale en un coup (sustainment
    comme SPNE) — est le mur Fudenberg–Maskin complet, hors périmètre de ce
    grain (cf `grim_trigger_sustains_iff` pour le cas particulier grim
    trigger, prouvé).

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
  -- STRETCH (Fudenberg–Maskin 1986) : existence d'une trajectoire d'actions
  -- conjointes réalisant le vecteur de paiement cible (u_row, u_col) comme
  -- moyenne actualisée (facteur 1 - d), pour tout d assez proche de 1.
  -- Requiert la convexité du polytope des paiements faisables et un argument
  -- de point extrême ; preuve de plusieurs pages, pas une seule tactique.
  --
  -- Deux réparations d'énoncé, chacune documentée :
  -- (2026-08-15) la borne « d < 1 » : l'ancien quantificateur « ∀ d ≥ δ* »
  -- rendait le théorème FAUX — à d ≥ 1 les séries ∑' d^n · payoff divergent
  -- et `tsum` vaut 0 (valeur junk). Le prouveur choisit δ* ≥ 0, donc
  -- d ∈ [δ*, 1) ⊆ [0, 1) et les séries convergent absolument.
  -- (2026-09-12, #15655) le facteur « 1 - d » : la conclusion NON normalisée
  -- était FAUSSE même dans [0, 1) — réfutée par
  -- folk_theorem_discounted_unnormalized_refuted ci-dessous.
  sorry

/-! ## Réfutation de l'énoncé non normalisé (#15655)

La correction du facteur `1 - d` n'est pas un raffinement : sans lui, la
conclusion de `folk_theorem_discounted` est carrément FAUSSE, même restreinte
à l'intervalle convergent `0 ≤ δ < 1` réparé en 2026-08-15. Le bloc suivant
le prouve par contre-exemple concret sur le PD canonique `(3, 2, 1, 0)` :
pour la cible `u = (2, 2)` — dont toutes les hypothèses tiennent et sont
prouvées comme conjoints du théorème de réfutation
(`pdCanonical_target_hypotheses` : faisable avec `pCC = 1`, strictement
individuellement rationnelle `2 > 1 = P`) — et pour tout seuil `δ_star < 1`,
il existe `d ∈ [δ_star, 1)` tel qu'AUCUNE trajectoire ne donne
`V_row = 2 ∧ V_col = 2`. L'argument (entièrement prouvé, zéro `sorry`) :
chaque profil d'actions paie `uₙ + vₙ ≥ 2` aux deux joueurs, donc
`V_row + V_col ≥ 2 · Σ' dⁿ = 2/(1-d) > 4` dès que `d > 1/2`. -/

/-- Le PD canonique du grain #15655 : `(T, R, P, S) = (3, 2, 1, 0)`. Les
    quatre contraintes `T > R > P > S` et `2R > T + S` (`4 > 3`) se vérifient
    par `norm_num`. C'est le témoin de
    `folk_theorem_discounted_unnormalized_refuted` : la cible `u = (2, 2)`
    y est faisable (`pCC = 1`) et strictement individuellement rationnelle
    (`2 > 1 = P`), donc la réfutation de l'énoncé non normalisé porte sur un
    point où TOUTES les hypothèses du théorème tiennent — fait prouvé par
    `pdCanonical_target_hypotheses`. -/
def pdCanonical : PrisonersDilemma where
  T := 3
  R := 2
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- Les hypothèses du théorème de Folk tiennent toutes pour le témoin
    `(g, u) = (pdCanonical, (2, 2))` : rationalité individuelle (`2 ≥ 1`),
    faisabilité (poids explicites `pCC = 1`, `pCD = pDC = pDD = 0` — la
    cible est la coopération mutuelle pure) et rationalité individuelle
    stricte (`2 > 1 = P`). Ce fait, jusque-là purement prosodique dans les
    docstrings, devient ici un lemme prouvé que
    `folk_theorem_discounted_unnormalized_refuted` expose comme conjoints de
    sa conclusion : la réfutation porte sur un point où TOUTES les hypothèses
    du théorème sont vérifiées formellement, pas seulement affirmées. -/
lemma pdCanonical_target_hypotheses :
    IndividuallyRational pdCanonical 2 2 ∧
    Feasible pdCanonical 2 2 ∧
    2 > pdCanonical.P ∧ 2 > pdCanonical.P := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  refine ⟨⟨by norm_num [hP], by norm_num [hP]⟩,
    ⟨1, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num [hT, hR, hP], by norm_num [hT, hR, hP]⟩,
    by norm_num [hP], by norm_num [hP]⟩

/-- Les paiements de stage du PD canonique vivent dans `[0, 3]` : minimum
    `S = 0`, maximum `T = 3`. Cette borne rend chaque terme `dⁿ · payoff`
    dominé par `3 · dⁿ` — le levier de sommabilité de la série actualisée
    (`summable_discounted_pdCanonical`). -/
lemma stagePayoff_pdCanonical_bounds (a b : PDAction) :
    0 ≤ stagePayoff pdCanonical a b ∧ stagePayoff pdCanonical a b ≤ 3 := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  have hS : pdCanonical.S = 0 := rfl
  cases a <;> cases b <;> norm_num [stagePayoff, hT, hR, hP, hS]

/-- Invariant clé de la réfutation : sur le PD canonique, la somme des
    paiements ligne + colonne d'un même profil d'actions joint vaut au moins
    `2` — coopération mutuelle `R + R = 4`, exploitation `T + S = 3` (dans
    les deux sens), défection mutuelle `P + P = 2`. -/
lemma stage_sum_ge_two (a b : PDAction) :
    2 ≤ stagePayoff pdCanonical a b + stagePayoff pdCanonical b a := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  have hS : pdCanonical.S = 0 := rfl
  cases a <;> cases b <;> norm_num [stagePayoff, hT, hR, hP, hS]

/-- Sommabilité de la série actualisée sur une trajectoire arbitraire du PD
    canonique : chaque terme `dⁿ · payoff` est dominé en valeur absolue par
    la série géométrique `3 · dⁿ`, sommable pour `d ∈ [0, 1)`
    (`Summable.of_norm_bounded`). -/
lemma summable_discounted_pdCanonical (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (a : ℕ → PDAction × PDAction) :
    Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).1 (a n).2 := by
  have hgeom : Summable fun n : ℕ => 3 * d^n :=
    (summable_geometric_of_lt_one hd0 hd1).mul_left 3
  have hb : ∀ n : ℕ, ‖d^n * stagePayoff pdCanonical (a n).1 (a n).2‖ ≤ 3 * d^n := by
    intro n
    have hp : 0 ≤ d^n := pow_nonneg hd0 n
    have hbd := stagePayoff_pdCanonical_bounds (a n).1 (a n).2
    have habs : |stagePayoff pdCanonical (a n).1 (a n).2| ≤ 3 := by
      rw [abs_of_nonneg hbd.1]
      exact hbd.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    calc d^n * |stagePayoff pdCanonical (a n).1 (a n).2|
        ≤ d^n * 3 := mul_le_mul_of_nonneg_left habs hp
      _ = 3 * d^n := by ring
  exact Summable.of_norm_bounded hgeom hb

/-- Inégalité terme à terme : pour `d ≥ 0`, le double de chaque poids
    géométrique `2 · dⁿ` est dominé par la somme des deux termes actualisés
    (ligne + colonne) de l'étage `n` — `stage_sum_ge_two` multiplié par
    `dⁿ ≥ 0`. -/
lemma pair_terms_ge_two (d : ℝ) (hd0 : 0 ≤ d) (n : ℕ)
    (a : ℕ → PDAction × PDAction) :
    2 * d^n ≤ d^n * stagePayoff pdCanonical (a n).1 (a n).2
            + d^n * stagePayoff pdCanonical (a n).2 (a n).1 := by
  have h2 := stage_sum_ge_two (a n).1 (a n).2
  have hp : 0 ≤ d^n := pow_nonneg hd0 n
  have h := mul_le_mul_of_nonneg_right h2 hp
  calc 2 * d^n
      ≤ (stagePayoff pdCanonical (a n).1 (a n).2
          + stagePayoff pdCanonical (a n).2 (a n).1) * d^n := h
    _ = d^n * stagePayoff pdCanonical (a n).1 (a n).2
        + d^n * stagePayoff pdCanonical (a n).2 (a n).1 := by ring

/-- Cœur mathématique de la réfutation : pour tout `d ∈ (1/2, 1)`, AUCUNE
    trajectoire du PD canonique ne réalise `V_row = 2 ∧ V_col = 2` en
    paiements actualisés NON normalisés. Si les deux équations tenaient, la
    somme des séries donnerait `∑' dⁿ · (uₙ + vₙ) = 4` (additivité du `tsum`,
    sommabilité par comparaison géométrique) alors que `uₙ + vₙ ≥ 2` à chaque
    étage forcerait `∑' dⁿ · (uₙ + vₙ) ≥ 2 · ∑' dⁿ = 2/(1-d) > 4` dès
    `d > 1/2` — contradiction. -/
theorem unnormalized_pair_payoff_refuted (d : ℝ) (hd : 1/2 < d) (hd1 : d < 1)
    (a : ℕ → PDAction × PDAction) :
    ¬ (discountedPayoff pdCanonical d a = 2 ∧
       discountedPayoff pdCanonical d (fun n => ((a n).2, (a n).1)) = 2) := by
  have hd0 : 0 ≤ d := by linarith
  intro h
  obtain ⟨hrow, hcol⟩ := h
  simp only [discountedPayoff] at hrow hcol
  have hsu : Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).1 (a n).2 :=
    summable_discounted_pdCanonical d hd0 hd1 a
  have hsv : Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).2 (a n).1 :=
    summable_discounted_pdCanonical d hd0 hd1 fun n => ((a n).2, (a n).1)
  have hsum : ∑' n : ℕ, (d^n * stagePayoff pdCanonical (a n).1 (a n).2
      + d^n * stagePayoff pdCanonical (a n).2 (a n).1) = 4 := by
    rw [Summable.tsum_add hsu hsv, hrow, hcol]
    ring
  have hgeom : ∑' n : ℕ, d^n = (1 - d)⁻¹ := tsum_geometric_of_lt_one hd0 hd1
  have hsum2 : Summable fun n : ℕ => 2 * d^n := by
    have he : (fun n : ℕ => 2 * d^n) = fun n : ℕ => d^n + d^n :=
      funext fun n => by ring
    rw [he]
    exact Summable.add (summable_geometric_of_lt_one hd0 hd1)
      (summable_geometric_of_lt_one hd0 hd1)
  have hle : ∑' n : ℕ, 2 * d^n
      ≤ ∑' n : ℕ, (d^n * stagePayoff pdCanonical (a n).1 (a n).2
          + d^n * stagePayoff pdCanonical (a n).2 (a n).1) :=
    hsum2.tsum_le_tsum (fun n => pair_terms_ge_two d hd0 n a) (hsu.add hsv)
  have hval : ∑' n : ℕ, 2 * d^n = 2 * ∑' n : ℕ, d^n := by
    have he : (fun n : ℕ => 2 * d^n) = fun n : ℕ => d^n + d^n :=
      funext fun n => by ring
    rw [he, Summable.tsum_add (summable_geometric_of_lt_one hd0 hd1)
      (summable_geometric_of_lt_one hd0 hd1)]
    ring
  have hfinal : (2:ℝ) / (1 - d) ≤ 4 := by
    have heq : (2:ℝ) / (1 - d) = 2 * ∑' n : ℕ, d^n := by
      rw [hgeom]; ring
    rw [heq, ← hval]
    linarith
  have hpos : 0 < 1 - d := by linarith
  have hgt : 4 < 2 / (1 - d) := by
    apply (lt_div_iff₀ hpos).mpr
    have hlt : 1 - d < 1 / 2 := by linarith
    have h4 : 4 * (1 - d) < 4 * (1 / 2) := mul_lt_mul_of_pos_left hlt (by norm_num)
    have h2 : (4:ℝ) * (1 / 2) = 2 := by norm_num
    linarith
  linarith

/-- **Réfutation de l'énoncé non normalisé** (#15655) : sur le PD canonique
    `(T, R, P, S) = (3, 2, 1, 0)` pour la cible `u = (2, 2)` — dont TOUTES
    les hypothèses de `folk_theorem_discounted` tiennent et sont exposées
    comme conjoints PROUVÉS de la conclusion (rationalité individuelle,
    faisabilité à poids explicites `pCC = 1`, rationalité individuelle
    stricte — via `pdCanonical_target_hypotheses`) — pour TOUT seuil
    `δ_star < 1` il existe un facteur `d ∈ [δ_star, 1)` (savoir
    `d = max δ_star (3/4) ∈ [3/4, 1) ⊂ (1/2, 1)`) tel qu'AUCUNE trajectoire
    d'actions conjointes ne réalise `V_row = 2 ∧ V_col = 2` en paiements
    actualisés NON normalisés. L'ancienne conclusion de
    `folk_theorem_discounted` (équations sans le facteur `1 - d`) était donc
    fausse ; c'est la non-régression du grain #15655 : ce théorème entièrement
    prouvé (zéro `sorry`) empêche de re-proposer l'énoncé non normalisé. -/
theorem folk_theorem_discounted_unnormalized_refuted :
    ∀ (δ_star : ℝ), δ_star < 1 →
      ∃ (d : ℝ), δ_star ≤ d ∧ d < 1 ∧
        IndividuallyRational pdCanonical 2 2 ∧
        Feasible pdCanonical 2 2 ∧
        2 > pdCanonical.P ∧ 2 > pdCanonical.P ∧
        ∀ (a : ℕ → PDAction × PDAction),
          ¬ (discountedPayoff pdCanonical d a = 2 ∧
             discountedPayoff pdCanonical d (fun n => ((a n).2, (a n).1)) = 2) := by
  intro δ_star hδ
  obtain ⟨hir, hfeas, hgt1, hgt2⟩ := pdCanonical_target_hypotheses
  refine ⟨max δ_star (3 / 4), le_max_left _ _, max_lt hδ (by norm_num),
    hir, hfeas, hgt1, hgt2, ?_⟩
  intro a h
  have h34 : 1 / 2 < max δ_star (3 / 4) := by
    have hle34 := le_max_right δ_star (3 / 4)
    linarith
  exact unnormalized_pair_payoff_refuted _ h34 (max_lt hδ (by norm_num)) a h

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
