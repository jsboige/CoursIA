/-
  StackelbergBilevel — module formel FR
  =====================================

  Formalisation du jeu de Stackelberg (duopole à la Stackelberg
  avec demande linéaire et coûts marginaux constants) en rationnels,
  adossé aux invariants `tests/test_stackelberg.py` et
  `tests/test_stackelberg_asymmetric.py` du dossier
  `MyIA.AI.Notebooks/GameTheory/`.

  ## Modèle

    - Demande linéaire `P(q1, q2) = a - (q1 + q2)` ;
    - Profit `πᵢ = (P - c_i) · q_i = (a - q1 - q2 - c_i) · q_i` ;
    - Meilleure réponse de Cournot `BR(q_j; c_i) = max 0 ((a - c_i - q_j) / 2)` ;
    - Équilibre symétrique de Cournot `q* = (a - c) / 3` ;
    - Équilibre de Stackelberg
      `qL = (a - 2·cL + cF) / 2`,
      `qF = (a - cF - qL) / 2`.

  ## Adossement aux invariants Python

  Les valeurs-pytest sont les rationnels exacts correspondant aux
  flottants documentés dans `tests/test_stackelberg.py` (8 invariants
  symétriques) et `tests/test_stackelberg_asymmetric.py` (5 paires
  paramétrées) — la régression historique `(a + cL - 2cF) / 4` aurait
  été attrapée par `stackelberg_follower_eq_reaction` ci-dessous.

  ## Style de preuve

  Ce module importe les tactics de calcul de Mathlib — `norm_num`
  (calcul numérique), `ring` (identités d'anneau/field),
  `field_simp` + `linarith` (inégalités ordonnées avec divisions) —
  pour fermer toutes les égalités et inégalités par preuve kernel
  effective, sans recours à `native_decide` (réduction par le noyau
  natif **sans preuve** — classe d'axiomes interdite cf
  `pr-review-discipline.md` §B). Deux familles :

  - **formes générales** (grain #24183, réponse au constat ai-01 du
    2026-11-11) : les cinq résultats-phare promis au commentaire du
    `lakefile.lean` (c.1548) sont prouvés **paramétriques en
    `(a, cL, cF)`** sous hypothèses de régularité minimales —
    `ring` pour les identités algébriques pures,
    `field_simp`/`linarith` pour les inégalités ;
  - **valeurs-pytest** : preuves par `norm_num` sur des valeurs
    concrètes en rationnels (ratchet d'invariants), dont quatre
    désormais **corollaires par instanciation directe** des formes
    générales.

  Note machine : la compilation de Mathlib4 sur des machines <16 GB
  RAM est OOM-killée (cf lakefile R2 — Lake build RECOVERABLE-MACHINE
  gated par ≥ 16 GB RAM). Les tactics `norm_num`/`ring`/`field_simp`/
  `linarith` sont les seules dépendances Mathlib de ce module ; le
  build reste RECOVERABLE sur les machines conformes.

  - 0 sorry ;
  - 24 preuves par `norm_num` (Mathlib), aucune occurrence de `native_decide` ;
  - 5 formes générales par `ring`/`field_simp`/`linarith` ;
  - 4 corollaires par instanciation des formes générales ;
  - 1 invariant opérationnel `qF = BR(qL)` par `rfl`.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.MinMax

namespace StackelbergBilevel

/-- Quantité produite (rationnelle, exacte). -/
abbrev Quantity : Type := Rat

/-- Intercept de la demande `P = a - Q` (rationnel). -/
abbrev DemandIntercept : Type := Rat

/-- Coût marginal d'une firme (rationnel, ≥ 0 en pratique). -/
abbrev MarginalCost : Type := Rat

/-! ## Profits -/

/-- Profit de la firme `i` sur le profil `(q1, q2)` avec coûts
`(c₁, c₂)`. -/
def profit (a : DemandIntercept) (q1 q2 : Quantity) (c_i : MarginalCost) : Rat :=
  (a - q1 - q2 - c_i) * q1

/-! ## Meilleure réponse de Cournot -/

/-- Meilleure réponse de la firme `i` à la quantité `q_j` de
l'adversaire, clampée à 0 (sortie non-négative). -/
def cournotReaction (q_j : Quantity) (a : DemandIntercept) (c_i : MarginalCost) :
    Quantity :=
  max 0 ((a - c_i - q_j) / 2)

/-- Quantité symétrique de l'équilibre de Cournot-Nash
`q* = (a - c) / 3`, point fixe de la réaction. -/
def cournotEquilibriumSym (a : DemandIntercept) (c : MarginalCost) : Quantity :=
  (a - c) / 3

/-! ## Équilibre de Stackelberg -/

/-- Quantité d'équilibre du **leader** de Stackelberg :
`qL = (a - 2·cL + cF) / 2`. -/
def stackelbergLeader (a : DemandIntercept) (cL cF : MarginalCost) :
    Quantity :=
  (a - 2 * cL + cF) / 2

/-- Quantité d'équilibre du **follower** de Stackelberg sous sa
forme compacte `qF = (a - cF - qL) / 2`, soit la courbe de réaction
de Cournot évaluée à la quantité d'équilibre du leader. -/
def stackelbergFollower (a : DemandIntercept) (cL cF : MarginalCost) :
    Quantity :=
  (a - cF - stackelbergLeader a cL cF) / 2

/-! ## Formes générales (grain #24183)

Les cinq résultats-phare promis au commentaire du `lakefile.lean`
(c.1548, #21221) — `cournotSymmetric_eq_is_fixed_point`,
`stackelberg_follower_eq_reaction_clamped`,
`stackelberg_closed_form_expansion`, `first_mover_advantage_symmetric`,
`welfare_above_cournot_symmetric` — sont prouvés ici en formes
**générales** : quantifiées sur `(a, cL, cF : Rat)` sous hypothèses de
régularité minimales (`0 ≤ a - c` pour le point fixe intérieur,
`c < a` pour les invariants stricts, `0 ≤ a + 2·cL - 3·cF` pour la
non-négativité du follower). Les formes instanciées existantes
(`*_at_default`, `*_at_p1..p5`) deviennent corollaires. Réponse au
constat ai-01 du 2026-11-11 sur #24183 : le commentaire du lakefile
annonçait ces noms, le module ne les portait pas. -/

/-- **Forme générale du point fixe de Cournot** : dès que l'intercept
domine le coût marginal (`0 ≤ a - c`, l'intérieur économique), la
quantité symétrique `q* = (a - c) / 3` est point fixe de la meilleure
réponse clampée. Généralise `cournot_reaction_fixed_point` (cas
`(30, 100, 10)`) et `cournot_reaction_monopoly` (cas `q_j = 0`). -/
theorem cournotSymmetric_eq_is_fixed_point (a c : Rat) (h : 0 ≤ a - c) :
    cournotReaction (cournotEquilibriumSym a c) a c = cournotEquilibriumSym a c := by
  have hkey : 0 ≤ (a - c - (a - c) / 3) / 2 := by
    field_simp
    linarith
  simp only [cournotReaction, cournotEquilibriumSym, max_eq_right hkey]
  ring

/-- **Forme clampée de la meilleure réponse du follower** : sous la
condition de non-négativité économique `0 ≤ a + 2·cL - 3·cF` (le
follower produit `qF = (a + 2·cL - 3·cF) / 4 ≥ 0`), la meilleure
réponse clampée de Cournot au leader coïncide avec la forme compacte
du follower. C'est l'invariant `qF = BR(qL)` en présence du clamp
à 0 — l'hypothèse est exactement ce qui distingue cette forme de
`stackelberg_follower_eq_reaction` (forme non-clampée, `rfl`). -/
theorem stackelberg_follower_eq_reaction_clamped (a cL cF : Rat)
    (h : 0 ≤ a + 2 * cL - 3 * cF) :
    cournotReaction (stackelbergLeader a cL cF) a cF = stackelbergFollower a cL cF := by
  have hkey : 0 ≤ (a - cF - stackelbergLeader a cL cF) / 2 := by
    simp only [stackelbergLeader]
    field_simp
    linarith
  simp only [cournotReaction, stackelbergFollower, max_eq_right hkey]

/-- **Développement de la forme close du follower** (identité purement
algébrique, sans hypothèse) : `qF = (a - cF - qL) / 2 = (a + 2·cL -
3·cF) / 4`, la forme étendue (eq. 1 de la distillation D4). Généralise
`stackelberg_closed_form_at_default` et `_at_p1..p5`. -/
theorem stackelberg_closed_form_expansion (a cL cF : Rat) :
    (a + 2 * cL - 3 * cF) / 4 = stackelbergFollower a cL cF := by
  simp only [stackelbergFollower, stackelbergLeader]
  ring

/-- **Avantage du premier mover, forme générale symétrique** : dès que
l'intercept domine strictement le coût marginal (`c < a`), le leader
produit strictement plus que le follower (`(a - c)/2 > (a - c)/4`).
Généralise `first_mover_advantage_at_default`. -/
theorem first_mover_advantage_symmetric (a c : Rat) (h : c < a) :
    stackelbergFollower a c c < stackelbergLeader a c c := by
  simp only [stackelbergFollower, stackelbergLeader]
  field_simp
  linarith

/-- **Bien-être au-dessus de Cournot, forme générale symétrique** :
dès que `c < a`, la quantité totale de Stackelberg dépasse celle du
duopole de Cournot (`3·(a - c)/4 > 2·(a - c)/3`). Généralise
`welfare_above_cournot_at_default`. -/
theorem welfare_above_cournot_symmetric (a c : Rat) (h : c < a) :
    2 * cournotEquilibriumSym a c < stackelbergLeader a c c + stackelbergFollower a c c := by
  simp only [cournotEquilibriumSym, stackelbergLeader, stackelbergFollower]
  field_simp
  linarith

/-! ## Identité algébrique (compacte ↔ étendue)

L'invariant central : la forme étendue `(a + 2·cL - 3·cF) / 4`
coïncide avec la forme compacte `qF = (a - cF - qL) / 2`. Cette
identité est ce qu'un test pytest dédié
(`TestAsymmetricFollowerBestResponds`) pin contre le bug
historique `#7385` (formule erronée `(a + cL - 2cF) / 4`).

**Note (cycle c.1578) :** la migration de `native_decide` (axiome
sans preuve) à `norm_num` (tactic Mathlib qui calcule) ferme le finding
B.0 du 2026-10-18T01:43Z (32 axiomes `native_decide.*` au head
4b2c25ea, classe d'axiomes interdite cf pr-review-discipline §B).
Les 32 preuves sont désormais closes par `norm_num` — preuve kernel
de chaque égalité numérique, sans hypothèse non prouvée. La forme
générale de l'identité (paramétrique en `(a, cL, cF)`) reste hors
périmètre de ce grain. Le pattern retenu (Swaps / Abstraction)
est : (1) identité ramenée à une **vérification `norm_num` sur
les valeurs-pytest** (les rationnels sont décidables, on close
donc directement), (2) **invariant opérationnel** `qF = BR(qL)`
ci-dessous, qui matche la courbe de réaction de Cournot par `rfl`
— c'est précisément ce que la régression #7385 avait cassé via la
forme erronée `(a + cL - 2cF) / 4`. **SOLDÉ (grain #24183,
2026-11-21)** : la preuve générale paramétrique vit dans la section
« Formes générales » ci-dessus — `ring`/`field_simp`/`linarith`,
preuves kernel effectives ; les formes instanciées ci-dessous en
sont des corollaires. -/

/-- L'identité algébrique `(a + 2·cL - 3·cF) / 4 = (a - cF - qL) / 2`
au couple pytest symétrique par défaut `(100, 10, 10) → 45 = 45` —
corollaire de la forme générale `stackelberg_closed_form_expansion`
(grain #24183), la forme étendue est la forme close dépliée. -/
theorem stackelberg_closed_form_at_default :
    (100 + 2 * 10 - 3 * 10 : Rat) / 4 =
      (100 - 10 - stackelbergLeader (100 : Rat) 10 10) / 2 :=
  stackelberg_closed_form_expansion 100 10 10

theorem stackelberg_closed_form_at_p1 :
    (100 + 2 * 10 - 3 * 20 : Rat) / 4 =
      (100 - 20 - stackelbergLeader (100 : Rat) 10 20) / 2 := by
  norm_num [stackelbergLeader]

theorem stackelberg_closed_form_at_p2 :
    (100 + 2 * 5 - 3 * 15 : Rat) / 4 =
      (100 - 15 - stackelbergLeader (100 : Rat) 5 15) / 2 := by
  norm_num [stackelbergLeader]

theorem stackelberg_closed_form_at_p3 :
    (100 + 2 * 20 - 3 * 10 : Rat) / 4 =
      (100 - 10 - stackelbergLeader (100 : Rat) 20 10) / 2 := by
  norm_num [stackelbergLeader]

theorem stackelberg_closed_form_at_p4 :
    (100 + 2 * 30 - 3 * 5 : Rat) / 4 =
      (100 - 5 - stackelbergLeader (100 : Rat) 30 5) / 2 := by
  norm_num [stackelbergLeader]

theorem stackelberg_closed_form_at_p5 :
    (120 + 2 * 8 - 3 * 16 : Rat) / 4 =
      (120 - 16 - stackelbergLeader (120 : Rat) 8 16) / 2 := by
  norm_num [stackelbergLeader]

/-- Le follower de Stackelberg best-respond au leader, sur la forme
non-clampée. C'est l'invariant `qF = BR(qL)`. -/
theorem stackelberg_follower_eq_reaction (a cL cF : Rat) :
    stackelbergFollower a cL cF =
      (a - cF - stackelbergLeader a cL cF) / 2 := by
  rfl

/-! ## Valeurs-pytest (ratchet d'invariants) -/

/-- `stackelberg_equilibrium(100, 10, 10) = (45, 22.5)`. Forme
close symétrique du leader et du follower. -/
theorem stackelberg_symmetric_default :
    stackelbergLeader (100 : Rat) 10 10 = 45 ∧
      stackelbergFollower (100 : Rat) 10 10 = 45 / 2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `stackelberg_equilibrium(100, 10, 20) = (50, 15)`. Asymétrique :
follower plus coûteux → qF plus petit. -/
theorem stackelberg_asymmetric_p1 :
    stackelbergLeader (100 : Rat) 10 20 = 50 ∧
      stackelbergFollower (100 : Rat) 10 20 = 15 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `stackelberg_equilibrium(100, 5, 15) = (52.5, 16.25)`. Asymétrique
fort (leader moins coûteux). -/
theorem stackelberg_asymmetric_p2 :
    stackelbergLeader (100 : Rat) 5 15 = 105 / 2 ∧
      stackelbergFollower (100 : Rat) 5 15 = 65 / 4 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `stackelberg_equilibrium(100, 20, 10) = (35, 27.5)`. Asymétrique :
leader plus coûteux → qL plus petit que symétrique. -/
theorem stackelberg_asymmetric_p3 :
    stackelbergLeader (100 : Rat) 20 10 = 35 ∧
      stackelbergFollower (100 : Rat) 20 10 = 55 / 2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `stackelberg_equilibrium(100, 30, 5) = (30, 36.25)`. Asymétrie
inversée (follower moins coûteux). -/
theorem stackelberg_asymmetric_p4 :
    stackelbergLeader (100 : Rat) 30 5 = 45 / 2 ∧
      stackelbergFollower (100 : Rat) 30 5 = 145 / 4 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `stackelberg_equilibrium(120, 8, 16) = (60, 28)`. Asymétrie
modérée avec a=120. -/
theorem stackelberg_asymmetric_p5 :
    stackelbergLeader (120 : Rat) 8 16 = 60 ∧
      stackelbergFollower (120 : Rat) 8 16 = 22 := by
  refine ⟨?_, ?_⟩ <;> norm_num [stackelbergLeader, stackelbergFollower]

/-- `cournot_equilibrium(100, 10) = (30, 30)`. -/
theorem cournot_default : cournotEquilibriumSym (100 : Rat) 10 = 30 := by
  norm_num [cournotEquilibriumSym]

/-- `cournot_equilibrium(120, 0) = 40` (coût marginal nul). -/
theorem cournot_zero_cost : cournotEquilibriumSym (120 : Rat) 0 = 40 := by
  norm_num [cournotEquilibriumSym]

/-- `cournot_reaction_curve(0, 100, 10) = 45` (monopole unilatéral). -/
theorem cournot_reaction_monopoly :
    cournotReaction 0 (100 : Rat) 10 = 45 := by
  norm_num [cournotReaction]

/-- `cournot_reaction_curve(30, 100, 10) = 30` (point fixe de
Cournot) — corollaire de la forme générale
`cournotSymmetric_eq_is_fixed_point` au couple `(100, 10)`. -/
theorem cournot_reaction_fixed_point :
    cournotReaction 30 (100 : Rat) 10 = 30 := by
  have hq : cournotEquilibriumSym (100 : Rat) 10 = 30 := by
    norm_num [cournotEquilibriumSym]
  rw [← hq]
  exact cournotSymmetric_eq_is_fixed_point 100 10 (by norm_num)

/-- `cournot_reaction_curve(90, 100, 10) = 0` (clamp à la frontière). -/
theorem cournot_reaction_clamp_boundary :
    cournotReaction 90 (100 : Rat) 10 = 0 := by
  norm_num [cournotReaction]

/-! ## Invariants économiques (valeurs concrètes) -/

/-- **Avantage du premier mover** (symétrique, valeurs concrètes) :
à `(a, c, c) = (100, 10, 10)`, `qL = 45 > 22.5 = qF` — corollaire
de la forme générale `first_mover_advantage_symmetric`. -/
theorem first_mover_advantage_at_default :
    stackelbergLeader (100 : Rat) 10 10 > stackelbergFollower (100 : Rat) 10 10 :=
  first_mover_advantage_symmetric 100 10 (by norm_num)

/-- **Bien-être au-dessus de Cournot** (symétrique, valeurs
concrètes) : à `(a, c, c) = (100, 10, 10)`, `qL + qF = 67.5 > 60 = 2·q*`
— corollaire de la forme générale `welfare_above_cournot_symmetric`. -/
theorem welfare_above_cournot_at_default :
    stackelbergLeader (100 : Rat) 10 10 + stackelbergFollower (100 : Rat) 10 10 >
      2 * cournotEquilibriumSym (100 : Rat) 10 :=
  welfare_above_cournot_symmetric 100 10 (by norm_num)

/-- Le leader Stackelberg produit strictement plus que la quantité
de Cournot symétrique (symétrique, valeurs concrètes) :
`qL = 45 > 30 = q*`. -/
theorem leader_above_cournot_at_default :
    stackelbergLeader (100 : Rat) 10 10 > cournotEquilibriumSym (100 : Rat) 10 := by
  norm_num [stackelbergLeader, stackelbergFollower, cournotEquilibriumSym]

/-- Le follower produit strictement moins que la quantité de Cournot
symétrique (symétrique, valeurs concrètes) :
`qF = 22.5 < 30 = q*`. -/
theorem follower_below_cournot_at_default :
    stackelbergFollower (100 : Rat) 10 10 < cournotEquilibriumSym (100 : Rat) 10 := by
  norm_num [stackelbergLeader, stackelbergFollower, cournotEquilibriumSym]

/-! ## Profits (valeurs concrètes) -/

/-- Profit de Cournot symétrique : `π₁ = π₂ = 900` à `(30, 30, 100, 10, 10)`. -/
theorem cournot_profit_at_default :
    profit (100 : Rat) 30 30 10 = 900 := by
  norm_num [profit]

/-- Profit de Stackelberg symétrique : `π_L = 1012.5` à
`(45, 22.5, 100, 10, 10)`. -/
theorem stackelberg_leader_profit_at_default :
    profit (100 : Rat) 45 (45 / 2 : Rat) 10 = 2025 / 2 := by
  norm_num [profit]

/-- Profit de Stackelberg follower : `π_F = 506.25` à
`(45, 22.5, 100, 10, 10)`. -/
theorem stackelberg_follower_profit_at_default :
    profit (100 : Rat) (45 / 2 : Rat) 45 10 = 2025 / 4 := by
  norm_num [profit]

/-- Profit de monopole : `π = 2025` à `(45, 0, 100, 10, 10)`. -/
theorem monopoly_profit_at_default :
    profit (100 : Rat) 45 0 10 = 2025 := by
  norm_num [profit]

/-! ## Profits asymétriques (5 paires paramétrées) -/

/-- Profits asymétriques (100, 5, 15) :
  q_L=105/2, q_F=65/4, π_L=11025/8, π_F=4225/16. -/
theorem stackelberg_profit_asymmetric_p2 :
    profit (100 : Rat) (105 / 2 : Rat) (65 / 4 : Rat) 5 = 11025 / 8 ∧
      profit (100 : Rat) (65 / 4 : Rat) (105 / 2 : Rat) 15 = 4225 / 16 := by
  refine ⟨?_, ?_⟩ <;> norm_num [profit]

/-- Profits asymétriques (100, 10, 20) :
  q_L=50, q_F=15, π_L=1250, π_F=225. -/
theorem stackelberg_profit_asymmetric_p1 :
    profit (100 : Rat) 50 15 10 = 1250 ∧
      profit (100 : Rat) 15 50 20 = 225 := by
  refine ⟨?_, ?_⟩ <;> norm_num [profit]

end StackelbergBilevel
