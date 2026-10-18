/-
Module StackelbergBilevel (organe 2 de #21221) : duopole de Stackelberg en
quantites, demande lineaire p = a - qL - qF (pente b = 1), couts marginaux
constants, tout sur Q.

Ancrages : les valeurs fermees ci-dessous sont celles des tests Python de la
serie (`MyIA.AI.Notebooks/GameTheory/tests/test_stackelberg.py`) — reaction du
suiveur au monopole 22.5, equilibre (45, 22.5) pour (a, c) = (100, 10), prix
32.5, profit du leader 1012.5, comparaison Cournot (30, 30) avec profit 900.

Methodes : uniquement la completion du carre, sans analyse — les profits sont
des polynomes de degre 2 en les quantites. Le niveau bas (suiveur) est demontre
dans `profitF_carre` / `reaction_argmax`, le niveau haut (leader) dans
`bilevel_carre` / `bilevel_optimum`, la valeur d'engagement dans
`engagement_bat_cournot`.
-/
import Mathlib.Tactic

/-! ## Definitions

Demande lineaire `p = a - Q` (pente `b = 1`, convention de `test_stackelberg.py`),
profits a couts marginaux constants, courbe de reaction du suiveur.
-/

namespace StackelbergBilevel

/-- Profit du suiveur : recette `(a - qL - qF) * qF` moins cout `c * qF`. -/
def profitF (a c qL qF : ℚ) : ℚ := (a - qL - qF) * qF - c * qF

/-- Profit du leader : recette `(a - qL - qF) * qL` moins cout `c * qL`. -/
def profitL (a c qL qF : ℚ) : ℚ := (a - qL - qF) * qL - c * qL

/-- Courbe de reaction du suiveur : `(a - c - qL) / 2`, meilleure reponse a la
quantite du leader. -/
def reaction (a c qL : ℚ) : ℚ := (a - c - qL) / 2

/-- Quantite de monopole `(a - c) / 2` : reaction face a un rival absent. -/
def monopole (a c : ℚ) : ℚ := (a - c) / 2

/-- Objectif bilevel du leader : son profit CONTRE la meilleure reponse du
suiveur. Forme close du probleme de la eq. 1 de Dai et al. (ICLR 2026) — le
niveau bas (argmax du suiveur) est resolu exactement ici, la ou le notebook 19b
l'approche par un suiveur PPO entrainable. -/
def bilevel (a c qL : ℚ) : ℚ := profitL a c qL (reaction a c qL)

/-! ## Niveau bas : le suiveur joue sa meilleure reponse

Le profit du suiveur se complete en carre autour de sa reaction.
-/

/-- Completion du carre (niveau bas) : le profit du suiveur vaut `br ^ 2` moins
un carre, nul exactement en `br = reaction a c qL`. -/
theorem profitF_carre (a c qL qF : ℚ) :
    profitF a c qL qF = (reaction a c qL) ^ 2 - (qF - reaction a c qL) ^ 2 := by
  unfold profitF reaction
  ring

/-- Le suiveur ne fait jamais mieux que sa courbe de reaction. -/
theorem reaction_optimale (a c qL qF : ℚ) :
    profitF a c qL qF ≤ (reaction a c qL) ^ 2 := by
  rw [profitF_carre]
  linarith [sq_nonneg (qF - reaction a c qL)]

/-- La reaction est l'UNIQUE maximisateur du profit du suiveur. -/
theorem reaction_argmax (a c qL qF : ℚ) :
    profitF a c qL qF = (reaction a c qL) ^ 2 ↔ qF = reaction a c qL := by
  rw [profitF_carre]
  constructor
  · intro h
    have h2 : (qF - reaction a c qL) ^ 2 = 0 := by linarith
    have h3 := sq_eq_zero_iff.mp h2
    linarith
  · intro h
    rw [h, sub_self]
    norm_num

/-! ## Niveau haut : le leader optimise contre la reaction

La fonction objectif bilevel du leader se complete en carre autour du monopole.
-/

/-- Completion du carre (niveau haut) : `bilevel` est maximal en `monopole a c`,
de valeur `(a - c) ^ 2 / 8`. -/
theorem bilevel_carre (a c qL : ℚ) :
    bilevel a c qL = (a - c) ^ 2 / 8 - (qL - (a - c) / 2) ^ 2 / 2 := by
  unfold bilevel profitL reaction
  ring

/-- Borne superieure : le leader bilevel n'excede pas `(a - c) ^ 2 / 8`. -/
theorem bilevel_borne (a c qL : ℚ) :
    bilevel a c qL ≤ (a - c) ^ 2 / 8 := by
  rw [bilevel_carre]
  linarith [sq_nonneg (qL - (a - c) / 2)]

/-- Paradoxe de Stackelberg : le maximisateur du leader est la quantite de
monopole, et le suiveur produit la moitie. -/
theorem bilevel_optimum (a c : ℚ) :
    bilevel a c (monopole a c) = (a - c) ^ 2 / 8 := by
  unfold monopole
  rw [bilevel_carre, sub_self]
  ring

/-! ## Ancrages numeriques (a, c) = (100, 10) — invariants de test_stackelberg.py
-/

/-- `test_stackelberg.py` : reaction du suiveur au monopole = 22.5. -/
theorem instance_reaction : reaction 100 10 45 = 45 / 2 := by norm_num [reaction]

/-- `test_stackelberg.py` : le monopole vaut 45. -/
theorem instance_monopole : monopole 100 10 = 45 := by norm_num [monopole]

/-- `test_stackelberg.py` : prix d'equilibre 32.5. -/
theorem instance_prix : (100 : ℚ) - 45 - 45 / 2 = 65 / 2 := by norm_num

/-- `test_stackelberg.py` : profit du leader a l'equilibre 1012.5. -/
theorem instance_profitL : profitL 100 10 45 (45 / 2) = 2025 / 2 := by
  norm_num [profitL]

/-- Profit du suiveur a l'equilibre : 506.25 (le carre de la reaction). -/
theorem instance_profitF : profitF 100 10 45 (45 / 2) = 2025 / 4 := by
  norm_num [profitF]

/-- La valeur bilevel au monopole est le profit du leader : 1012.5. -/
theorem instance_bilevel : bilevel 100 10 45 = 2025 / 2 := by
  unfold bilevel
  rw [instance_reaction]
  norm_num [profitL]

/-! ## Comparaison Cournot : la valeur de l'engagement
-/

/-- Quantite de Cournot symetrique `(a - c) / 3`. -/
def cournot (a c : ℚ) : ℚ := (a - c) / 3

/-- `test_stackelberg.py` : Cournot symetrique (30, 30). -/
theorem instance_cournot : cournot 100 10 = 30 := by norm_num [cournot]

/-- `test_stackelberg.py` : profit Cournot 900 chacun. -/
theorem instance_profit_cournot : profitL 100 10 30 30 = 900 := by
  norm_num [profitL]

/-- Valeur de l'engagement : le leader Stackelberg `(a - c) ^ 2 / 8` domine le
duopole symetrique de Cournot `(a - c) ^ 2 / 9`. C'est l'argument du notebook
19b en forme close — annoncer sa morphologie d'abord (co-designer, niveau haut)
vaut mieux que repondre symetriquement. -/
theorem engagement_bat_cournot (a c : ℚ) :
    (a - c) ^ 2 / 9 ≤ (a - c) ^ 2 / 8 := by
  have h : (0 : ℚ) ≤ (a - c) ^ 2 := sq_nonneg (a - c)
  field_simp
  nlinarith [h]

end StackelbergBilevel
