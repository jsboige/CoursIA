import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Hasse calculée par le noyau : compter les points d'une courbe elliptique sur F_p

Pendant kernel du notebook `01-corps-finis-borne-hasse.ipynb` (série
*Serre 100*, EPIC #16334 — voie de graduation « pendants kernel »).
Le notebook *mesure* la borne de Hasse en Python ; ce module la fait
*vérifier par le noyau Lean* sur les mêmes courbes, et démontre
l'identité qui relie la trace de Frobenius au caractère quadratique
(exercice 2 du notebook).

Plan, en miroir du notebook :

1. **Définitions** (`pointsAffines`, `nombrePoints`, `traceFrobenius`,
   `lisse`) — sur `ZMod p` muni de sa structure d'anneau : compter
   n'exige pas la primalité, seule l'identité du §3 l'exige.
2. **Vérifications par le noyau** : la table du notebook (cellule « La
   trace de Frobenius », courbe `y² = x³ + 2x + 3`) est reproduite
   exactement, et la borne `t² ≤ 4p` est vérifiée sur **toutes** les
   courbes lisses de `F_5` et `F_7` — le « Toutes sous la borne : True »
   du notebook, mais prouvé et non plus observé.
3. **L'identité trace/caractère** : `t = -∑ x, χ (x³ + ax + b)`, où `χ`
   est le caractère quadratique de `ZMod p` — l'exercice 2 du notebook,
   démontré pour tout `p` premier impair.
-/

set_option autoImplicit false

namespace Serre100

/-! ## Définitions — le vocabulaire du notebook, en Lean

Un point affine de la courbe `y² = x³ + ax + b` sur `ZMod p` est un couple
vérifiant l'équation ; le point à l'infini compte pour un. La trace de
Frobenius est `t = p + 1 - #E`, la non-singularité est `4a³ + 27b² ≠ 0`.
-/

/-- Points affines de `y² = x³ + ax + b` sur `ZMod p` (sans le point à
l'infini). Défini sur l'anneau `ZMod p` : le comptage ne demande pas que
`p` soit premier. -/
def pointsAffines (p : ℕ) [NeZero p] (a b : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun xy => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1 + b)

/-- Nombre de points de la courbe, point à l'infini inclus (notebook,
`nombre_points`). -/
def nombrePoints (p : ℕ) [NeZero p] (a b : ZMod p) : ℕ :=
  1 + (pointsAffines p a b).card

/-- Trace de Frobenius `t = p + 1 - #E` (notebook, `trace_frobenius`). -/
def traceFrobenius (p : ℕ) [NeZero p] (a b : ZMod p) : ℤ :=
  (p : ℤ) + 1 - (nombrePoints p a b : ℤ)

/-- Non-singularité : `4a³ + 27b² ≠ 0` dans `ZMod p` (notebook,
`est_lisse`). -/
@[reducible] def Lisse (p : ℕ) [NeZero p] (a b : ZMod p) : Prop :=
  4 * a ^ 3 + 27 * b ^ 2 ≠ 0

/-! ## La borne de Hasse, vérifiée par le noyau

Le notebook observe (`Toutes sous la borne : True`, 1701 courbes
mesurées) ; le noyau démontre ici les mêmes comptages, exactement.
La forme entière de la borne `|t| ≤ 2√p` est `t² ≤ 4p`.
-/

/-- La courbe-phare du notebook (`a = 2`, `b = 3`, `p = 7`) : 5 points
affines, 6 avec le point à l'infini — cellule « compter les points ». -/
example : (pointsAffines 7 2 3).card = 5 := by decide

example : nombrePoints 7 2 3 = 6 := by decide

/-- La table du notebook (cellule « La trace de Frobenius »), courbe
`y² = x³ + 2x + 3`, reproduite ligne par ligne. -/
example : traceFrobenius 5 2 3 = -1 := by decide
example : traceFrobenius 7 2 3 = 2 := by decide
example : traceFrobenius 11 2 3 = -1 := by decide
example : traceFrobenius 13 2 3 = -4 := by decide
example : traceFrobenius 17 2 3 = -4 := by decide
example : traceFrobenius 19 2 3 = 0 := by decide
example : traceFrobenius 23 2 3 = 0 := by decide
example : traceFrobenius 29 2 3 = -6 := by decide

/-- La borne de Hasse, forme entière `t² ≤ 4p`, sur **toutes** les
courbes lisses de `F_5`. -/
example : ∀ a b : ZMod 5, Lisse 5 a b →
    (traceFrobenius 5 a b) ^ 2 ≤ (4 * 5 : ℤ) := by decide

/-- La borne de Hasse sur **toutes** les courbes lisses de `F_7`. -/
example : ∀ a b : ZMod 7, Lisse 7 a b →
    (traceFrobenius 7 a b) ^ 2 ≤ (4 * 7 : ℤ) := by decide

/-- La borne de Hasse sur **toutes** les courbes lisses de `F_11`. -/
example : ∀ a b : ZMod 11, Lisse 11 a b →
    (traceFrobenius 11 a b) ^ 2 ≤ (4 * 11 : ℤ) := by decide

/-! ## L'identité trace/caractère — l'exercice 2 du notebook, démontré

Le notebook demande (exercice 2) de vérifier que
`∑ x, χ (x³ + ax + b) = -t`, où `χ` est le symbole de Legendre. On le
démontre ici pour tout `p` premier impair, en trois temps : chaque
fibre du carré compte `1 + χ v` solutions ; sommer sur `x` compte les
points affines ; réarranger donne la trace.
-/

section Identite

open Finset

variable {p : ℕ} [NeZero p] [Fact p.Prime]

omit [NeZero p] in
private theorem deux_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h2le : 2 ≤ p := hp.two_le
  have hd : p ∣ (2 : ℕ) := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd two_pos hd
  omega

/-- Fibre du carré en caractéristique impaire : pour tout `v`, le nombre
de `y` tels que `y² = v` vaut exactement `1 + χ v` — les trois régimes
(`v = 0` : une solution ; carré non nul : deux ; non-carré : aucune). -/
theorem card_fibre_carre (hp2 : p ≠ 2) (v : ZMod p) :
    ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)).card : ℤ)
      = 1 + quadraticChar (ZMod p) v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    have hsingleton :
        (Finset.univ.filter (fun y : ZMod p => y ^ 2 = 0)) = {(0 : ZMod p)} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨by simp, ?_⟩
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      exact sq_eq_zero_iff.1 hy
    rw [hsingleton, Finset.card_singleton, quadraticChar_zero]
    norm_num
  · by_cases hsq : IsSquare v
    · obtain ⟨w, hw⟩ := hsq
      have hwm : w * w = v := hw.symm
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hwm
        exact hv hwm.symm
      have hwneg : w ≠ -w := by
        intro h
        apply hw0
        have h2 : (2 : ZMod p) * w = 0 := by
          linear_combination h
        exact ((mul_eq_zero.1 h2).resolve_left (deux_ne_zero_zmod hp2))
      have hsol :
          (Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)) = insert w {-w} := by
        ext y
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hy
          have hprod : (y - w) * (y + w) = 0 := by
            linear_combination hy - hwm
          rcases mul_eq_zero.1 hprod with h | h
          · exact Or.inl (sub_eq_zero.1 h)
          · exact Or.inr (eq_neg_iff_add_eq_zero.2 h)
        · rintro (rfl | rfl)
          · rw [← hwm]; ring
          · rw [← hwm]; ring
      have hcard : (insert w {-w} : Finset (ZMod p)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        intro hmem
        exact hwneg (by simpa using hmem)
      have hchi : quadraticChar (ZMod p) v = 1 := by
        rw [← hwm, ← pow_two]
        exact quadraticChar_sq_one' hw0
      rw [hsol, hcard, hchi]
      norm_num
    · have hempty : (Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)) = ∅ := by
        ext y
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro hy
        exact hsq ⟨y, by simpa [pow_two] using hy.symm⟩
      have hchi : quadraticChar (ZMod p) v = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 hsq
      rw [hempty, Finset.card_empty, hchi]
      norm_num

/-- Comptage par fibres : les points affines se comptent en sommant sur
`x` le nombre de `y` dans la fibre du carré. -/
theorem card_pointsAffines_eq_sum (a b : ZMod p) :
    (pointsAffines p a b).card
      = ∑ x : ZMod p, (Finset.univ.filter
          (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card := by
  unfold pointsAffines
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  show ∑ y ∈ (Finset.univ : Finset (ZMod p)),
      (if y ^ 2 = x ^ 3 + a * x + b then (1 : ℕ) else 0)
    = (Finset.univ.filter
          (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]

/-- L'identité de l'exercice 2 du notebook : la trace de Frobenius est
l'opposée de la somme du caractère quadratique sur les abscisses,
`∑ x, χ (x³ + ax + b) = -t`, pour toute courbe (même singulière —
l'identité est purement comptable). -/
theorem trace_eg_moins_somme_caractere (hp2 : p ≠ 2) (a b : ZMod p) :
    traceFrobenius p a b
      = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
  have hfib : ∀ x : ZMod p,
      ((Finset.univ.filter
        (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card : ℤ)
        = 1 + quadraticChar (ZMod p) (x ^ 3 + a * x + b) :=
    fun x => card_fibre_carre hp2 _
  have hcard : ((pointsAffines p a b).card : ℤ)
      = (Fintype.card (ZMod p) : ℤ)
        + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
    have h1 : ∑ x : ZMod p, ((1 : ℤ) + quadraticChar (ZMod p) (x ^ 3 + a * x + b))
        = ((pointsAffines p a b).card : ℤ) := by
      rw [card_pointsAffines_eq_sum, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ => (hfib x).symm
    have hsu : (Fintype.card (ZMod p) : ℤ)
        = ∑ x : ZMod p, (1 : ℤ) := by
      simp [Finset.sum_const, Finset.card_univ]
    calc ((pointsAffines p a b).card : ℤ)
        = ∑ x : ZMod p, ((1 : ℤ) + quadraticChar (ZMod p) (x ^ 3 + a * x + b)) :=
          h1.symm
      _ = (Fintype.card (ZMod p) : ℤ)
            + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
          rw [Finset.sum_add_distrib, ← hsu]
  rw [traceFrobenius, nombrePoints]
  push_cast
  rw [hcard, ZMod.card]
  ring

end Identite

end Serre100
