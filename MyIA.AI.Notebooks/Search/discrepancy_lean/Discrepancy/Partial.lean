import Discrepancy.Kernel

/-!
# b2 — Invariant de coloration partielle

Deuxième boute du grignotage de `BeckFialaClassic` (`disc ≤ 2k−1`), voir
`FORMAL_STATUS.md`. L'algorithme de Beck-Fiala maintient une coloration
**partielle** `c₀ : α → ℚ` : des variables déjà figées à `±1`, des variables
flottantes strictement intérieures (`|c₀ x| < 1`). Tant qu'une ligne est
dangereuse, la phase b1 la déplace le long d'une direction de noyau qui
préserve sa somme **exactement**. Quand une ligne cesse d'être dangereuse
(≤ `k` flottants), elle n'est plus protégée : chacun de ses flottants restants
sera figé à `±1` lors des phases ultérieures, et chaque figage déplace la
somme de **moins de `2`** (d'un point strictement intérieur vers un extrême).

Ce fichier isole le contenu arithmétique de cet invariant :

* `sum_sub_eq_sum_inter` — la dérive d'une somme se concentre sur les
  flottants : deux états qui coïncident hors de `Y` ne différent sur `S` que
  par `S ∩ Y` ;
* `natAbs_le_of_cast_abs_lt` — l'arrondi entier : une somme entière
  strictement inférieure à `2k` en valeur absolue est au plus `2k−1` ;
* `frozen_line_sum_le` — l'invariant assemblé : une ligne figée avec `≤ k`
  flottants, partie d'une somme exactement préservée (nulle), termine à
  `|∑ c| ≤ 2k−1` sous la coloration finale `±1`.

C'est la moitié « analyse » de la borne finale ; la moitié « algorithme »
(progrès b3, terminaison b4) l'assemble avec b1.
-/

namespace Discrepancy

section PartialInvariant

variable {α : Type*} [DecidableEq α]

/-- La dérive d'une somme se concentre sur les flottants : si deux états
`c₀`, `c₁` coïncident hors de `Y`, la différence de leurs sommes sur `S`
est la somme de leurs différences sur `S ∩ Y`. -/
private theorem sum_sub_eq_sum_inter (c₀ c₁ : α → ℚ) (S Y : Finset α)
    (hout : ∀ x ∈ S, x ∉ Y → c₀ x = c₁ x) :
    (∑ x ∈ S, c₀ x) - (∑ x ∈ S, c₁ x) = ∑ x ∈ S ∩ Y, (c₀ x - c₁ x) := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.sum_subset (Finset.inter_subset_left)
    (fun x hxS hxno => sub_eq_zero.mpr
      (hout x hxS (fun hY => hxno (Finset.mem_inter.mpr ⟨hxS, hY⟩))))).symm

/-- **L'arrondi entier de b2** : une somme entière de valeur absolue
strictement inférieure à `2k` est au plus `2k−1`. C'est ce pas qui convertit
la dérive stricte « moins de `2` par flottant » en borne impaire finale. -/
theorem natAbs_le_of_cast_abs_lt (z : ℤ) (k : ℕ)
    (h : |(z : ℚ)| < ((2 * k : ℕ) : ℚ)) : z.natAbs ≤ 2 * k - 1 := by
  have h1 : |z| < ((2 * k : ℕ) : ℤ) := by exact_mod_cast h
  have h2 : -((2 * k : ℕ) : ℤ) < z ∧ z < ((2 * k : ℕ) : ℤ) := abs_lt.mp h1
  omega

/-- **b2 — l'invariant d'une ligne figée.** Soit `S` une ligne qui cesse
d'être dangereuse avec `Y ⊆ S` flottants (`|Y| ≤ k`), partie d'un état
partiel `c₀` à somme exactement préservée (nulle) et flottants strictement
intérieurs. Alors sous toute coloration finale `c` en `±1` qui coïncide avec
`c₀` hors de `Y`, la somme colorée de `S` vérifie `|∑_{x∈S} c x| ≤ 2k−1`.

Chaque flottant dérive de moins de `2` (strictement intérieur vers un
extrême), la somme entière dérive donc de moins de `2k`, et l'arrondi
(`natAbs_le_of_cast_abs_lt`) donne `2k−1`. C'est la garantie que les lignes
quittées par l'algorithme ne dépassent jamais la borne de Beck-Fiala. -/
theorem frozen_line_sum_le (c₀ : α → ℚ) (c : α → ℤ) (Y S : Finset α) (k : ℕ)
    (hY : Y ⊆ S) (hkY : Y.card ≤ k) (hcolor : IsColoring c)
    (hfloat : ∀ x ∈ Y, |c₀ x| < 1)
    (hsum₀ : ∑ x ∈ S, c₀ x = 0)
    (hout : ∀ x ∈ S, x ∉ Y → (c x : ℚ) = c₀ x) :
    (∑ x ∈ S, c x).natAbs ≤ 2 * k - 1 := by
  classical
  have hSIY : S ∩ Y = Y := Finset.inter_eq_right.mpr hY
  have hcast : (∑ x ∈ S, (c x : ℚ)) = ((∑ x ∈ S, c x : ℤ) : ℚ) := by
    rw [← Int.cast_sum]
  rcases Y.eq_empty_or_nonempty with hY0 | hYne
  · -- Cas vide : la somme finale est exactement la somme initiale, nulle.
    have hnull : (∑ x ∈ S, (c x : ℚ)) = 0 := by
      rw [← hsum₀]
      exact Finset.sum_congr rfl fun x hx =>
        hout x hx (by simp [hY0])
    rw [hcast] at hnull
    have hz0 : ∑ x ∈ S, c x = 0 := by
      simpa using Int.cast_eq_zero.mp hnull
    simp only [hz0, Int.natAbs_zero]
    omega
  · -- Cas non vide : dérive stricte < 2·|Y| ≤ 2k, puis arrondi entier.
    have hterm : ∀ x ∈ Y, |((c x : ℚ) - c₀ x)| < (2 : ℚ) := by
      intro x hx
      have hbound := abs_lt.mp (hfloat x hx)
      rcases hcolor x with hc | hc
      · rw [hc]
        rw [abs_lt]
        constructor <;> (push_cast; linarith)
      · rw [hc]
        rw [abs_lt]
        constructor <;> (push_cast; linarith)
    have hstep1 : (∑ x ∈ S, (c x : ℚ)) - (∑ x ∈ S, c₀ x)
        = ∑ x ∈ Y, ((c x : ℚ) - c₀ x) := by
      rw [sum_sub_eq_sum_inter (fun x => (c x : ℚ)) c₀ S Y hout, hSIY]
    have habs : |∑ x ∈ Y, ((c x : ℚ) - c₀ x)|
        ≤ ∑ x ∈ Y, |((c x : ℚ) - c₀ x)| :=
      Finset.abs_sum_le_sum_abs (fun x => ((c x : ℚ) - c₀ x)) Y
    have hltsum : (∑ x ∈ Y, |((c x : ℚ) - c₀ x)|) < (∑ x ∈ Y, ((2 : ℚ))) := by
      obtain ⟨x₀, hx₀⟩ := hYne
      exact Finset.sum_lt_sum (fun x hx => le_of_lt (hterm x hx))
        ⟨x₀, hx₀, hterm x₀ hx₀⟩
    have hconst : (∑ x ∈ Y, ((2 : ℚ))) = ((2 * Y.card : ℕ) : ℚ) := by
      rw [Finset.sum_const]
      push_cast
      ring
    have hdrift : |(∑ x ∈ S, (c x : ℚ))| < ((2 * Y.card : ℕ) : ℚ) := by
      have hz : (∑ x ∈ S, (c x : ℚ))
          = (∑ x ∈ S, (c x : ℚ)) - (∑ x ∈ S, c₀ x) := by
        rw [hsum₀, sub_zero]
      rw [hz, hstep1]
      calc |∑ x ∈ Y, ((c x : ℚ) - c₀ x)|
          ≤ (∑ x ∈ Y, |((c x : ℚ) - c₀ x)|) := habs
        _ < ((2 * Y.card : ℕ) : ℚ) := by rw [hconst] at hltsum; exact hltsum
    have hcard : ((2 * Y.card : ℕ) : ℚ) ≤ ((2 * k : ℕ) : ℚ) := by
      have h2k : (2 * Y.card : ℕ) ≤ 2 * k := by omega
      exact_mod_cast h2k
    have hzz : |((∑ x ∈ S, c x : ℤ) : ℚ)| < ((2 * k : ℕ) : ℚ) := by
      rw [← hcast]
      exact lt_of_lt_of_le hdrift hcard
    exact natAbs_le_of_cast_abs_lt (∑ x ∈ S, c x) k hzz

end PartialInvariant

end Discrepancy
