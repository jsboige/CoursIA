import Mathlib
import Kelly.Bet
import Kelly.Growth
import Kelly.Kelly

/-!
# Kelly.Fractional — inégalité fondamentale du *fractional Kelly*

La fraction de Kelly `f* = (b·p − q)/b` maximise le taux de croissance espéré
`g(f) = p·log(1 + b·f) + q·log(1 − f)`. Ce module prouve l'**inégalité du
*fractional Kelly*** : pour `c ∈ [0, 1]`, miser la fraction `c·f*` ne surpasse
jamais la fraction optimale complète :

    growth(c·f*) ≤ growth(f*)     (avec égalité ssi c = 1)

C'est la **justification formelle du *demi-Kelly*** (c = 1/2) et, plus
généralement, de toutes les stratégies de *position sizing* qui réduisent la
fraction optimale pour sacrifier de la log-croissance en échange d'une
volatilité moindre (cf. Thorp, *The Kelly Criterion in Blackjack, Sports
Betting, and the Stock Market* ; voir aussi le carnet compagnon
`Kelly_companion-Fractional-Python.ipynb` qui **mesure** ce compromis).

## Stratégie de preuve

On n'invoque **pas** la concavité de `growth` (la stratégie est contournée dans
`Kelly.lean` lui-même — cf. commentaire `Growth.lean:22`). On montre
directement que `c·f*` reste dans la **zone admissible** `(−1/b, 1)` dès que
`f*` l'est, puis on applique le **théorème phare** `kelly_optimal` :

1. `c·f* ∈ [0, f*]` quand `f* ≥ 0` (et `c·f* ∈ [f*, 0]` quand `f* < 0`),
   mais dans les deux cas `c·f*` est sandwiché dans `(−1/b, 1)`.
2. `kelly_optimal β (c·f*)` (qui s'applique à **toute** fraction admissible)
   donne alors directement `growth(c·f*) ≤ growth(f*)`.

L'égalité en `c = 1` est triviale (`1·f* = f*`). L'inégalité stricte pour
`c < 1` et `f* ≠ 0` (pari à edge non nul) suit de `kelly_unique` — la
même logique, avec la version stricte du théorème phare.

Référence : voir l'issue #19516 (plan de croissance #16231).
-/

namespace KellyLean

open Real

/-- La fraction `c·f*` (c ∈ [0, 1]) reste dans la **zone admissible** `(−1/b, 1)`
    dès que `f*` lui-même y est. Le cas `f* < 0` est plus subtil : on a alors
    `c·f* ∈ [f*, 0]`, mais le minorant `f* > −1/b` (f* admissible) reste
    protecteur. -/
lemma fractional_feasible (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Feasible β (c * kellyFrac β) := by
  obtain ⟨hfs_left, hfs_right⟩ := kellyFrac_feasible β
  refine ⟨?_, ?_⟩
  · -- -1/b < c·f*
    -- Cas c = 0 : c·f* = 0 > -1/b (b > 0).
    -- Cas c > 0 : on multiplie hfs_left par c ; puis -c/b ≥ -1/b (c ≤ 1, b > 0).
    rcases eq_or_lt_of_le hc0 with rfl | hc0_pos
    · -- c = 0 : c·f* = 0 > -1/b (b > 0)
      positivity
    · -- hfs_left : -1/b < f* ; hc0_pos : 0 < c ; donc c·f* > c·(-1/b) = -c/b
      have h1 : c * (-(1 / β.b)) < c * kellyFrac β :=
        mul_lt_mul_of_pos_left hfs_left hc0_pos
      -- -c/b ≥ -1/b (puisque c ≤ 1 et b > 0)
      have h2 : -(1 / β.b) ≤ c * (-(1 / β.b)) := by
        rw [neg_mul]
        exact neg_le_neg_iff.mpr (mul_le_mul_of_nonneg_right hc1 (one_div_nonneg.mpr β.hb_pos.le))
      linarith
  · -- c·f* < 1
    -- Cas c = 0 : 0 < 1 trivialement.
    -- Cas c > 0 : c·f* < c·1 = c ≤ 1.
    rcases eq_or_lt_of_le hc0 with rfl | hc0_pos
    · simp
    · have h1 : c * kellyFrac β < c * 1 :=
        mul_lt_mul_of_pos_left hfs_right hc0_pos
      linarith [hc1]

/-- **Inégalité fondamentale du *fractional Kelly*** : pour `c ∈ [0, 1]`,
    `growth(c·f*) ≤ growth(f*)`. C'est la justification formelle du
    *demi-Kelly* : miser une fraction `c` de la fraction optimale `f*` ne
    surpasse jamais la mise optimale complète. Suit de `kelly_optimal`
    appliqué à `c·f*` (admissible par `fractional_feasible`). -/
theorem growth_fractional_le (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    growth β (c * kellyFrac β) ≤ growth β (kellyFrac β) :=
  kelly_optimal β (c * kellyFrac β) (fractional_feasible β c hc0 hc1)

/-- **Égalité en c = 1** : la fraction `1·f*` redonne `f*`, donc même
    croissance. C'est la borne supérieure de `growth_fractional_le` (atteinte
    en `c = 1`). -/
theorem growth_fractional_eq_one (β : Bet) :
    growth β (1 * kellyFrac β) = growth β (kellyFrac β) := by
  simp

/-- **Inégalité stricte pour c < 1 et pari à edge non nul** : si `c ∈ [0, 1)`
    et `f* ≠ 0` (le pari a un avantage), alors `growth(c·f*) < growth(f*)`.
    Suit de `kelly_unique` appliqué à `c·f*` (admissible et distinct de `f*`).
    Cas particulier du *demi-Kelly* (c = 1/2) sur un pari favorable. -/
theorem growth_fractional_lt (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hclt : c < 1)
    (hfne : kellyFrac β ≠ 0) :
    growth β (c * kellyFrac β) < growth β (kellyFrac β) := by
  -- c·f* est admissible (hclt.le = hc1)
  have hfeas := fractional_feasible β c hc0 hclt.le
  -- c·f* ≠ f* : si c·f* = f* alors (1-c)·f* = 0
  have hne : c * kellyFrac β ≠ kellyFrac β := by
    intro heq
    have hmul : (1 - c) * kellyFrac β = 0 := by
      have h1 := congrArg (fun x => x - kellyFrac β) heq
      linarith
    rcases mul_eq_zero.mp hmul with h1 | h2
    · linarith
    · exact hfne h2
  exact kelly_unique β (c * kellyFrac β) hfeas hne

end KellyLean