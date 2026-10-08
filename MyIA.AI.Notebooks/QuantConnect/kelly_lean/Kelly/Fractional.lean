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
  have hfeas := kellyFrac_feasible β
  -- hfeas.1 : -1/β.b < kellyFrac β
  -- hfeas.2 : kellyFrac β < 1
  refine ⟨?_, ?_⟩
  · -- -1/β.b < c·f* : on exploite `kellyFrac_feasible.1` (hfeas.1) + c ∈ [0, 1].
    -- Cas c = 0 : c·f* = 0 > -1/b. Cas c > 0, c < 1 : c·(-1/b) > -1/b
    -- (c < 1, b > 0) puis c·f* > c·(-1/b) (hfeas.1, c > 0). Cas c = 1 :
    -- c·f* = f* > -1/b (hfeas.1). Évite la voie `mul_assoc` du commit cassé
    -- (Lean 4.33 a changé le comportement des rewrites sur les produits à 3
    -- facteurs).
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · rw [zero_mul]
      -- But : -1 / β.b < 0.  Suit de 0 < 1 / β.b (one_div_pos de β.hb_pos).
      have hpos : 0 < 1 / β.b := one_div_pos.mpr β.hb_pos
      linarith [show (1 / β.b) + (-1 / β.b) = 0 from by ring, hpos]
    · -- 0 < c
      rcases lt_or_ge c 1 with hclt | hcge
      · -- 0 < c < 1
        have hm1 : -1 / β.b < c * (-1 / β.b) := by
          have h1 : -1 * (1 / β.b) = -1 / β.b := by ring
          have h2 : c * (-1 / β.b) = -c * (1 / β.b) := by ring
          have h3 : -1 * (1 / β.b) < -c * (1 / β.b) :=
            mul_lt_mul_of_pos_right (by linarith : -1 < -c) (one_div_pos.mpr β.hb_pos)
          linarith [h1, h2, h3]
        have hm2 : c * (-1 / β.b) < c * kellyFrac β := mul_lt_mul_of_pos_left hfeas.1 hcpos
        linarith [hm1, hm2]
      · -- 0 < c et c ≥ 1 et c ≤ 1, donc c = 1
        have h1 : c = 1 := le_antisymm hc1 hcge
        rw [h1, one_mul]
        exact hfeas.1
  · -- c·f* < 1 : symétriquement, on exploite `kellyFrac_feasible.2` (hfeas.2).
    -- Cas c = 0 : c·f* = 0 < 1. Cas c > 0 : c·f* < c·1 = c ≤ 1
    -- (hfeas.2, c > 0 puis hc1).
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · simp  -- c = 0
    · have hmul : c * kellyFrac β < c * 1 := mul_lt_mul_of_pos_left hfeas.2 hcpos
      linarith [hmul, hc1]

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