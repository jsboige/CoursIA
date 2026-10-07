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
  have hb := β.hb_pos
  have hkf : kellyFrac β * β.b = β.b * β.p - (1 - β.p) := by
    simp [kellyFrac, q]; field_simp [hb.ne']
  refine ⟨?_, ?_⟩
  · -- -1/b < c·f*  ⟺  -1 < c·f*·b  (b > 0), puis hkf ramène à de l'arithmétique
    -- polynomiale close par nlinarith. Évite le case split c=0/c>0 qui cassait
    -- sous Lean 4.33 (Decidable / mul_lt_mul_of_pos_left / linarith).
    rw [div_lt_iff₀ hb, ← mul_assoc, mul_assoc c (kellyFrac β) β.b, hkf]
    nlinarith [β.hp_pos, β.hp_lt_one, hb, hc0, hc1]
  · -- c·f* < 1  ⟺  1 - c·f* > 0. On développe 1 - c·f* = c·(1-f*) + (1-c),
    -- et (1-f*) > 0 vient de `kellyFrac_feasible`. nlinarith ferme.
    have h1f : 1 - kellyFrac β = (1 - β.p) * (β.b + 1) / β.b := by
      unfold kellyFrac q; field_simp [hb.ne']; ring
    have h1f_pos : 0 < 1 - kellyFrac β := by
      rw [h1f]
      positivity
    have eq1 : 1 - c * kellyFrac β = c * (1 - kellyFrac β) + (1 - c) := by ring
    rw [eq1]
    nlinarith [h1f_pos, hc0, hc1]

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