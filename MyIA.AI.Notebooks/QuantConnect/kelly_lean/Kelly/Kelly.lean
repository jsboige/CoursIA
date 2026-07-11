import Mathlib
import Kelly.Bet
import Kelly.Growth

/-!
# Kelly.Kelly — optimalité de la fraction `f*` (critère de Kelly)

Le **théorème de Kelly** : la fraction optimale à miser sur un pari de Bernoulli
(probabilité de gain `p`, cote nette `b`) est

    f* = (b·p − q) / b        (q = 1 − p)

qui **maximise de façon unique** le taux de croissance espéré `g(f) = p·log(1+bf) +
q·log(1−f)`. Tout sur-pari (`f > f*`) ou sous-pari (`f < f*`) est strictement
sous-optimal.

## Stratégie de preuve

On évite la concavité abstraite et on prouve `g(f) ≤ g(f*)` **directement** via la
tangente du logarithme en 1, `log t ≤ t − 1` (avec égalité ssi `t = 1`). En écrivant

    g(f) − g(f*) = p · log((1+bf)/(1+bf*)) + q · log((1−f)/(1−f*))

et en appliquant `log t ≤ t − 1` à chaque rapport, on obtient

    g(f) − g(f*) ≤ (f − f*) · [p·b/(1+bf*) − q/(1−f*)] = (f − f*) · g'(f*).

Or `g'(f*) = 0` (condition du premier ordre, vérifiée par calcul). Donc
`g(f) ≤ g(f*)`. L'unicité suit de la version stricte `log t < t − 1` pour `t ≠ 1` :
si `f ≠ f*`, les rapports diffèrent de `1`, donc les inégalités sont strictes, et
`g(f) < g(f*)`.

Référence : J. L. Kelly Jr., *A New Interpretation of Information Rate*, BSTT (1956).
Voir l'issue #4052.
-/

namespace KellyLean

open Real

/-- La **fraction de Kelly** `f* = (b·p − q)/b` (la mise optimale par unité de capital). -/
noncomputable def kellyFrac (β : Bet) : ℝ := (β.b * β.p - q β) / β.b

/-- La fraction de Kelly vit dans la zone admissible `(−1/b, 1)` : les deux
    multiplicateurs de richesse en `f*` sont strictement positifs. -/
lemma kellyFrac_feasible (β : Bet) : Feasible β (kellyFrac β) := by
  have hb := β.hb_pos
  -- kellyFrac β * β.b = β.b·p − (1 − p)  (on multiplie par b > 0)
  have hkf : kellyFrac β * β.b = β.b * β.p - (1 - β.p) := by
    simp [kellyFrac, q]; field_simp [hb.ne']
  refine ⟨?_, ?_⟩
  · -- −1/b < f*  ⟺  −1 < f*·b  (b > 0)
    rw [div_lt_iff₀ hb, hkf]
    nlinarith [β.hp_pos, hb]
  · -- f* < 1  ⟺  1 − f* = (1 − p)·(b + 1)/b > 0
    have h1f : 1 - kellyFrac β = (1 - β.p) * (β.b + 1) / β.b := by
      unfold kellyFrac q; field_simp [β.hb_pos.ne']; ring
    have hpos : 0 < 1 - kellyFrac β := by
      rw [h1f]
      exact div_pos (mul_pos (by linarith [β.hp_lt_one]) (b_add_one_pos β)) β.hb_pos
    linarith

/-- Multiplicateur de gain évalué en `f*` : `winWealth β f* = p · (b + 1)`. -/
lemma winWealth_kelly (β : Bet) : winWealth β (kellyFrac β) = β.p * (β.b + 1) := by
  unfold winWealth kellyFrac q; field_simp [β.hb_pos.ne']; ring

/-- Multiplicateur de perte évalué en `f*` : `loseWealth β f* = q · (b + 1) / b`. -/
lemma loseWealth_kelly (β : Bet) : loseWealth β (kellyFrac β) = q β * (β.b + 1) / β.b := by
  unfold loseWealth kellyFrac q; field_simp [β.hb_pos.ne']; ring

/-- **Condition du premier ordre** : la pente du log-croissance s'annule en `f*`,
    `g'(f*) = growthGrad β f* = 0`. -/
lemma growthGrad_kelly_zero (β : Bet) : growthGrad β (kellyFrac β) = 0 := by
  have hq : q β ≠ 0 := (q_pos β).ne'
  have hbo : β.b + 1 ≠ 0 := (b_add_one_pos β).ne'
  have hpb : β.p * (β.b + 1) ≠ 0 := mul_ne_zero β.hp_pos.ne' hbo
  rw [growthGrad, winWealth_kelly, loseWealth_kelly]
  field_simp [β.hp_pos.ne', hq, β.hb_pos.ne', hbo, hpb]
  ring

/-- **Majoration clé** : pour toute fraction admissible `f`,
    `g(f) − g(f*) ≤ (f − f*) · g'(f*)`. Suit de `log t ≤ t − 1` appliqué aux deux
    rapports. -/
lemma growth_diff_le (β : Bet) (f : ℝ) (hf : Feasible β f) :
    growth β f - growth β (kellyFrac β) ≤ (f - kellyFrac β) * growthGrad β (kellyFrac β) := by
  have hfs := kellyFrac_feasible β
  set fstar := kellyFrac β with hfstar
  have hwp := winWealth_pos_of_feasible β f hf
  have hwl := loseWealth_pos_of_feasible β f hf
  have hwsp := winWealth_pos_of_feasible β fstar hfs
  have hwlp := loseWealth_pos_of_feasible β fstar hfs
  -- g(f) − g(f*) = p·log(Ww_f/Ww_*) + q·log(Wl_f/Wl_*)
  have h1 : log (winWealth β f / winWealth β fstar) =
      log (winWealth β f) - log (winWealth β fstar) := Real.log_div hwp.ne' hwsp.ne'
  have h2 : log (loseWealth β f / loseWealth β fstar) =
      log (loseWealth β f) - log (loseWealth β fstar) := Real.log_div hwl.ne' hwlp.ne'
  have hdiffeq : growth β f - growth β fstar =
      β.p * log (winWealth β f / winWealth β fstar) +
        q β * log (loseWealth β f / loseWealth β fstar) := by
    unfold growth; rw [h1, h2]; ring
  -- borne chaque rapport via log t ≤ t − 1 (en fait : égalité algébrique du majorant)
  have hwin_bound : log (winWealth β f / winWealth β fstar) ≤
      (f - fstar) * (β.b / winWealth β fstar) := by
    refine (log_le_sub_one_of_pos (div_pos hwp hwsp)).trans ?_
    simp only [winWealth] at hwsp ⊢
    field_simp [hwsp.ne']
    linarith
  have hlose_bound : log (loseWealth β f / loseWealth β fstar) ≤
      (f - fstar) * (-1 / loseWealth β fstar) := by
    refine (log_le_sub_one_of_pos (div_pos hwl hwlp)).trans ?_
    simp only [loseWealth] at hwlp ⊢
    field_simp [hwlp.ne']
    linarith
  -- combine (p,q > 0 préservent les inégalités)
  calc growth β f - growth β fstar
      = β.p * log (winWealth β f / winWealth β fstar) +
          q β * log (loseWealth β f / loseWealth β fstar) := hdiffeq
    _ ≤ β.p * ((f - fstar) * (β.b / winWealth β fstar)) +
          q β * ((f - fstar) * (-1 / loseWealth β fstar)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hwin_bound β.hp_pos.le
        · exact mul_le_mul_of_nonneg_left hlose_bound (q_pos β).le
    _ = (f - fstar) * growthGrad β fstar := by
        rw [growthGrad]; field_simp [hwsp.ne', hwlp.ne']; ring

/-- **Théorème de Kelly** (maximiseur) : `f*` maximise le taux de croissance espéré.
    Pour toute fraction admissible `f`, `g(f) ≤ g(f*)`. -/
theorem kelly_optimal (β : Bet) (f : ℝ) (hf : Feasible β f) :
    growth β f ≤ growth β (kellyFrac β) := by
  have hbound := growth_diff_le β f hf
  rw [growthGrad_kelly_zero, mul_zero] at hbound
  linarith

/-- **Sur-pari et sous-pari strictement sous-optimaux** : si `f ≠ f*` est admissible,
    alors `g(f) < g(f*)` (unicité du maximiseur). Suit de `log t < t − 1` pour `t ≠ 1`. -/
theorem kelly_unique (β : Bet) (f : ℝ) (hf : Feasible β f) (hfne : f ≠ kellyFrac β) :
    growth β f < growth β (kellyFrac β) := by
  have hfs := kellyFrac_feasible β
  set fstar := kellyFrac β with hfstar
  have hwp := winWealth_pos_of_feasible β f hf
  have hwl := loseWealth_pos_of_feasible β f hf
  have hwsp := winWealth_pos_of_feasible β fstar hfs
  have hwlp := loseWealth_pos_of_feasible β fstar hfs
  -- f ≠ f* ⟹ les multiplicateurs de richesse diffèrent (1+b·_ et 1−_ sont injectifs)
  have hwin_inj : winWealth β f = winWealth β fstar → f = fstar := by
    intro h
    unfold winWealth at h
    have : β.b * f = β.b * fstar := by linarith
    exact mul_left_cancel₀ β.hb_pos.ne' this
  have hlose_inj : loseWealth β f = loseWealth β fstar → f = fstar := by
    intro h; unfold loseWealth at h; linarith
  have hwinne : winWealth β f / winWealth β fstar ≠ 1 := by
    intro heq
    apply hfne
    apply hwin_inj
    field_simp [hwsp.ne'] at heq
    exact heq
  have hlosene : loseWealth β f / loseWealth β fstar ≠ 1 := by
    intro heq
    apply hfne
    apply hlose_inj
    field_simp [hwlp.ne'] at heq
    exact heq
  -- versions strictes : log t < t − 1 pour t ≠ 1
  have h1 : log (winWealth β f / winWealth β fstar) =
      log (winWealth β f) - log (winWealth β fstar) := Real.log_div hwp.ne' hwsp.ne'
  have h2 : log (loseWealth β f / loseWealth β fstar) =
      log (loseWealth β f) - log (loseWealth β fstar) := Real.log_div hwl.ne' hwlp.ne'
  have hdiffeq : growth β f - growth β fstar =
      β.p * log (winWealth β f / winWealth β fstar) +
        q β * log (loseWealth β f / loseWealth β fstar) := by
    unfold growth; rw [h1, h2]; ring
  -- f ≠ f* ⟹ AU MOINS l'un des rapports diffère de 1 ; utilisons la borne stricte
  have hwin_strict : log (winWealth β f / winWealth β fstar) <
      (f - fstar) * (β.b / winWealth β fstar) := by
    refine (log_lt_sub_one_of_pos (div_pos hwp hwsp) hwinne).trans_le ?_
    simp only [winWealth] at hwsp ⊢
    field_simp [hwsp.ne']
    linarith
  have hlose_strict : log (loseWealth β f / loseWealth β fstar) <
      (f - fstar) * (-1 / loseWealth β fstar) := by
    refine (log_lt_sub_one_of_pos (div_pos hwl hwlp) hlosene).trans_le ?_
    simp only [loseWealth] at hwlp ⊢
    field_simp [hwlp.ne']
    linarith
  have hgrad0 : growthGrad β fstar = 0 := growthGrad_kelly_zero β
  have hdiff : growth β f - growth β fstar < 0 := by
    calc growth β f - growth β fstar
        = β.p * log (winWealth β f / winWealth β fstar) +
            q β * log (loseWealth β f / loseWealth β fstar) := hdiffeq
      _ < β.p * ((f - fstar) * (β.b / winWealth β fstar)) +
            q β * ((f - fstar) * (-1 / loseWealth β fstar)) := by
          refine add_lt_add ?_ ?_
          · exact mul_lt_mul_of_pos_left hwin_strict β.hp_pos
          · exact mul_lt_mul_of_pos_left hlose_strict (q_pos β)
      _ = (f - fstar) * growthGrad β fstar := by
          rw [growthGrad]; field_simp [hwsp.ne', hwlp.ne']; ring
      _ = 0 := by rw [hgrad0, mul_zero]
  linarith

/-! ## 8. Critère pratique : parier ssi l'edge est positif

La règle de décision opérationnelle du critère de Kelly : la fraction optimale
`f*` est **strictement positive exactement quand le pari est favorable**
(`b·p − q > 0`). Inversement, un pari défavorable (`b·p − q < 0`) donne `f* < 0` :
le maximiseur bascule côté short. Le cas neutre `b·p − q = 0` (pari actuariellement
équitable) donne `f* = 0` : ne rien parer est optimal. Cette équivalence de signe
est l'incarnation formelle de la prose de `Growth.lean` (§« edge » `g'(0) = b·p − q`).
-/

/-- **Fraction de Kelly positive ssi pari favorable** : `f* > 0` exactement quand
    l'« edge » `b·p − q` est strictement positif (le pari est avantageux, `b·p > q`).
    C'est le critère pratique de Kelly — ne miser côté long que si l'on a un
    avantage mathématique. Suit directement de `f* = (b·p − q)/b` avec `b > 0` :
    le signe de la fraction égale celui du numérateur. -/
theorem kellyFrac_pos_iff (β : Bet) :
    0 < kellyFrac β ↔ 0 < β.b * β.p - q β := by
  unfold kellyFrac
  rw [lt_div_iff₀ β.hb_pos, zero_mul]

/-- **Edge positif ssi Kelly positive** : le gradient du log-croissance en `f = 0`
    (l'« edge » `g'(0) = b·p − q`, cf `growthGrad_zero`) est strictement positif
    exactement quand la fraction optimale `f*` l'est. Concrétise formellement la
    règle de décision « miser ssi `g'(0) > 0` » : la pente initiale du log-croissance
    signe la direction de la mise optimale (long si positive, short si négative,
    flat si nulle). -/
theorem growthGrad_zero_pos_iff (β : Bet) :
    0 < growthGrad β 0 ↔ 0 < kellyFrac β := by
  rw [growthGrad_zero, kellyFrac_pos_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

/-- **Fraction de Kelly négative ssi pari défavorable** : `f* < 0` exactement quand
    l'« edge » `b·p − q` est strictement négatif (le pari est désavantageux, `b·p < q`).
    Le maximiseur bascule alors côté short. Formalise le second cas de la prose §8
    (« un pari défavorable donne `f* < 0` »). -/
theorem kellyFrac_neg_iff (β : Bet) :
    kellyFrac β < 0 ↔ β.b * β.p - q β < 0 := by
  unfold kellyFrac
  rw [div_lt_iff₀ β.hb_pos, zero_mul]

/-- **Edge négatif ssi Kelly négative** : la pente initiale `g'(0) = b·p − q` est
    strictement négative exactement quand `f* < 0`. La direction short est signée par
    la pente du log-croissance en l'origine. -/
theorem growthGrad_zero_neg_iff (β : Bet) :
    growthGrad β 0 < 0 ↔ kellyFrac β < 0 := by
  rw [growthGrad_zero, kellyFrac_neg_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

/-- **Fraction de Kelly nulle ssi pari équitable** : `f* = 0` exactement quand
    l'« edge » `b·p − q` est nul (pari actuariellement équitable, `b·p = q`).
    Ne rien miser est alors optimal. Formalise le cas neutre de la prose §8. -/
theorem kellyFrac_eq_zero_iff (β : Bet) :
    kellyFrac β = 0 ↔ β.b * β.p - q β = 0 := by
  unfold kellyFrac
  rw [div_eq_zero_iff, or_iff_left β.hb_pos.ne']

/-- **Edge nul siff Kelly nulle** : la pente initiale `g'(0)` est nulle exactement
    quand `f* = 0`. Le cas neutre où ne rien miser est optimal — frontière entre les
    régimes long et short. -/
theorem growthGrad_zero_eq_zero_iff (β : Bet) :
    growthGrad β 0 = 0 ↔ kellyFrac β = 0 := by
  rw [growthGrad_zero, kellyFrac_eq_zero_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

/-! ## 9. Capstone : la croissance optimale est nulle ssi le pari est équitable

Les régimes du §8 décrivent le **signe de la fraction optimale** `f*`. Cette section
en donne la **valeur de croissance** : comme `f*` maximise `g` et que `g(0) = 0`
(ne rien miser laisse le capital inchangé), l'optimum satisfait toujours
`g(f*) ≥ 0`. Il est **nul exactement au point neutre** `f* = 0` (pari actuariellement
équitable, `b·p = q`) ; dès qu'un edge existe (`f* ≠ 0`), l'optimum est **strictement
positif** — un pari à Kelly optimal ne détruit jamais le capital, et n'enrichit que
s'il y a avantage. Ce capstone boucle la formalisation du critère opérationnel :
`sign(f*) = sign(edge)` (§8) et `g(f*) = 0 ↔ f* = 0` (ici) — les deux faces d'un
même résultat.
-/

/-- **Croissance optimale nulle ssi pari équitable** : `g(f*) = 0` exactement quand
    `f* = 0`. Suit de `kelly_optimal` (qui donne `g(0) = 0 ≤ g(f*)` via `f = 0`
    admissible) et `kelly_unique` (qui donne `g(f*) > g(0) = 0` dès que `f* ≠ 0`).
    Capstone du critère opérationnel : la fraction nulle ne croît ni ne décroît, et
    tout edge non nul produit une croissance optimale strictement positive. -/
theorem kelly_growth_eq_zero_iff (β : Bet) :
    growth β (kellyFrac β) = 0 ↔ kellyFrac β = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- g(f*) = 0 mais f* ≠ 0 : kelly_unique donne g(0) < g(f*) = 0, contradiction
    by_contra hne
    have hfeas0 : Feasible β 0 := ⟨by rw [div_lt_iff₀ β.hb_pos]; linarith, by linarith⟩
    have hne' : (0 : ℝ) ≠ kellyFrac β := fun he => hne (Eq.symm he)
    have hu := kelly_unique β 0 hfeas0 hne'
    rw [growth_zero] at hu
    linarith
  · -- f* = 0 : alors g(f*) = g(0) = 0
    rw [h]; exact growth_zero β

end KellyLean
