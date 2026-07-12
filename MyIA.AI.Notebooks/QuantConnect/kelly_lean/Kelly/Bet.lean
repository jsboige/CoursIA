import Mathlib

/-!
# Kelly.Bet — pari de Bernoulli, fraction misée, multiplicateurs de richesse

Un **pari de Bernoulli** (le cadre canonique du critère de Kelly) : avec probabilité
`p` on gagne et on reçoit `b` fois la mise `f` (cote nette `b`), avec probabilité
`q = 1 − p` on perd la mise. La richesse relative après le pari vaut :
- **`1 + b·f`** en cas de gain (capital + profit `b·f`),
- **`1 − f`** en cas de perte (capital − mise `f`).

La **fraction misée** `f` vit dans l'intervalle ouvert `(−1/b, 1)` : en deçà les deux
multiplicateurs sont strictement positifs (le log-croissance est défini). Une fraction
négative = pari *contre* le joueur (short), `f = 0` = rien parier.

Ce module pose le modèle. La fraction optimale `f*` et le théorème phare vivent dans
`Kelly.lean`. Voir l'issue #4052.
-/

namespace KellyLean

open Real

/-- Un pari de Bernoulli paramétré par sa probabilité de gain `p` et sa cote nette `b`. -/
structure Bet where
  /-- Probabilité de gain, strictement entre 0 et 1. -/
  p : ℝ
  hp_pos : 0 < p
  hp_lt_one : p < 1
  /-- Cote nette : profit `b` par unité misée en cas de gain, `b > 0`. -/
  b : ℝ
  hb_pos : 0 < b

/-- Probabilité de perte, `q = 1 − p`. -/
def q (β : Bet) : ℝ := 1 - β.p

/-- La probabilité de perte est strictement positive (car `p < 1`). -/
lemma q_pos (β : Bet) : 0 < q β := by unfold q; linarith [β.hp_lt_one]

/-- La probabilité de perte est strictement inférieure à 1 (car `p > 0`). -/
lemma q_lt_one (β : Bet) : q β < 1 := by unfold q; linarith [β.hp_pos]

/-- Probabilités somment à 1 : `p + q = 1`. -/
lemma pq_add_eq_one (β : Bet) : β.p + q β = 1 := by unfold q; ring

/-- Multiplicateur de richesse en cas de **gain** : `1 + b·f` (capital + profit `b·f`). -/
def winWealth (β : Bet) (f : ℝ) : ℝ := 1 + β.b * f

-- Multiplicateur de richesse en cas de **perte** : `1 − f` (capital − mise `f`).
-- Le corps ne dépend pas de la cote `β.b` (perdre sa mise est universel), mais `β`
-- est gardé en paramètre pour la symétrie d'API avec `winWealth`. L'option silences
-- le linter `unusedVariables` (intentionnel : API symétrique).
set_option linter.unusedVariables false in
def loseWealth (β : Bet) (f : ℝ) : ℝ := 1 - f

/-- La cote nette vérifie `b + 1 > 0` (utile pour les domaines). -/
lemma b_add_one_pos (β : Bet) : 0 < β.b + 1 := by linarith [β.hb_pos]

/-- `winWealth` est strictement positif sur la zone admissible `f > −1/b`. -/
lemma winWealth_pos (β : Bet) (f : ℝ) (hf : -1 / β.b < f) : 0 < winWealth β f := by
  unfold winWealth
  rw [div_lt_iff₀ β.hb_pos] at hf
  linarith [mul_comm β.b f]

/-- `loseWealth` est strictement positif sur la zone admissible `f < 1`. -/
lemma loseWealth_pos (β : Bet) (f : ℝ) (hf : f < 1) : 0 < loseWealth β f := by
  unfold loseWealth; linarith

/-- **Zone admissible** d'une fraction `f` : les deux multiplicateurs sont strictement
    positifs, i.e. `f ∈ (−1/b, 1)`. Le log-croissance y est défini. -/
def Feasible (β : Bet) (f : ℝ) : Prop := -1 / β.b < f ∧ f < 1

/-- Toute fraction admissible rend `winWealth` strictement positif. -/
lemma winWealth_pos_of_feasible (β : Bet) (f : ℝ) (hf : Feasible β f) :
    0 < winWealth β f :=
  winWealth_pos β f hf.1

/-- Toute fraction admissible rend `loseWealth` strictement positif. -/
lemma loseWealth_pos_of_feasible (β : Bet) (f : ℝ) (hf : Feasible β f) :
    0 < loseWealth β f :=
  loseWealth_pos β f hf.2

end KellyLean
