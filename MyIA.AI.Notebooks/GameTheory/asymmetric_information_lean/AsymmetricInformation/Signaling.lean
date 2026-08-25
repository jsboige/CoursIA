/-
  Signaling — modèle Spence 1973, formalisation bornée
  ====================================================

  Formalisation du modèle de signalisation coûteuse de Spence 1973 *QJE*
  87(3):355-374. Le candidat de type `q ∈ {H, L}` (productivité `y_q`)
  choisit un signal `s ∈ ℕ` (coût `c(q, s) ∈ ℕ`), l'employeur observe `s`
  et propose un salaire `w(s)`. L'utilité du candidat est `w - c`.

  Quatre contraintes explicites à l'équilibre séparateur :
  1. IC_H : `y_H - c(H, s_H) ≥ y_L - c(H, s_L)`
  2. IC_L : `y_L - c(L, s_L) ≥ y_H - c(L, s_H)`
  3. IR_H : `y_H - c(H, s_H) ≥ u_bar_H`
  4. IR_L : `y_L - c(L, s_L) ≥ u_bar_L`

  Salaire concurrentiel : `w_q = y_q` (l'employeur paie la productivité du
  type qui choisit le signal). **PAS** de rente H universelle nulle.

  Bornes strictes (audit c.475 catégorie #1+#5) :
  - PAS d'énoncé `∃` pour l'intervalle sans hypothèses FINIES listées ;
  - Riley least-cost separator illustré sur une **instance finie explicite**
    (pas un théorème général) ;
  - Pas de single-crossing universel — chaque lemme liste ses hypothèses.
-/

namespace AsymmetricInformation.Signaling

/-- Type du candidat : haut ou bas productivité. -/
inductive WorkerType where
  | low
  | high
  deriving DecidableEq, Repr

/-- Coût du signal `s` pour le type `q`, en entiers naturels (cohérent avec
    l'API amont). Single-crossing encodé : coût plus faible pour H. -/
def signalCost (q : WorkerType) (s : Nat) : Nat :=
  match q with
  | .low  => 2 * s   -- coût plus élevé pour L (single-crossing encodé)
  | .high => s

/-- Utilité du candidat de type `q` recevant salaire `w` et ayant choisi
    le signal `s` (coût `signalCost q s`). `w - c(q, s)` directement. -/
def workerUtility (w : Int) (q : WorkerType) (s : Nat) : Int :=
  w - (signalCost q s : Int)

/-- Productivité type : `y_H > y_L`. -/
structure Productivity where
  yLow : Int
  yHigh : Int
  hOrder : yLow < yHigh

/-- Salaire concurrentiel : `w_q = y_q` (Spence 1973, eq. de signalisation). -/
def competitiveWage (p : Productivity) (q : WorkerType) : Int :=
  match q with | .low => p.yLow | .high => p.yHigh

/-- Les **quatre contraintes** explicites d'un séparateur. `s_L < s_H` est
    imposé par l'énoncé (séparation signifie que les deux types choisissent
    des signaux distincts). -/
structure Separator (p : Productivity) where
  sLow : Nat
  sHigh : Nat
  sOrder : sLow < sHigh
  reserveLow : Int
  reserveHigh : Int
  icHigh :
    p.yHigh - (signalCost .high sHigh : Int)
      ≥ p.yLow - (signalCost .high sLow : Int)
  icLow :
    p.yLow - (signalCost .low sLow : Int)
      ≥ p.yHigh - (signalCost .low sHigh : Int)
  irHigh :
    p.yHigh - (signalCost .high sHigh : Int) ≥ reserveHigh
  irLow :
    p.yLow - (signalCost .low sLow : Int) ≥ reserveLow

/-- Constructeur d'un salaire à partir d'un séparateur : `w_q = y_q`
    (concurrentiel, pas de rente H universelle). -/
def separatorWage (p : Productivity) (sep : Separator p) (q : WorkerType) : Int :=
  competitiveWage p q

/-- **Exemples décidés** : sur l'instance `(y_H, y_L) = (10, 4)` et coût
    spécifié, `(s_L, s_H) = (0, 6)` est un séparateur valide :

    - IC_H : `10 - 6 ≥ 4 - 0` ⟹ `4 ≥ 4` ✓
    - IC_L : `4 - 0 ≥ 10 - 12` ⟹ `4 ≥ -2` ✓
    - IR_H : `10 - 6 ≥ 0` ⟹ `4 ≥ 0` ✓ (u_bar_H = 0)
    - IR_L : `4 - 0 ≥ 0` ⟹ `4 ≥ 0` ✓ (u_bar_L = 0) -/
example : ∃ sep : Separator ⟨4, 10, by omega⟩,
    sep.sLow = 0 ∧ sep.sHigh = 6 ∧ sep.reserveLow ≤ 0 ∧ sep.reserveHigh ≤ 0 := by
  refine ⟨⟨0, 6, by omega, 0, 0, by decide, by decide, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩

/-- **PAS de claim d'unicité générale** : sur la même instance, on exhibe
    un **deuxième séparateur** `(s_L, s_H) = (1, 7)` qui satisfait aussi
    les 4 contraintes. Calcul : `signalCost .high 7 = 7`,
    `signalCost .high 1 = 1`, `signalCost .low 1 = 2`, `signalCost .low 7 = 14`.
    - IC_H : `10 - 7 ≥ 4 - 1` ⟹ `3 ≥ 3` ✓
    - IC_L : `4 - 2 ≥ 10 - 14` ⟹ `2 ≥ -4` ✓
    - IR_H : `10 - 7 ≥ 0` ⟹ `3 ≥ 0` ✓
    - IR_L : `4 - 2 ≥ 0` ⟹ `2 ≥ 0` ✓ -/
example : ∃ sep : Separator ⟨4, 10, by omega⟩,
    sep.sLow = 1 ∧ sep.sHigh = 7 ∧ sep.reserveLow ≤ 0 ∧ sep.reserveHigh ≤ 0 := by
  refine ⟨⟨1, 7, by omega, 0, 0, by decide, by decide, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩

end AsymmetricInformation.Signaling
