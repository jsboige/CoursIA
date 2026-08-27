/-
Certificat d'optimalite par dualite (issue #12598).

Le pont entre la machinerie duale (Duality.lean) et la question algorithmique
(notion d'optimalite de Definitions.lean) : un couple dual realisable dont la
valeur egale celle d'une affectation `σ` prouve que `σ` est optimale — gap de
dualite nul, le theoreme que le notebook GT-27 verifie numeriquement
(triple test, section 3) devient une preuve verifiee par le noyau Lean.

La seconde voie vers le gap nul : si toutes les aretes du matching sont des
aretes d'egalite (`u i + v (σ i) = C i (σ i)`), les valeurs primale et duale
coincident automatiquement — c'est l'invariant de sortie de l'algorithme
de Kuhn-Munkres (cf KuhnMunkres.lean).
-/
import Mathlib
import Assignment.Duality

namespace Assignment

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ) (σ : Equiv.Perm (Fin n))

/-- Si toutes les aretes du matching sont des aretes d'egalite, la valeur
duale egale la valeur primale (reindexation de `∑ v` le long de `σ`). -/
theorem dualValue_eq_of_edges (h : ∀ i, u i + v (σ i : Fin n) = C i (σ i)) :
    dualValue u v = value C σ := by
  have hreindex : (∑ i, v (σ i : Fin n)) = ∑ j, v j :=
    Equiv.sum_comp σ (fun j => v j)
  calc dualValue u v
      = ∑ i, (u i + v (σ i : Fin n)) := by
        rw [Finset.sum_add_distrib, hreindex]
        rfl
    _ = ∑ i, C i (σ i) := Finset.sum_congr rfl fun i _ => h i
    _ = value C σ := rfl

/-- **Certificat d'optimalite a gap nul** : dual realisable + valeur duale
egale a la valeur de `σ` ⇒ `σ` est optimale. C'est la forme exacte du
certificat que la methode hongroise produit en terminant. -/
theorem optimality_of_zero_gap (h : DualFeasible C u v)
    (heq : dualValue u v = value C σ) : IsOptimal C σ := by
  intro τ
  rw [← heq]
  exact weak_duality C u v h τ

end Assignment
