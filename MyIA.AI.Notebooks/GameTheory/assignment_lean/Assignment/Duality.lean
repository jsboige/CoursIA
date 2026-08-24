/-
Potentiels duaux du probleme d'affectation (issue #12598).

Le primal LP minimise `∑ i j, C i j * x i j` sous contraintes de ligne et
de colonne ; son dual maximise `∑ i, u i + ∑ j, v j` sous la contrainte
`u i + v j ≤ C i j` pour toute paire. Ces potentiels sont exactement les
labels de l'algorithme de Kuhn-Munkres : la realisabilite duale est
l'invariant maintenu de bout en bout, et le resserrement hongrois
(cf KuhnMunkres.lean) ne le casse jamais.

Le resultat central du fichier est la dualite faible : toute affectation
(realisable) a une valeur au moins egale a celle de tout couple dual
realisable. C'est la borne qui, atteinte avec egalite, certifie
l'optimalite (cf Optimality.lean).
-/
import Mathlib
import Assignment.Definitions

namespace Assignment

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ)

/-- Realisabilite duale : `u i + v j ≤ C i j` pour toute paire (i, j). -/
def DualFeasible : Prop := ∀ i j, u i + v j ≤ C i j

/-- Valeur duale : somme de tous les potentiels. -/
def dualValue : ℤ := (∑ i, u i) + (∑ j, v j)

/-- **Dualite faible** : toute affectation est au-dessus de la valeur duale.

Le calcul reindexe `∑ j, v j` le long de la permutation `σ`
(chaque colonne est visitee exactement une fois par un matching parfait),
puis majore terme a terme par realisabilite duale. C'est la premiere moitie
du certificat d'optimalite de Kuhn-Munkres. -/
theorem weak_duality (h : DualFeasible C u v) (σ : Equiv.Perm (Fin n)) :
    dualValue u v ≤ value C σ := by
  have hreindex : (∑ i, v (σ i : Fin n)) = ∑ j, v j :=
    Equiv.sum_comp σ (fun j => v j)
  calc dualValue u v
      = ∑ i, (u i + v (σ i : Fin n)) := by
        rw [Finset.sum_add_distrib, hreindex]
        rfl
    _ ≤ ∑ i, C i (σ i) := Finset.sum_le_sum fun i _ => h i (σ i)
    _ = value C σ := rfl

end Assignment
