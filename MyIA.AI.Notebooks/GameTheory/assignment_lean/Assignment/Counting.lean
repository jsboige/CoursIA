/-
Compter les couplages parfaits : le permanent comme pont (issue #21958, Pli 6 de #19898).

La dualite (Duality.lean) exhibe un couplage optimal en temps polynomial ;
compter TOUS les couplages parfaits releve d'une autre classe (#P-dur,
famille 113 d'openai/math) et le polytope du couplage n'admet aucune
remontee semidefinie compacte (famille 126). Ce fichier formalise le pont
entre les deux mondes : le permanent de Mathlib
(Mathlib.LinearAlgebra.Matrix.Permanent) de la matrice d'adjacence 0/1
egale le cardinal des couplages parfaits du graphe biparti.

Organ-first (#13564) : `Matrix.permanent` est l'organe natif ; ce fichier
ne redefinit rien, il prouve la correspondance permanent <-> couplages.
-/
import Mathlib

namespace Assignment

open Matrix

variable {n : ℕ}

/-- Matrice d'adjacence entiere d'un graphe biparti sur `Fin n × Fin n` :
`1` si l'arete existe, `0` sinon. -/
def adjMatrix (B : Matrix (Fin n) (Fin n) Bool) : Matrix (Fin n) (Fin n) ℕ :=
  B.map fun b => if b then 1 else 0

/-- L'ensemble des couplages parfaits d'un graphe biparti : les permutations
dont toutes les aretes ligne `i` vers colonne `σ i` sont presentes. -/
def perfectMatchingSet (B : Matrix (Fin n) (Fin n) Bool) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ i, B i (σ i)

/-- Un produit de indicateurs 0/1 vaut 1 exactement quand toutes les aretes
sont presentes, 0 sinon. Lemme technique du pont. -/
theorem prod_ite_eq_one_iff (B : Matrix (Fin n) (Fin n) Bool)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, (if B i (σ i) then (1:ℕ) else 0)) = if ∀ i, B i (σ i) then 1 else 0 := by
  by_cases h : ∀ i, B i (σ i)
  · simp [h]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : (if B i (σ i) then (1:ℕ) else 0) = 0 := by
      cases hBi : B i (σ i) with
      | false => simp
      | true => exact absurd hBi hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- **Le pont** : le permanent (Mathlib) de la matrice d'adjacence 0/1 egale
le nombre de couplages parfaits du graphe biparti. C'est la formalisation
locale du point d'entree des familles 113 (FPRAS pour compter) et 126
(cloture SDP) d'openai/math, citees avec leur statut epistemique dans le
carnet ANALYSE-12. -/
theorem card_eq_permanent (B : Matrix (Fin n) (Fin n) Bool) :
    (perfectMatchingSet B).card = (adjMatrix B).permanent := by
  classical
  calc (perfectMatchingSet B).card
      = ∑ σ : Equiv.Perm (Fin n), (if ∀ i, B i (σ i) then (1:ℕ) else 0) := by
        simp only [perfectMatchingSet]
        exact Finset.card_filter _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, (if B i (σ i) then (1:ℕ) else 0) :=
        Finset.sum_congr rfl fun σ _ => (prod_ite_eq_one_iff B σ).symm
    _ = ((adjMatrix B)ᵀ).permanent := rfl
    _ = (adjMatrix B).permanent := Matrix.permanent_transpose _

/-- Graphe biparti complet : toutes les permutations sont couvrantes, le
cardinal est le factoriel. -/
theorem card_eq_factorial (B : Matrix (Fin n) (Fin n) Bool) (h : ∀ i j, B i j) :
    (perfectMatchingSet B).card
      = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
  simp [perfectMatchingSet, h]

/-- Corollaire du pont sur le graphe complet : le permanent de la matrice
tout-un est le factoriel de n (temoin croise avec `Fintype.card_perm`). -/
theorem permanent_complete_eq_factorial (B : Matrix (Fin n) (Fin n) Bool)
    (h : ∀ i j, B i j) :
    (adjMatrix B).permanent = Nat.factorial (Fintype.card (Fin n)) := by
  rw [← card_eq_permanent B, card_eq_factorial B h, Finset.card_univ,
    Fintype.card_perm]

end Assignment
