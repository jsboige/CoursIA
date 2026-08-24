/-
Charpente de correction de l'algorithme de Kuhn-Munkres (issue #12598).

Kuhn (1955) d'apres Konig et Egervary ; Munkres (1957) pour la preuve du
temps fortement polynomial. L'implémentation pedagogique complete vit dans
le notebook GT-27 (arbre hongrois BFS, resserrement dual) ; ce fichier
formalise la structure de correction :

1. le **graphe d'egalite** — les paires ou la contrainte duale est saturee ;
2. l'**invariant de sortie** — une affectation dont toutes les aretes sont
   dans le graphe d'egalite, avec un dual realisable, est optimale
   (assemblage de Duality + Optimality) ;
3. le **resserrement hongrois** — l'operation qui deplace les potentiels
   (`u += δ` sur un ensemble de lignes, `v -= δ` sur un ensemble de
   colonnes) preserve la realisabilite duale, sous l'hypothese que `δ`
   n'excede la marge d'aucune arete sortante (lignes serrees x colonnes
   non serrees). C'est exactement le `delta = min marge` de l'algorithme.

Hors scope (deliberement, cf issue) : la preuve de terminaison et la
complexite O(n³) — la correction structurelle par dualite suffit.
-/
import Mathlib
import Assignment.Optimality

namespace Assignment

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ)

/-- Arete d'egalite : la paire `(i, j)` sature la contrainte duale
(`u i + v j = C i j`). Le graphe d'egalite est l'union de ces aretes ;
l'arbre hongrois de l'algorithme y vit exclusivement. -/
def EqEdge (i j : Fin n) : Prop := u i + v j = C i j

/-- **Invariant de sortie de Kuhn-Munkres** : si le potentiel final est
dual-realisable et si toutes les aretes de `σ` sont des aretes d'egalite,
alors `σ` est optimale. C'est le certificat produit en terminant : la
methode hongroise ne demande a aucune etape de faire confiance a un
solveur exterieur. -/
theorem kuhn_munkres_correct (σ : Equiv.Perm (Fin n)) (h : DualFeasible C u v)
    (heq : ∀ i, EqEdge C u v i (σ i)) : IsOptimal C σ :=
  optimality_of_zero_gap C u v σ h (dualValue_eq_of_edges C u v σ heq)

/-- **Le resserrement hongrois preserve la realisabilite duale.**

Etant donnes un ensemble de lignes `S` et de colonnes `T` (l'arbre hongrois
et ses colonnes decouvertes), un `δ ≥ 0` majore par la marge de toute arete
sortante (`i ∈ S`, `j ∉ T`) produit un nouveau couple dual encore
realisable : les aretes internes `(S, T)` voient leurs deux contributions
bouger en sens opposes, les aretes entrantes `(∉ S, T)` ne font que
descendre, et les aretes sortantes `(S, ∉ T)` restent sous leur cout par
hypothese sur `δ`. Le `δ = min marge` de l'algorithme satisfait
l'hypothese par definition du minimum. -/
theorem dualFeasible_tighten (S T : Finset (Fin n)) (h : DualFeasible C u v)
    (δ : ℤ) (hδ : 0 ≤ δ)
    (hmargin : ∀ i ∈ S, ∀ j ∉ T, δ ≤ C i j - (u i + v j)) :
    DualFeasible C (fun i => if i ∈ S then u i + δ else u i)
                 (fun j => if j ∈ T then v j - δ else v j) := by
  intro i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ T
    · -- arete interne : les deux contributions se compensent
      simp only [if_pos hi, if_pos hj]
      have h₀ : u i + v j ≤ C i j := h i j
      linarith
    · -- arete sortante : bornee par l'hypothese de marge sur delta
      simp only [if_pos hi, if_neg hj]
      have h₀ : u i + v j ≤ C i j := h i j
      have h₁ : δ ≤ C i j - (u i + v j) := hmargin i hi j hj
      linarith
  · by_cases hj : j ∈ T
    · -- arete entrante : la contribution de v ne fait que descendre
      simp only [if_neg hi, if_pos hj]
      have h₀ : u i + v j ≤ C i j := h i j
      linarith
    · -- arete non touchee
      simp only [if_neg hi, if_neg hj]
      exact h i j

end Assignment
