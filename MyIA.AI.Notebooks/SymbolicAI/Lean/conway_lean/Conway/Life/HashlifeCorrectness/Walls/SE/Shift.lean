/-  # HashlifeCorrectness.Walls.SE.Shift

Caracterisation par quadrant + lemme de decalage SE.

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Walls.SE.Basic

namespace Conway
namespace Life

open MacroCell

/-! ### Étape 4 (préparation) — caractérisation par quadrant du supernœud résultat

Le supernœud `node R1 R2 R4 R5` (niveau `k+1`) est caractérisé quadrant par
quadrant : sur chaque quadrant de `[0, 2·2^k)²`, sa grille vaut l'évolution
`2^(k-1)` du nœud de recombinaison correspondant, au point re-translaté que
produit `centralCorrect_mem_shift`. Les trois autres quadrants sont exclus par
leurs propres bornes (les conjonctions de `centralCorrect_mem_shift`), via
`hA : 2^(k-1+1) = 2^k` (qui exige `1 ≤ k`). -/


/-- **P4.4 SE-quadrant shift lemma (factorisé, c.552 — rebase de #6944 sur main post-#6955).**
    Symétrique au `p4_ne_shift_lemma` pour l'offset SE OUTER `(2^k + 2^k, 2^k + 2^k) = (2^(k+1), 2^(k+1))`.
    Convention uniforme avec NE/NW (c.8122) : voir `p4_sw_shift_lemma` pour le
    contexte. Sorry-free. -/
theorem p4_se_shift_lemma
    (k : Nat) (hk1 : 1 ≤ k)
    (r1 r2 r4 r5 : MacroCell)
    (hr1_l : r1.level = k) (hr2_l : r2.level = k)
    (hr4_l : r4.level = k) (hr5_l : r5.level = k)
    (hr1_w : r1.wf = true) (hr2_w : r2.wf = true)
    (hr4_w : r4.wf = true) (hr5_w : r5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int) :
    p ∈ (hashlifeResultAux ((k - 1) + 2) (node r1 r2 r4 r5)).toGrid
          ((2^k + (2^k : Int), 2^k + (2^k : Int))) ↔
      isAlive (evolve (2^(k - 1)) ((node r1 r2 r4 r5).toGrid (0, 0)))
        (p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int),
         p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)) = true ∧
      ((2^k + (2^k : Int))) ≤ p.1 ∧
        p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
      ((2^k + (2^k : Int))) ≤ p.2 ∧
        p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) := by
  have hcc : centralCorrect (node r1 r2 r4 r5) (k - 1) :=
    p4_wave2_ih_step k hk1 r1 r2 r4 r5
      hr1_l hr2_l hr4_l hr5_l hr1_w hr2_w hr4_w hr5_w ih
  exact centralCorrect_mem_shift (node r1 r2 r4 r5) (k - 1)
    (2^k + (2^k : Int)) (2^k + (2^k : Int)) p hcc

end Life
end Conway
