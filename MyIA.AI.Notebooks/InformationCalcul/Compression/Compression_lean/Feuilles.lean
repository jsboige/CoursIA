/-
# Feuilles — profondeurs et substitution d'un poids (pli 5e de #18706)

Le théorème d'optimalité complet (le trie de Huffman réalise le coût
minimal parmi les arbres de mêmes feuilles) se prouve par induction sur le
nombre de symboles : marier les deux minima, résoudre le problème réduit,
développer. Le pas descendant de l'induction — tout arbre de coût minimal
porte ses deux minima en feuilles sœurs à profondeur maximale — exige de
parler de la profondeur d'une feuille donnée et de déplacer des poids. Ce
module pose les outils : `depthOf` (profondeur de la première feuille d'un
poids donné, parcours profondeur d'abord gauche), `maxDepth` (la hauteur),
et `swapW` (remplacer le poids de la première feuille de poids `x` par
`y`), avec ses trois invariants : le poids total paie exactement l'écart
(`weight_swapW`), le multi-ensemble des feuilles remplace une occurrence
de `x` par `y` (`leafWeights_swapW`), et la facture est l'écart de poids
fois la profondeur de la cible (`costW_swapW_eq` — une feuille à profondeur
`d` qui s'allège de `x − y` rend `d · (x − y)`). L'échange de DEUX feuilles
— l'inégalité de réarrangement du pli 5c lue sur l'arbre — refermera la
trousse au pli suivant.

Ancres du carnet `Compression-02` : le trie de Huffman de `[1, 1, 2, 4]`
porte ses feuilles aux profondeurs `[3, 3, 2, 1]` — la plus légère à la
profondeur maximale 3, la plus lourde juste sous la racine ; et sur
l'arbre déséquilibré de la maille 21 → 15 → 14 (pli 5b), alléger le poids
4 en 1 à profondeur 3 rend la facture 12 = 21 − 3 · (4 − 1).
-/
import Expansion

namespace CompressionLean

/-! ## La profondeur d'une feuille, la profondeur maximale -/

/-- Profondeur de la première feuille de poids `x`, en parcours profondeur
d'abord gauche. La valeur par défaut (feuille seule, ou poids absent) est
`0` : les lemmes ne lisent `depthOf` que sous hypothèse d'appartenance, où
le défaut n'intervient pas. -/
def depthOf : WTree → ℕ → ℕ
  | .leaf _, _ => 0
  | .node l r, x => if x ∈ leafWeights l then depthOf l x + 1 else depthOf r x + 1

/-- La profondeur maximale des feuilles — la hauteur de l'arbre. -/
def maxDepth : WTree → ℕ
  | .leaf _ => 0
  | .node l r => 1 + max (maxDepth l) (maxDepth r)

/-- Toute feuille vit au plus à la profondeur maximale. -/
theorem depthOf_le_maxDepth : ∀ (t : WTree) (x : ℕ), x ∈ leafWeights t →
    depthOf t x ≤ maxDepth t := by
  intro t
  induction t with
  | leaf w =>
      intro x h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp only [depthOf, maxDepth]
      omega
  | node l r ihl ihr =>
      intro x h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : x ∈ leafWeights l
      · have h1 := ihl x hq
        simp only [depthOf, if_pos hq, maxDepth]
        omega
      · have hr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        have h1 := ihr x hr
        simp only [depthOf, if_neg hq, maxDepth]
        omega

/-! ## Substituer le poids d'une feuille -/

/-- Remplacer le poids de la première feuille de poids `x` (parcours
profondeur d'abord gauche) par `y`. Même squelette de parcours que `subst`
du pli 5d — là où `subst` rouvrait une masse fusionnée en deux feuilles,
`swapW` ne touche qu'au poids d'une feuille, la structure est préservée. -/
def swapW : WTree → ℕ → ℕ → WTree
  | .leaf w, x, y => if w = x then .leaf y else .leaf w
  | .node l r, x, y =>
      if x ∈ leafWeights l then .node (swapW l x y) r else .node l (swapW r x y)

/-- Garde : hors cible, `swapW` ne touche rien. -/
theorem swapW_self : ∀ (t : WTree) (x y : ℕ), x ∉ leafWeights t →
    swapW t x y = t := by
  intro t
  induction t with
  | leaf w =>
      intro x y h
      by_cases hw : w = x
      · exact absurd (by simp [leafWeights, hw]) h
      · simp only [swapW, if_neg hw]
  | node l r ihl ihr =>
      intro x y h
      simp only [swapW]
      by_cases hq : x ∈ leafWeights l
      · exact absurd hq (fun hm => h (by
          simp only [leafWeights]
          exact List.mem_append.mpr (Or.inl hm)))
      · have hr : x ∉ leafWeights r := fun hm =>
          h (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inr hm))
        simp only [if_neg hq]
        rw [ihr x y hr]

/-- Le poids total paie exactement l'écart : substituer `y` au poids `x`
ajoute `y − x` à la masse (forme sans soustraction, valable en ℕ). -/
theorem weight_swapW : ∀ (t : WTree) (x y : ℕ), x ∈ leafWeights t →
    weight (swapW t x y) + x = weight t + y := by
  intro t
  induction t with
  | leaf w =>
      intro x y h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp only [swapW, if_true, weight]
      omega
  | node l r ihl ihr =>
      intro x y h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : x ∈ leafWeights l
      · have h1 := ihl x y hq
        simp only [swapW, if_pos hq, weight]
        omega
      · have hr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        have h1 := ihr x y hr
        simp only [swapW, if_neg hq, weight]
        omega

/-- Le multi-ensemble des feuilles remplace une occurrence de `x` par `y`
(l'occurrence effacée est la première, celle que `swapW` réécrit). -/
theorem leafWeights_swapW : ∀ (t : WTree) (x y : ℕ), x ∈ leafWeights t →
    List.Perm (leafWeights (swapW t x y))
      ((leafWeights t).erase x ++ [y]) := by
  intro t
  induction t with
  | leaf w =>
      intro x y h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp [swapW, leafWeights]
  | node l r ihl ihr =>
      intro x y h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : x ∈ leafWeights l
      · simp only [swapW, if_pos hq, leafWeights]
        rw [List.erase_append, if_pos hq]
        refine List.Perm.trans (List.Perm.append_right (leafWeights r) (ihl x y hq)) ?_
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
      · have hr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        simp only [swapW, if_neg hq, leafWeights]
        rw [List.erase_append, if_neg hq, List.append_assoc]
        exact List.Perm.append_left _ (ihr x y hr)

/-! ## La facture de la substitution -/

/-- **Théorème central du pli : substituer un poids facture l'écart à la
profondeur de la cible.** Remplacer la feuille de poids `x` (à profondeur
`depthOf t x`) par une feuille de poids `y` change la facture de
`x · d` à `y · d` — la structure ne bouge pas, seule la feuille réécrite
paie différemment, tous les autres termes de `costW` sont inchangés
(forme sans soustraction : valable en ℕ pour tout `y`). -/
theorem costW_swapW_eq : ∀ (t : WTree) (x y : ℕ), x ∈ leafWeights t →
    costW (swapW t x y) + x * depthOf t x = costW t + y * depthOf t x := by
  intro t
  induction t with
  | leaf w =>
      intro x y h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp [swapW, costW, depthOf]
  | node l r ihl ihr =>
      intro x y h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : x ∈ leafWeights l
      · have h1 := ihl x y hq
        have h2 := weight_swapW l x y hq
        simp only [swapW, if_pos hq, costW, depthOf, Nat.mul_add]
        omega
      · have hr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        have h1 := ihr x y hr
        have h2 := weight_swapW r x y hr
        simp only [swapW, if_neg hq, costW, depthOf, Nat.mul_add]
        omega

/-- Alléger une feuille ne coûte jamais plus : substituer un poids plus
petit à la même profondeur ne peut que baisser la facture. C'est le
corollaire monotone du théorème central — l'ingrédient qui, au pli
suivant, fera descendre les minima vers les paires profondes sans jamais
augmenter le coût. -/
theorem costW_swapW_le : ∀ (t : WTree) (x y : ℕ), y ≤ x → x ∈ leafWeights t →
    costW (swapW t x y) ≤ costW t := by
  intro t x y hy h
  have h1 := costW_swapW_eq t x y h
  have h2 : y * depthOf t x ≤ x * depthOf t x :=
    Nat.mul_le_mul hy (Nat.le_refl _)
  omega

/-! ## Ancres du carnet 02 : profondeurs du trie, maille 21 -/

/- Le trie de Huffman de [1, 1, 2, 4] : la plus légère feuille à la
profondeur maximale 3, la charge 2 à 2, la plus lourde juste sous la
racine — les profondeurs [3, 3, 2, 1] du pli 4, lues feuille à feuille. -/
#eval depthOf (huffman [1, 1, 2, 4]) 1
-- 3

#eval depthOf (huffman [1, 1, 2, 4]) 2
-- 2

#eval depthOf (huffman [1, 1, 2, 4]) 4
-- 1

#eval maxDepth (huffman [1, 1, 2, 4])
-- 3

/-- L'arbre déséquilibré du carnet 02 : coût 21, le poids 4 enfoncé à la
profondeur maximale — la maille de départ de la descente 21 → 15 → 14 du
pli 5b. -/
def desequilibre : WTree :=
  .node (.leaf 1) (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))

/-- La maille de départ : 21 = 1·1 + 1·2 + 2·3 + 4·3. -/
example : costW desequilibre = 21 := by decide

/-- Le poids 4 vit à la profondeur maximale 3. -/
example : depthOf desequilibre 4 = 3 := by decide

/-- Alléger le poids 4 en 1 à profondeur 3 rend la facture 12 : 21 −
3 · (4 − 1) = 21 − 9 — l'écart de poids fois la profondeur de la cible. -/
example : costW (swapW desequilibre 4 1) = 12 := by decide

/-- Le théorème central sur la même maille : 12 + 4·3 = 21 + 1·3 = 24. -/
example : costW (swapW desequilibre 4 1) + 4 * 3
    = costW desequilibre + 1 * 3 := by
  have h4 : depthOf desequilibre 4 = 3 := by decide
  rw [← h4, costW_swapW_eq desequilibre 4 1 (by decide)]

end CompressionLean
