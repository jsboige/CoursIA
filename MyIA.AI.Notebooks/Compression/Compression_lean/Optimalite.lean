/-
# Optimalité — le coût d'un code préfixe (pli 5 de #18706)

Le coût d'un code préfixe porte chaque feuille à sa profondeur : `w * d`. Ce
module établit l'identité structurelle du coût — chaque fusion de la
construction facture le poids du sous-arbre construit (`costW`) — et l'unit
à la lecture externe (`costAt k`, coût à profondeur de départ `k`) par le
théorème central `costAt_eq` : `costAt k t = costW t + k * weight t`.

Ancres du carnet `Compression-02` : le trie de Huffman de `[1, 1, 2, 4]`
coûte 14 (1·3 + 1·3 + 2·2 + 4·1), contre 16 pour le code fixe de 2 bits
(2·(1+1+2+4)) — Huffman gagne en descendant les poids forts près de la
racine. Le théorème d'optimalité parmi tous les arbres préfixes (lemme
d'échange) est le pli suivant de la feuille de route.
-/
import Huffman

namespace CompressionLean

/-! ## Parcours des poids -/

/-- Poids des feuilles en parcours profondeur d'abord gauche — le même ordre
que `depthsW` (pli 4), donc l'appariement `(leafWeights t)[i], (depthsW t)[i]`
est la feuille et sa profondeur. -/
def leafWeights : WTree → List ℕ
  | .leaf w => [w]
  | .node l r => leafWeights l ++ leafWeights r

/-- Les deux parcours produisent des listes de même longueur. -/
theorem leafWeights_length (t : WTree) : (leafWeights t).length = (depthsW t).length := by
  induction t with
  | leaf w => rfl
  | node l r ihl ihr =>
    simp only [leafWeights, depthsW, List.length_append, List.length_map, ihl, ihr]

/-- La masse des feuilles est le poids de l'arbre. -/
theorem leafWeights_sum (t : WTree) : (leafWeights t).sum = weight t := by
  induction t with
  | leaf w => rfl
  | node l r ihl ihr =>
    simp only [leafWeights, weight, List.sum_append, ihl, ihr]

/-! ## Le coût, deux lectures -/

/-- Coût à profondeur de départ `k` : chaque feuille paie son poids fois sa
profondeur absolue (`k` + descentes). `costAt 0 t` est la lecture externe du
coût du code porté par `t`. -/
def costAt (k : ℕ) : WTree → ℕ
  | .leaf w => w * k
  | .node l r => costAt (k + 1) l + costAt (k + 1) r

/-- Coût interne : chaque nœud interne facture le poids de son sous-arbre.
C'est la lecture de la construction — fusionner `l` et `r` ajoute
`weight l + weight r` au coût total, indépendamment de la profondeur. -/
def costW : WTree → ℕ
  | .leaf _ => 0
  | .node l r => costW l + weight l + costW r + weight r

/-- Forme équivalente : la fusion facture le poids du nœud construit. -/
theorem cost_node_charge (l r : WTree) :
    costW (.node l r) = costW l + costW r + weight (.node l r) := by
  simp only [costW, weight]
  omega

/-- Théorème central : la lecture externe se décompose en la part
structurelle (`costW`) plus la masse facturée au niveau de départ. Chaque
niveau de descente supplémentaire coûte exactement la masse de l'arbre. -/
theorem costAt_eq (k : ℕ) (t : WTree) : costAt k t = costW t + k * weight t := by
  induction t generalizing k with
  | leaf w =>
    simp only [costAt, costW, weight]
    ring
  | node l r ihl ihr =>
    simp only [costAt, costW, weight]
    rw [ihl (k + 1), ihr (k + 1)]
    ring

/-- À la racine, les deux lectures coïncident. -/
theorem cost_zero (t : WTree) : costAt 0 t = costW t := by
  rw [costAt_eq]
  omega

/-! ## Ancres du carnet 02 -/

/- Le trie de Huffman de [1, 1, 2, 4] : a=0, b=10, c=110, d=111 (pli 4). -/

/-- Le coût du trie de Huffman de `[1, 1, 2, 4]` : 14 = 1·3 + 1·3 + 2·2 + 4·1
(profondeurs `[3, 3, 2, 1]`, pli 4), strictement sous les 16 du code fixe. -/
example : costAt 0 (huffman [1, 1, 2, 4]) = 14 := by
  simp [huffman, build, insertT, weight, costAt]

/-- Le code fixe de 2 bits sur les mêmes poids : toute profondeur 2, coût
2·(1+1+2+4) = 16 — Huffman économise 2 en montant les poids forts. -/
example : costAt 0 (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 2) (.leaf 4))) = 16 := by
  decide

/-- La masse se conserve : le trie porte le poids total de la forêt initiale. -/
example : weight (huffman [1, 1, 2, 4]) = 8 := by
  simp [huffman, build, insertT, weight]

/- Les poids des feuilles du trie, en parcours : la fusion des deux minima
les a enfoncées à profondeur maximale. -/
#eval leafWeights (huffman [1, 1, 2, 4])

end CompressionLean
