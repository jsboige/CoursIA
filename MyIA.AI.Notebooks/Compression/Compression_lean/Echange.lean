/-
# Échange — faire monter un poids fort ne augmente jamais le coût (pli 5b de #18706)

Le lemme d'échange est le geste central de l'optimalité de Huffman. Ce module
en établit la forme élémentaire : dans un nœud, échanger un poids faible `a`
placé près de la racine contre un poids fort `b` placé en dessous ne augmente
pas le coût — l'arbre qui garde `b` en haut est le meilleur des deux. La
symétrie du coût entre les deux branches d'un nœud (`cost_node_comm`) dit que
ce choix est le seul degré de liberté local. La généralisation à des poids à
profondeurs arbitraires (par le parcours `leafWeights`/`depthsW` du pli 5) et
le théorème d'optimalité complet sont le pli suivant.

Ancres du carnet `Compression-02` sur les poids `[1, 1, 2, 4]` : l'arbre qui
garde les poids faibles en haut coûte 21 ; deux échanges (1 contre 4, puis
2 contre 1) le ramènent au trie de Huffman (14, pli 5) sans jamais augmenter
le coût — chaque étape est une instance de `exchange_le`.
-/
import Optimalite

namespace CompressionLean

/-! ## Symétrie du coût entre branches -/

/-- Le coût d'un nœud ne dépend pas de l'ordre de ses deux branches : échanger
des sous-arbres entiers de même niveau ne change rien (le poids descend avec
son sous-arbre). Le choix qui compte se joue entre feuilles, pas entre
branches. -/
theorem cost_node_comm (k : ℕ) (l r : WTree) :
    costAt k (.node l r) = costAt k (.node r l) := by
  simp only [costAt]
  omega

/-! ## Le lemme d'échange élémentaire -/

/-- Échanger un poids faible `a` placé en haut contre un poids fort `b` placé
en dessous ne augmente pas le coût : l'arbre qui garde `b` près de la racine
est le meilleur des deux. L'écart de coût vaut exactement `b - a`, le prix
d'un niveau de descente du poids fort. C'est le geste du carnet `Compression-02`
: Huffman gagne en gardant les poids forts près de la racine. -/
theorem exchange_le (k a b : ℕ) (r : WTree) (h : a ≤ b) :
    costAt k (.node (.leaf b) (.node (.leaf a) r)) ≤
      costAt k (.node (.leaf a) (.node (.leaf b) r)) := by
  simp only [costAt, Nat.mul_succ]
  omega

/-- La forme stricte : dès que `a < b`, garder le poids fort en haut gagne
strictement — l'égalité ne tient que pour des poids égaux. -/
theorem exchange_lt (k a b : ℕ) (r : WTree) (h : a < b) :
    costAt k (.node (.leaf b) (.node (.leaf a) r)) <
      costAt k (.node (.leaf a) (.node (.leaf b) r)) := by
  simp only [costAt, Nat.mul_succ]
  omega

/-! ## Ancres du carnet 02 : la descente 21 → 15 → 14 -/

/- L'arbre défavorable : les poids faibles en haut. Coût 21 =
1·1 + 1·2 + 2·3 + 4·3 — chaque poids paie un niveau de trop. -/

/-- Les poids `[1, 1, 2, 4]` mal orientés (faibles en haut) coûtent 21. -/
example : costAt 0 (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))) = 21 := by
  decide

/- Premier échange : le 4 monte d'un niveau contre un 1 (instance directe de
`exchange_le` avec `a = 1`, `b = 4`, `r = .node (.leaf 2) (.leaf 1)`). Le coût
tombe de 21 à 15. -/

/-- Après l'échange 1 contre 4 : coût 15 = 4·1 + 1·2 + 2·3 + 1·3. -/
example : costAt 0 (.node (.leaf 4) (.node (.leaf 1) (.node (.leaf 2) (.leaf 1)))) = 15 := by
  decide

/-- La première étape ne augmente pas le coût — instance de `exchange_le`. -/
example :
    costAt 0 (.node (.leaf 4) (.node (.leaf 1) (.node (.leaf 2) (.leaf 1)))) ≤
      costAt 0 (.node (.leaf 1) (.node (.leaf 4) (.node (.leaf 2) (.leaf 1)))) := by
  exact exchange_le 0 1 4 (.node (.leaf 2) (.leaf 1)) (by omega)

/- Second échange : le 2 monte contre le 1 restant. L'arbre obtenu est le trie
de Huffman de `[1, 1, 2, 4]` (profondeurs `[3, 3, 2, 1]`, pli 4) au coût 14 de
l'ancre du pli 5. -/

/-- Après le second échange : coût 14 = 4·1 + 2·2 + 1·3 + 1·3 — le trie de
Huffman de `[1, 1, 2, 4]` (comparer `Optimalite.lean`, ancre 14 contre 16). -/
example : costAt 0 (.node (.leaf 4) (.node (.leaf 2) (.node (.leaf 1) (.leaf 1)))) = 14 := by
  decide

/-- La seconde étape ne augmente pas le coût : `exchange_le` au niveau du
sous-arbre, puis le 4 commun à la racine paie `4·1` des deux côtés. -/
example :
    costAt 0 (.node (.leaf 4) (.node (.leaf 2) (.node (.leaf 1) (.leaf 1)))) ≤
      costAt 0 (.node (.leaf 4) (.node (.leaf 1) (.node (.leaf 2) (.leaf 1)))) := by
  have h := exchange_le 1 1 2 (.leaf 1) (by omega)
  simp only [costAt] at h ⊢
  omega

/- La maille élémentaire de l'échange, sur feuilles nues : garder le 4 en haut
coûte 10, le mettre en dessous du 1 coûte 13 — écart 3 = `b - a`. -/

/-- L'écart de la maille élémentaire : 10 contre 13. -/
example :
    costAt 0 (.node (.leaf 4) (.node (.leaf 1) (.leaf 2))) = 10 ∧
      costAt 0 (.node (.leaf 1) (.node (.leaf 4) (.leaf 2))) = 13 := by
  constructor <;> decide

end CompressionLean
