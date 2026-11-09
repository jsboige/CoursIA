/-
# Expansion — le pas inductif de l'optimalité (pli 5d de #18706)

La preuve d'optimalité de Huffman procède par induction sur le nombre de
symboles : marier les deux plus petits poids `a + b`, résoudre le problème
réduit, puis développer la masse `a + b` en ses deux constituants. Ce module
établit la seconde moitié — l'**expansion** — avec sa trousse complète :
développer la feuille de poids `a + b` en un nœud `node (leaf a) (leaf b)`
descend les deux constituants d'un niveau sans toucher au reste de l'arbre,
et facture exactement la masse fusionnée : `costW (subst t a b) = costW t +
(a + b)` (lecture construction, cohérente avec `cost_dot` du pli 5c : la
feille `w` à profondeur `d` paie `w · d`, le nœud développé `a · (d+1) +
b · (d+1) = w · d + w`). Le poids, lui, ne bouge pas (`weight_subst`), et le
multi-ensemble des feuilles remplace une occurrence de `a + b` par `a` et
`b` (`leafWeights_subst`).

C'est l'ingrédient montant de l'induction : si un arbre `t'` est de coût
minimal pour les poids fusionnés, son expansion est un candidat de coût
`costW t' + (a + b)` pour les poids séparés. Le sens descendant — tout arbre
optimal contient les deux minima en feuilles sœurs (par l'inégalité de
réarrangement du pli 5c) — refermera le théorème d'optimalité complet au
pli suivant.

Ancres du carnet `Compression-02` : sur les poids `[1, 1, 2, 4]`, Huffman
commence par marier `1 + 1` ; le problème réduit vit sur `[2, 2, 4]` (trie
de coût 12, profondeurs `[2, 2, 1]`), et son expansion en `(1, 1)` rend le
coût 14 du trie complet — les profondeurs `[3, 3, 2, 1]` de l'ancre du pli 4.
-/
import Appariement

namespace CompressionLean

/-! ## L'expansion : développer une masse fusionnée -/

/-- Développer la première feuille de poids `a + b` (parcours profondeur
d'abord gauche) en le nœud `node (leaf a) (leaf b)`. C'est la fusion de
`build` (pli 4) vue dans l'autre sens : là où la construction marie deux
arbres en un nœud, `subst` reprend une masse déjà mariée et la rouvre en
ses deux constituants. -/
def subst : WTree → ℕ → ℕ → WTree
  | .leaf w, a, b => if w = a + b then .node (.leaf a) (.leaf b) else .leaf w
  | .node l r, a, b =>
      if a + b ∈ leafWeights l then .node (subst l a b) r
      else .node l (subst r a b)

/-- Garde : hors de sa cible, `subst` ne touche rien. -/
theorem subst_self : ∀ (t : WTree) (a b : ℕ), (a + b) ∉ leafWeights t →
    subst t a b = t := by
  intro t
  induction t with
  | leaf w =>
      intro a b h
      by_cases hw : w = a + b
      · exact absurd (by simp [leafWeights, hw]) h
      · simp only [subst, if_neg hw]
  | node l r ihl ihr =>
      intro a b h
      simp only [subst]
      by_cases hq : (a + b) ∈ leafWeights l
      · exact absurd hq (fun hm => h (by
          simp only [leafWeights]
          exact List.mem_append.mpr (Or.inl hm)))
      · have hr : (a + b) ∉ leafWeights r := fun hm =>
          h (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inr hm))
        simp only [if_neg hq]
        rw [ihr a b hr]

/-- L'expansion conserve le poids : le nœud développé pèse la masse de la
feuille qu'il remplace. -/
theorem weight_subst : ∀ (t : WTree) (a b : ℕ),
    weight (subst t a b) = weight t := by
  intro t
  induction t with
  | leaf w =>
      intro a b
      by_cases hw : w = a + b
      · simp only [subst, if_pos hw, weight]
        omega
      · simp only [subst, if_neg hw, weight]
  | node l r ihl ihr =>
      intro a b
      simp only [subst]
      by_cases hq : (a + b) ∈ leafWeights l
      · simp only [if_pos hq, weight, ihl a b]
      · simp only [if_neg hq, weight, ihr a b]

/-! ## La facture de l'expansion -/

/-- **Théorème central du pli : l'expansion facture exactement la masse
fusionnée.** Développer la feuille `a + b` en ses deux constituants les
descend d'un niveau chacun — les autres feuilles ne bougent pas — et le
surcoût est précisément `a + b`. C'est `cost_node_charge` (pli 5) lu dans
l'autre sens : la fusion qui avait facturé `a + b` la refacture à
l'ouverture. -/
theorem costW_subst : ∀ (t : WTree) (a b : ℕ), (a + b) ∈ leafWeights t →
    costW (subst t a b) = costW t + (a + b) := by
  intro t
  induction t with
  | leaf w =>
      intro a b h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp only [subst, if_true, costW, weight]
      omega
  | node l r ihl ihr =>
      intro a b h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : (a + b) ∈ leafWeights l
      · simp only [subst, if_pos hq, costW]
        rw [ihl a b hq, weight_subst l a b]
        omega
      · have hr : (a + b) ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        simp only [subst, if_neg hq, costW]
        rw [ihr a b hr, weight_subst r a b]
        omega

/-- L'expansion remplace une occurrence de la masse par ses deux
constituants : le multi-ensemble des feuilles perd un `a + b` et gagne `a`
et `b` (l'occurrence effacée est la première, celle que `subst` développe). -/
theorem leafWeights_subst : ∀ (t : WTree) (a b : ℕ), (a + b) ∈ leafWeights t →
    List.Perm (leafWeights (subst t a b))
      ((leafWeights t).erase (a + b) ++ [a, b]) := by
  intro t
  induction t with
  | leaf w =>
      intro a b h
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp [subst, leafWeights]
  | node l r ihl ihr =>
      intro a b h
      simp only [leafWeights, List.mem_append] at h
      by_cases hq : (a + b) ∈ leafWeights l
      · simp only [subst, if_pos hq, leafWeights]
        rw [List.erase_append, if_pos hq]
        refine List.Perm.trans (List.Perm.append_right (leafWeights r) (ihl a b hq)) ?_
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
      · have hr : (a + b) ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hq
          · exact hm
        simp only [subst, if_neg hq, leafWeights]
        rw [List.erase_append, if_neg hq, List.append_assoc]
        exact List.Perm.append_left _ (ihr a b hr)

/-! ## Ancres du carnet 02 : le problème réduit et son expansion -/

/- Sur les poids `[1, 1, 2, 4]`, la première fusion marie `1 + 1` : le
problème réduit vit sur `[2, 2, 4]`, de trie `node (node 2 2) 4` —
profondeurs `[2, 2, 1]`, coût 12. -/
#eval leafWeights (huffman [2, 2, 4])
-- [2, 2, 4]

#eval depthsW (huffman [2, 2, 4])
-- [2, 2, 1]

/-- Le coût du problème réduit : 12 = 2·2 + 2·2 + 4·1. -/
example : costW (huffman [2, 2, 4]) = 12 := by
  simp [huffman, build, insertT, weight, costW]

/-- L'expansion en `(1, 1)` rend le coût du problème complet : 12 + (1 + 1)
= 14, le coût du trie de Huffman de `[1, 1, 2, 4]` (ancre 14 du pli 5) —
les profondeurs passent de `[2, 2, 1]` à `[3, 3, 2, 1]` (ancre du pli 4),
les deux constituants descendent d'un niveau, les autres feuilles ne
bougent pas. -/
example : costW (subst (huffman [2, 2, 4]) 1 1) = 14 := by
  have h : (1 + 1) ∈ leafWeights (huffman [2, 2, 4]) := by
    simp [huffman, build, insertT, weight, leafWeights]
  rw [costW_subst (huffman [2, 2, 4]) 1 1 h]
  simp [huffman, build, insertT, weight, costW]

/- Les feuilles de l'expansion : la masse `2` réouverte en `1` et `1`. -/
#eval leafWeights (subst (huffman [2, 2, 4]) 1 1)
-- [1, 1, 2, 4]

/-- Le poids ne bouge pas : la masse totale reste celle des fréquences
d'entrée. -/
example : weight (subst (huffman [2, 2, 4]) 1 1) = 8 := by
  simp [huffman, build, insertT, weight, subst, leafWeights]

end CompressionLean
