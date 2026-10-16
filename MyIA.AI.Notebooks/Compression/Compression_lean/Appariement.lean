/-
# Appariement — le coût comme somme pondérée, l'échange général (pli 5c de #18706)

Le pli 5b (`Echange`) a établi le lemme d'échange dans sa maille élémentaire :
un père et son fils. Ce module porte la généralisation : le coût d'un arbre
est la somme des produits poids × profondeur de ses feuilles (`cost_dot`), et
l'échange de deux feuilles quelconques se lit alors comme l'inégalité de
réarrangement — apparier les poids forts aux profondeurs faibles ne coûte
jamais plus, l'écart exact étant le produit des deux écarts. Le théorème
d'optimalité complet (le trie de Huffman réalise le minimum, par induction
sur `sorted_two_min`) est le pli suivant.
-/
import Echange

namespace CompressionLean

/-! ## Le produit pondéré des deux parcours -/

/-- Produit scalaire de deux listes : chaque feuille paie son poids fois sa
profondeur. Les parcours `leafWeights` et `depthsW` visitent les feuilles
dans le même ordre (pli 5) — le produit terme à terme est la facture du
code. -/
def dotp : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | w :: ws, d :: ds => w * d + dotp ws ds

/-- Le produit est additif sur la concaténation : la facture d'une forêt est
la somme des factures, les deux parcours s'additionnant des deux côtés. -/
theorem dotp_append : ∀ (l1 r1 l2 r2 : List ℕ), l1.length = r1.length →
    dotp (l1 ++ l2) (r1 ++ r2) = dotp l1 r1 + dotp l2 r2 := by
  intro l1
  induction l1 with
  | nil =>
      intro r1 l2 r2 h
      cases r1 with
      | nil => simp [dotp]
      | cons e es => simp at h
  | cons w ws ih =>
      intro r1 l2 r2 h
      cases r1 with
      | nil => simp at h
      | cons e es =>
          simp only [List.cons_append, List.length_cons] at h ⊢
          simp only [dotp]
          rw [ih es l2 r2 (by omega)]
          omega

/-- Descendre toute une bande de feuilles d'un niveau facture exactement la
masse : chaque produit paie un poids de plus. C'est le pas qui unit les deux
lectures du coût dans `cost_dot`. -/
theorem dotp_map_succ : ∀ (l d : List ℕ), l.length = d.length →
    dotp l (d.map (· + 1)) = dotp l d + l.sum := by
  intro l
  induction l with
  | nil =>
      intro d h
      cases d with
      | nil => simp [dotp]
      | cons e es => simp at h
  | cons w ws ih =>
      intro d h
      cases d with
      | nil => simp at h
      | cons e es =>
          simp only [List.map_cons, List.length_cons] at h ⊢
          simp only [dotp, List.sum_cons]
          rw [ih es (by omega), Nat.mul_succ]
          omega

/-! ## La caractérisation en somme pondérée -/

/-- **Théorème central : le coût est la facture feuille à feuille.** La
lecture interne du pli 5 (`costW`, une charge par fusion) rejoint ici le
produit pondéré des parcours : `costW t = Σ wᵢ · dᵢ`. Tout échange de
feuilles devient une identité algébrique sur la somme. -/
theorem cost_dot (t : WTree) :
    costW t = dotp (leafWeights t) (depthsW t) := by
  induction t with
  | leaf w => simp [costW, leafWeights, depthsW, dotp]
  | node l r ihl ihr =>
      simp only [costW, leafWeights, depthsW]
      rw [dotp_append (leafWeights l) ((depthsW l).map (· + 1)) (leafWeights r)
          ((depthsW r).map (· + 1))
          (by simp only [List.length_map]; exact leafWeights_length l),
        dotp_map_succ (leafWeights l) (depthsW l) (leafWeights_length l),
        dotp_map_succ (leafWeights r) (depthsW r) (leafWeights_length r),
        ihl, ihr, leafWeights_sum l, leafWeights_sum r]
      omega

/-! ## L'inégalité de réarrangement, deux feuilles -/

/-- **L'écart exact de l'échange** : réapparier le poids faible `w1` à la
grande profondeur `d1` et le poids fort `w2` à la petite `d2` — le bon
appariement — coûte exactement le produit des deux écarts de moins que
l'inverse. -/
theorem rearrange_two_eq (w1 w2 d1 d2 : ℕ) (hw : w1 ≤ w2) (hd : d2 ≤ d1) :
    w1 * d2 + w2 * d1 = w1 * d1 + w2 * d2 + (w2 - w1) * (d1 - d2) := by
  obtain ⟨b, hb⟩ : ∃ b, w2 = w1 + b := ⟨w2 - w1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, d1 = d2 + e := ⟨d1 - d2, by omega⟩
  have hb' : w2 - w1 = b := by omega
  have he' : d1 - d2 = e := by omega
  rw [hb', he', hb, he]
  ring

/-- **L'échange général** : entre deux feuilles quelconques, apparier le
poids fort à la petite profondeur ne coûte jamais plus. C'est la
généralisation du `exchange_le` du pli 5b : ici les deux feuilles vivent à
des profondeurs arbitraires de l'arbre, et la preuve est l'identité
algébrique de `rearrange_two_eq` lue sur la somme `cost_dot`. -/
theorem rearrange_two (w1 w2 d1 d2 : ℕ) (hw : w1 ≤ w2) (hd : d2 ≤ d1) :
    w1 * d1 + w2 * d2 ≤ w1 * d2 + w2 * d1 := by
  rw [rearrange_two_eq w1 w2 d1 d2 hw hd]
  omega

/-! ## Ancres du carnet 02 -/

/- La facture du trie de Huffman de [1, 1, 2, 4] : 14 = 1·3 + 1·3 + 2·2 + 4·1,
la même valeur que les deux lectures du pli 5. -/
#eval dotp (leafWeights (huffman [1, 1, 2, 4])) (depthsW (huffman [1, 1, 2, 4]))

/-- Le théorème central sur l'ancre : la charge par fusions est la facture
feuille à feuille. -/
example : costW (huffman [1, 1, 2, 4]) =
    dotp (leafWeights (huffman [1, 1, 2, 4])) (depthsW (huffman [1, 1, 2, 4])) := by
  rw [cost_dot]

/-- L'échange général sur la paire du carnet : le poids 1 à profondeur 3, le
poids 4 à profondeur 1 — le bon appariement 1·3 + 4·1 = 7 contre 1·1 + 4·3 =
13, écart 6 = (4 - 1) · (3 - 1). -/
example : 1 * 3 + 4 * 1 ≤ 1 * 1 + 4 * 3 := by
  exact rearrange_two 1 4 3 1 (by omega) (by omega)

/-- L'écart exact de la même paire : 6. -/
example : 1 * 1 + 4 * 3 = 1 * 3 + 4 * 1 + (4 - 1) * (3 - 1) := by
  exact rearrange_two_eq 1 4 3 1 (by omega) (by omega)

/-- La maille élémentaire du pli 5b relue par le réarrangement : garder le 4
à profondeur 1 et le 1 à profondeur 2 (6) contre l'inverse (9) — les 2·2
communs mis à part, ce sont les 10 contre 13 d'`Echange`. -/
example : 1 * 2 + 4 * 1 ≤ 1 * 1 + 4 * 2 := by
  exact rearrange_two 1 4 2 1 (by omega) (by omega)

end CompressionLean
