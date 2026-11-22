/-
# Descente — amener un minimum dans la paire profonde (pli 5g de #18706)

Le théorème d'optimalité (pli suivant) veut voir les deux poids minima vivre
dans la paire de sœurs à la profondeur maximale — le réceptacle que le pli 5f a
garanti exister (`sisterPath_spec`). Ce pli en livre la première moitié :
**tout poids minimal peut être amené dans cette paire par UN échange
positionnel, sans jamais augmenter le coût** (`min_to_bottom`).

L'échange est positionnel — deux `replaceAt` aux chemins exacts, pas un
`exchangeW` par poids : quand le trie compte deux feuilles de même poids (la
maille du carnet 02 porte deux 1), un lemme énoncé sur « la feuille de poids x »
risque de viser la mauvaise ; le chemin, lui, désigne une feuille unique. La
facture combinée (`costW_exchPos_eq`) reprend celle du pli 5f feuille à
feuille : chaque position paie l'écart de poids à SA profondeur, et l'écart
total est le produit des écarts — nul ou négatif dès que le poids qui descend
est minimal et la cible plus profonde (`costW_exchPos_le`).

L'infrastructure est le vrai contenu du pli : les chemins se prolongent
(`subtreeAt_congr`), un remplacement ne touche aucune position divergente
(`subtreeAt_replaceAt_ne`), le multi-ensemble des feuilles survit au
remplacement (`leafWeights_replaceAt`), toute feuille a un chemin
(`exists_leafPos`) et aucun chemin ne dépasse la hauteur (`pathLen_le_maxDepth`).

Ancre du carnet `Compression-02` : sur l'arbre déséquilibré de la maille 21,
descendre le minimum 1 (profondeur 1) dans la paire (2, 4) à la profondeur
maximale rend 21 − (2−1)·(3−1) = 19.
-/
import Soeurs

namespace CompressionLean

/-! ## L'infrastructure positionnelle -/

/-- Un chemin vers un sous-arbre se prolonge : consulter `π ++ π'` revient à
consulter `π'` depuis le sous-arbre au bout de `π`. -/
theorem subtreeAt_congr : ∀ (t : WTree) (π π' : List Bool) (s : WTree),
    subtreeAt t π = some s → subtreeAt t (π ++ π') = subtreeAt s π' := by
  intro t
  induction t with
  | leaf w =>
      intro π π' s h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst h
          rfl
      | cons go π'' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π π' s h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst h
          rfl
      | cons go π'' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, subtreeAt]
              exact ihl π'' π' s h
          | false =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, subtreeAt]
              exact ihr π'' π' s h

/-- La feuille au bout d'un chemin pèse son poids dans le multi-ensemble. -/
theorem subtreeAt_mem : ∀ (t : WTree) (π : List Bool) (x : ℕ),
    subtreeAt t π = some (.leaf x) → x ∈ leafWeights t := by
  intro t
  induction t with
  | leaf w =>
      intro π x h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          simp [leafWeights]
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          simp only [leafWeights, List.mem_append]
          cases go with
          | true =>
              simp only [subtreeAt] at h
              exact Or.inl (ihl π' x h)
          | false =>
              simp only [subtreeAt] at h
              exact Or.inr (ihr π' x h)

/-- Toute feuille de l'arbre est au bout d'un chemin. -/
theorem exists_leafPos : ∀ (t : WTree) (w : ℕ), w ∈ leafWeights t →
    ∃ π : List Bool, subtreeAt t π = some (.leaf w) := by
  intro t
  induction t with
  | leaf w' =>
      intro w hw
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact ⟨[], rfl⟩
  | node l r ihl ihr =>
      intro w hw
      simp only [leafWeights, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨π, hπ⟩ := ihl w hw
        exact ⟨true :: π, hπ⟩
      · obtain ⟨π, hπ⟩ := ihr w hw
        exact ⟨false :: π, hπ⟩

/-- Aucun chemin valide ne dépasse la hauteur : la profondeur maximale
plafonne tous les chemins, pas seulement celui de la paire du pli 5f. -/
theorem pathLen_le_maxDepth : ∀ (t : WTree) (π : List Bool) (s : WTree),
    subtreeAt t π = some s → π.length ≤ maxDepth t := by
  intro t
  induction t with
  | leaf w =>
      intro π s h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst h
          exact Nat.zero_le _
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π s h
      cases π with
      | nil =>
          simp only [List.length_nil]
          exact Nat.zero_le _
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have h1 := ihl π' s h
              simp only [List.length_cons, maxDepth]
              omega
          | false =>
              simp only [subtreeAt] at h
              have h1 := ihr π' s h
              simp only [List.length_cons, maxDepth]
              omega

/-- Remplacer une feuille ne change pas la forme : la hauteur est un invariant
du remplacement (l'échange du pli conserve donc la profondeur de la paire). -/
theorem maxDepth_replaceAt : ∀ (t : WTree) (π : List Bool) (x y : ℕ),
    subtreeAt t π = some (.leaf x) → maxDepth (replaceAt t π y) = maxDepth t := by
  intro t
  induction t with
  | leaf w =>
      intro π x y h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          rfl
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x y h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [replaceAt, maxDepth]
              rw [ihl π' x y h]
          | false =>
              simp only [subtreeAt] at h
              simp only [replaceAt, maxDepth]
              rw [ihr π' x y h]

/-- Le remplacement atteint sa cible : la position visée porte bien le nouveau
poids. -/
theorem subtreeAt_replaceAt_self : ∀ (t : WTree) (π : List Bool) (x y : ℕ),
    subtreeAt t π = some (.leaf x) →
    subtreeAt (replaceAt t π y) π = some (.leaf y) := by
  intro t
  induction t with
  | leaf w =>
      intro π x y h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          rfl
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x y h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [replaceAt, subtreeAt]
              exact ihl π' x y h
          | false =>
              simp only [subtreeAt] at h
              simp only [replaceAt, subtreeAt]
              exact ihr π' x y h

/-- **Remplacer une feuille ne touche aucune position divergente** : dès que
les deux chemins ne sont pas emboîtés (aucun n'est préfixe de l'autre) et
distincts, la consultation ailleurs rend le même sous-arbre avant et après le
remplacement. -/
theorem subtreeAt_replaceAt_ne : ∀ (t : WTree) (cible π : List Bool) (x y : ℕ),
    subtreeAt t cible = some (.leaf x) → π ≠ cible →
    (∀ q, cible ++ q ≠ π) → (∀ q, π ++ q ≠ cible) →
    subtreeAt (replaceAt t cible y) π = subtreeAt t π := by
  intro t
  induction t with
  | leaf w =>
      intro cible π x y h hne hnp1 hnp2
      cases cible with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          cases π with
          | nil => exact absurd rfl hne
          | cons go π' => rfl
      | cons go c' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro cible π x y h hne hnp1 hnp2
      cases cible with
      | nil => simp [subtreeAt] at h
      | cons go c' =>
          cases π with
          | nil =>
              exact (hnp2 (go :: c') (List.nil_append (go :: c'))).elim
          | cons go2 π' =>
              cases go with
              | true =>
                  cases go2 with
                  | true =>
                      have hne' : π' ≠ c' := by
                        intro he
                        apply hne
                        rw [he]
                      have hc1 : ∀ q, c' ++ q ≠ π' := fun q hq =>
                        hnp1 q (by simp only [List.cons_append]; rw [hq])
                      have hc2 : ∀ q, π' ++ q ≠ c' := fun q hq =>
                        hnp2 q (by simp only [List.cons_append]; rw [hq])
                      simp only [replaceAt, subtreeAt]
                      exact ihl c' π' x y h hne' hc1 hc2
                  | false => rfl
              | false =>
                  cases go2 with
                  | true => rfl
                  | false =>
                      have hne' : π' ≠ c' := by
                        intro he
                        apply hne
                        rw [he]
                      have hc1 : ∀ q, c' ++ q ≠ π' := fun q hq =>
                        hnp1 q (by simp only [List.cons_append]; rw [hq])
                      have hc2 : ∀ q, π' ++ q ≠ c' := fun q hq =>
                        hnp2 q (by simp only [List.cons_append]; rw [hq])
                      simp only [replaceAt, subtreeAt]
                      exact ihr c' π' x y h hne' hc1 hc2

/-- **Deux positions qui portent des sous-arbres ne peuvent être emboîtées
que si elles coïncident** : prolonger le chemin d'une feuille quitte l'arbre
(`none`), donc un préfixe strict d'un chemin valide ne mène plus nulle part. -/
theorem leafPos_prefix : ∀ (t : WTree) (π₁ π₂ : List Bool) (x : ℕ) (s : WTree),
    subtreeAt t π₁ = some (.leaf x) → subtreeAt t π₂ = some s →
    ∀ q, π₁ ++ q = π₂ → π₁ = π₂ := by
  intro t π₁ π₂ x s h1 h2 q hq
  rw [← hq, subtreeAt_congr t π₁ q (.leaf x) h1] at h2
  cases q with
  | nil => simpa only [List.append_nil] using hq
  | cons go q' => simp [subtreeAt] at h2

/-- Remplacer l'enfant gauche d'un nœud interne adressé par un chemin. -/
theorem subtreeAt_parent_left : ∀ (t : WTree) (π : List Bool) (x y : ℕ) (r : WTree),
    subtreeAt t π = some (WTree.node (.leaf x) r) →
    subtreeAt (replaceAt t (π ++ [true]) y) π = some (WTree.node (.leaf y) r) := by
  intro t
  induction t with
  | leaf w =>
      intro π x y r h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' => simp [subtreeAt] at h
  | node l r' ihl ihr =>
      intro π x y r h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.node.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          rfl
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, replaceAt, subtreeAt]
              exact ihl π' x y r h
          | false =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, replaceAt, subtreeAt]
              exact ihr π' x y r h

/-- Remplacer l'enfant droit d'un nœud interne adressé par un chemin. -/
theorem subtreeAt_parent_right : ∀ (t : WTree) (π : List Bool) (x y : ℕ) (l : WTree),
    subtreeAt t π = some (WTree.node l (.leaf x)) →
    subtreeAt (replaceAt t (π ++ [false]) y) π = some (WTree.node l (.leaf y)) := by
  intro t
  induction t with
  | leaf w =>
      intro π x y l h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' => simp [subtreeAt] at h
  | node l' r ihl ihr =>
      intro π x y l h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.node.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          rfl
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, replaceAt, subtreeAt]
              exact ihl π' x y l h
          | false =>
              simp only [subtreeAt] at h
              simp only [List.cons_append, replaceAt, subtreeAt]
              exact ihr π' x y l h

/-- Effacer une occurrence de `l₂` commute à la concaténation au sens du
multi-ensemble : que l'occurrence effacée vive dans la partie gauche ou dans
`l₂` elle-même, le résultat est une permutation de `l₁ ++ l₂.erase x`. La
garde `x ∈ l₂` est nécessaire — sans elle, `erase` retirerait une occurrence
de `l₁` et le compte du poids partirait du mauvais côté. -/
theorem perm_erase_append : ∀ (l₁ l₂ : List ℕ) (x : ℕ), x ∈ l₂ →
    List.Perm ((l₁ ++ l₂).erase x) (l₁ ++ l₂.erase x) := by
  intro l₁ l₂ x hmem
  rw [List.perm_iff_count]
  intro v
  by_cases hvx : v = x
  · rw [hvx]
    by_cases hxl : x ∈ l₁
    · have hc1 : 0 < List.count x l₁ := List.count_pos_iff.mpr hxl
      have hc2 : 0 < List.count x l₂ := List.count_pos_iff.mpr hmem
      rw [List.erase_append, if_pos hxl, List.count_append, List.count_append,
          List.count_erase_self, List.count_erase_self]
      omega
    · rw [List.erase_append, if_neg hxl]
  · rw [List.count_erase_of_ne hvx, List.count_append, List.count_append,
      List.count_erase_of_ne hvx]

/-- Le multi-ensemble des feuilles après remplacement positionnel : une
occurrence du poids cédé part, le nouveau arrive — miroir positionnel de
`leafWeights_swapW` (au sens du multi-ensemble : peu importe l'occurrence
effacée, le chemin peut viser la partie droite alors que le poids vit aussi
à gauche). -/
theorem leafWeights_replaceAt : ∀ (t : WTree) (π : List Bool) (x y : ℕ),
    subtreeAt t π = some (.leaf x) →
    List.Perm (leafWeights (replaceAt t π y)) ((leafWeights t).erase x ++ [y]) := by
  intro t
  induction t with
  | leaf w =>
      intro π x y h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          simp [replaceAt, leafWeights]
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x y h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have hmem : x ∈ leafWeights l := subtreeAt_mem l π' x h
              simp only [replaceAt, leafWeights]
              rw [List.erase_append, if_pos hmem]
              refine List.Perm.trans (List.Perm.append_right (leafWeights r) (ihl π' x y h)) ?_
              rw [List.append_assoc, List.append_assoc]
              exact List.Perm.append_left _ List.perm_append_comm
          | false =>
              simp only [subtreeAt] at h
              simp only [replaceAt, leafWeights]
              refine List.Perm.trans (List.Perm.append_left (leafWeights l) (ihr π' x y h)) ?_
              rw [← List.append_assoc]
              exact List.Perm.append_right [y]
                (perm_erase_append (leafWeights l) (leafWeights r) x
                  (subtreeAt_mem r π' x h)).symm

/-- La double substitution croisée (x parti, y venu ; y reparti, x revenu)
est neutre sur le multi-ensemble. -/
theorem perm_double_exch : ∀ (l : List ℕ) (x y : ℕ), x ∈ l →
    List.Perm ((l.erase x ++ [y]).erase y ++ [x]) l := by
  intro l x y hmem
  have key : ∀ v : ℕ, ((l.erase x ++ [y]).erase y).count v = (l.erase x).count v := by
    intro v
    by_cases hvy : v = y
    · rw [hvy, List.count_erase_self, List.count_append]
      have hy1 : List.count y [y] = 1 := by
        rw [List.count_cons_self, List.count_nil]
      rw [hy1]
      omega
    · rw [List.count_erase_of_ne hvy, List.count_append]
      have hy0 : List.count v [y] = 0 := by
        rw [List.count_cons_of_ne (Ne.symm hvy), List.count_nil]
      rw [hy0]
      omega
  rw [List.perm_iff_count]
  intro v
  rw [List.count_append, key v]
  by_cases hvx : v = x
  · rw [hvx, List.count_erase_self]
    have hc : 0 < List.count x l := List.count_pos_iff.mpr hmem
    have hx1 : List.count x [x] = 1 := by
      rw [List.count_cons_self, List.count_nil]
    rw [hx1]
    omega
  · rw [List.count_erase_of_ne hvx]
    have hx0 : List.count v [x] = 0 := by
      rw [List.count_cons_of_ne (Ne.symm hvx), List.count_nil]
    rw [hx0]
    omega

/-! ## L'échange positionnel de deux feuilles -/

/-- Échanger les CONTENUS de deux positions : la feuille de poids `x₁` en `π₁`
et la feuille de poids `x₂` en `π₂` permutent leurs poids. Deux `replaceAt`
aux chemins exacts — jamais par poids : quand l'arbre compte deux feuilles de
même poids, l'échange par poids pourrait viser la mauvaise. -/
def exchPos (t : WTree) (π₁ π₂ : List Bool) (x₁ x₂ : ℕ) : WTree :=
  replaceAt (replaceAt t π₁ x₂) π₂ x₁

/-- **Facture de l'échange positionnel : chaque position paie l'écart de poids
à SA profondeur.** Tous les autres termes de `costW` sont inchangés — le
remplacement en `π₁` ne touche pas `π₂` (chemins divergents, `leafPos_prefix`)
et réciproquement. -/
theorem costW_exchPos_eq : ∀ (t : WTree) (π₁ π₂ : List Bool) (x₁ x₂ : ℕ),
    subtreeAt t π₁ = some (.leaf x₁) → subtreeAt t π₂ = some (.leaf x₂) → π₁ ≠ π₂ →
    costW (exchPos t π₁ π₂ x₁ x₂) + x₁ * π₁.length + x₂ * π₂.length
      = costW t + x₂ * π₁.length + x₁ * π₂.length := by
  intro t π₁ π₂ x₁ x₂ h1 h2 hne
  have hkeep : subtreeAt (replaceAt t π₁ x₂) π₂ = some (.leaf x₂) := by
    refine (subtreeAt_replaceAt_ne t π₁ π₂ x₁ x₂ h1 hne.symm ?_ ?_).trans h2
    · intro q hq
      exact hne (leafPos_prefix t π₁ π₂ x₁ (.leaf x₂) h1 h2 q hq)
    · intro q hq
      exact hne (leafPos_prefix t π₂ π₁ x₂ (.leaf x₁) h2 h1 q hq).symm
  have hc1 := costW_replaceAt_eq t π₁ x₁ x₂ h1
  have hc2 := costW_replaceAt_eq (replaceAt t π₁ x₂) π₂ x₂ x₁ hkeep
  simp only [exchPos]
  omega

/-- **Faire descendre un poids plus léger dans une position plus profonde ne
coûte jamais plus** : l'écart est le produit `(x₁ − x₂)·(|π₁| − |π₂|)`, nul ou
négatif sous les deux inégalités — le réarrangement du pli 5c lu sur les
chemins. -/
theorem costW_exchPos_le : ∀ (t : WTree) (π₁ π₂ : List Bool) (x₁ x₂ : ℕ),
    subtreeAt t π₁ = some (.leaf x₁) → subtreeAt t π₂ = some (.leaf x₂) → π₁ ≠ π₂ →
    x₂ ≤ x₁ → π₂.length ≤ π₁.length →
    costW (exchPos t π₁ π₂ x₁ x₂) ≤ costW t := by
  intro t π₁ π₂ x₁ x₂ h1 h2 hne hle hlen
  have hfact := costW_exchPos_eq t π₁ π₂ x₁ x₂ h1 h2 hne
  obtain ⟨k, hk⟩ : ∃ k, x₁ = x₂ + k := ⟨x₁ - x₂, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, π₁.length = π₂.length + m := ⟨π₁.length - π₂.length, by omega⟩
  simp only [exchPos] at hfact ⊢
  simp only [hk, hm, Nat.mul_add, Nat.add_mul] at hfact ⊢
  omega

/-! ## La descente du minimum -/

/-- **Tout poids minimal peut être amené dans la paire de sœurs à la profondeur
maximale sans augmenter le coût.** La première moitié du lemme des sœurs du
théorème d'optimalité : le réceptacle du pli 5f (`sisterPath_spec`) reçoit le
minimum par UN échange positionnel — soit il y est déjà (cas trivial), soit la
facture `costW_exchPos_le` plafonne le coût à l'égalité du produit des écarts.
Le multi-ensemble des feuilles est conservé, la forme (donc la hauteur) aussi :
la paire obtenue vit exactement à la profondeur maximale de l'arbre initial. -/
theorem min_to_bottom : ∀ (t : WTree), (∃ l r, t = WTree.node l r) → ∀ (w : ℕ),
    (∀ v ∈ leafWeights t, w ≤ v) → w ∈ leafWeights t →
    ∃ (t' : WTree) (π : List Bool) (c : ℕ),
      List.Perm (leafWeights t') (leafWeights t) ∧
      costW t' ≤ costW t ∧
      subtreeAt t' π = some (WTree.node (.leaf w) (.leaf c)) ∧
      π.length + 1 = maxDepth t' := by
  intro t hnode w hmin hw
  obtain ⟨π₀, a, b, hs, hl⟩ := sisterPath_spec t hnode
  have hL : subtreeAt t (π₀ ++ [true]) = some (.leaf a) := by
    rw [subtreeAt_congr t π₀ [true] (WTree.node (.leaf a) (.leaf b)) hs]
    rfl
  have hR : subtreeAt t (π₀ ++ [false]) = some (.leaf b) := by
    rw [subtreeAt_congr t π₀ [false] (WTree.node (.leaf a) (.leaf b)) hs]
    rfl
  have hlenL : (π₀ ++ [true]).length = maxDepth t := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlenR : (π₀ ++ [false]).length = maxDepth t := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have mema : a ∈ leafWeights t := subtreeAt_mem t (π₀ ++ [true]) a hL
  by_cases hwa : w = a
  · exact ⟨t, π₀, b, List.Perm.refl _, Nat.le_refl _, by rw [hwa]; exact hs, hl⟩
  · by_cases hwb : w = b
    · -- échange interne à la paire : le minimum prend la place gauche
      have hneLR : (π₀ ++ [false]) ≠ (π₀ ++ [true]) := by
        intro he
        rw [he] at hR
        exact hwa (hwb.trans (WTree.leaf.inj (Option.some.inj (hL.symm.trans hR))).symm)
      have hba : b ≤ a := by
        rw [← hwb]
        exact hmin a mema
      have hkeepR' : subtreeAt (replaceAt t (π₀ ++ [true]) b) (π₀ ++ [false])
          = some (.leaf b) := by
        refine (subtreeAt_replaceAt_ne t (π₀ ++ [true]) (π₀ ++ [false]) a b hL hneLR ?_ ?_).trans hR
        · intro q hq
          exact hneLR (leafPos_prefix t (π₀ ++ [true]) (π₀ ++ [false]) a (.leaf b) hL hR q hq).symm
        · intro q hq
          exact hneLR (leafPos_prefix t (π₀ ++ [false]) (π₀ ++ [true]) b (.leaf a) hR hL q hq)
      have hu0 : subtreeAt (replaceAt t (π₀ ++ [true]) b) π₀
          = some (WTree.node (.leaf b) (.leaf b)) :=
        subtreeAt_parent_left t π₀ a b (.leaf b) hs
      have hpr : subtreeAt (replaceAt (replaceAt t (π₀ ++ [true]) b) (π₀ ++ [false]) a) π₀
          = some (WTree.node (.leaf b) (.leaf a)) :=
        subtreeAt_parent_right (replaceAt t (π₀ ++ [true]) b) π₀ b a (.leaf b) hu0
      have hmd1 := maxDepth_replaceAt t (π₀ ++ [true]) a b hL
      have hmd2 := maxDepth_replaceAt (replaceAt t (π₀ ++ [true]) b) (π₀ ++ [false]) b a hkeepR'
      have hp1 := leafWeights_replaceAt t (π₀ ++ [true]) a b hL
      have hp2 := leafWeights_replaceAt (replaceAt t (π₀ ++ [true]) b) (π₀ ++ [false]) b a hkeepR'
      refine ⟨exchPos t (π₀ ++ [true]) (π₀ ++ [false]) a b, π₀, a,
        hp2.trans ((List.Perm.append_right [a] (hp1.erase b)).trans
          (perm_double_exch (leafWeights t) a b mema)),
        costW_exchPos_le t (π₀ ++ [true]) (π₀ ++ [false]) a b hL hR hneLR.symm hba (by omega),
        by rw [hwb]; simp only [exchPos]; exact hpr, ?_⟩
      simp only [exchPos]
      omega
    · -- le cas principal : une occurrence du minimum ailleurs dans l'arbre
      obtain ⟨πw, hwπ⟩ := exists_leafPos t w hw
      have hneL : πw ≠ (π₀ ++ [true]) := by
        intro he
        rw [he] at hwπ
        exact hwa (WTree.leaf.inj (Option.some.inj (hwπ.symm.trans hL)))
      have hneR : πw ≠ (π₀ ++ [false]) := by
        intro he
        rw [he] at hwπ
        exact hwb (WTree.leaf.inj (Option.some.inj (hwπ.symm.trans hR)))
      have hne0 : πw ≠ π₀ := by
        intro he
        rw [he] at hwπ
        exact absurd (hwπ.symm.trans hs) (by simp)
      have hdiv1 : ∀ q, (π₀ ++ [true]) ++ q ≠ πw := fun q hq =>
        hneL (leafPos_prefix t (π₀ ++ [true]) πw a (.leaf w) hL hwπ q hq).symm
      have hdiv2 : ∀ q, πw ++ q ≠ (π₀ ++ [true]) := fun q hq =>
        hneL (leafPos_prefix t πw (π₀ ++ [true]) w (.leaf a) hwπ hL q hq)
      have hdiv0 : ∀ q, πw ++ q ≠ π₀ := fun q hq =>
        hne0 (leafPos_prefix t πw π₀ w (WTree.node (.leaf a) (.leaf b)) hwπ hs q hq)
      have hdiv0' : ∀ q, π₀ ++ q ≠ πw := by
        intro q hq
        rw [← hq, subtreeAt_congr t π₀ q (WTree.node (.leaf a) (.leaf b)) hs] at hwπ
        cases q with
        | nil =>
            exact hne0 (by simpa only [List.append_nil] using hq.symm)
        | cons go q' =>
            cases go with
            | true =>
                simp only [subtreeAt] at hwπ
                cases q' with
                | nil => exact hwa (WTree.leaf.inj (Option.some.inj hwπ)).symm
                | cons g2 q'' => simp [subtreeAt] at hwπ
            | false =>
                simp only [subtreeAt] at hwπ
                cases q' with
                | nil => exact hwb (WTree.leaf.inj (Option.some.inj hwπ)).symm
                | cons g2 q'' => simp [subtreeAt] at hwπ
      have hkeep2 : subtreeAt (replaceAt t (π₀ ++ [true]) w) πw = some (.leaf w) :=
        (subtreeAt_replaceAt_ne t (π₀ ++ [true]) πw a w hL hneL hdiv1 hdiv2).trans hwπ
      have hu0 : subtreeAt (replaceAt t (π₀ ++ [true]) w) π₀
          = some (WTree.node (.leaf w) (.leaf b)) :=
        subtreeAt_parent_left t π₀ a w (.leaf b) hs
      have hkeep0 : subtreeAt (replaceAt (replaceAt t (π₀ ++ [true]) w) πw a) π₀
          = subtreeAt (replaceAt t (π₀ ++ [true]) w) π₀ :=
        subtreeAt_replaceAt_ne (replaceAt t (π₀ ++ [true]) w) πw π₀ w a hkeep2 hne0.symm
          hdiv0 hdiv0'
      have hwa_le : w ≤ a := hmin a mema
      have hlen_le : πw.length ≤ (π₀ ++ [true]).length :=
        le_trans (pathLen_le_maxDepth t πw (.leaf w) hwπ) (by omega)
      have hmd1 := maxDepth_replaceAt t (π₀ ++ [true]) a w hL
      have hmd2 := maxDepth_replaceAt (replaceAt t (π₀ ++ [true]) w) πw w a hkeep2
      have hp1 := leafWeights_replaceAt t (π₀ ++ [true]) a w hL
      have hp2 := leafWeights_replaceAt (replaceAt t (π₀ ++ [true]) w) πw w a hkeep2
      refine ⟨exchPos t (π₀ ++ [true]) πw a w, π₀, b,
        hp2.trans ((List.Perm.append_right [a] (hp1.erase w)).trans
          (perm_double_exch (leafWeights t) a w mema)),
        costW_exchPos_le t (π₀ ++ [true]) πw a w hL hwπ hneL.symm hwa_le hlen_le,
        by simp only [exchPos]; rw [hkeep0]; exact hu0, ?_⟩
      simp only [exchPos]
      omega

/-! ## Ancres du carnet 02 : la maille 21 → 19 -/

/- Le minimum 1 de la maille 21 (profondeur 1) descend dans la paire (2, 4)
à la profondeur maximale 3 : la facture positionnelle rend
21 − (2−1)·(3−1) = 19. -/
#eval costW (exchPos desequilibre [false, false, true] [true] 2 1)
-- 19

example : costW (exchPos desequilibre [false, false, true] [true] 2 1) = 19 := by
  decide

/-- Le théorème vit sur la maille du carnet : un arbre de coût ≤ 21 porte le
poids 1 dans une paire de sœurs à la profondeur maximale. -/
example : ∃ (t' : WTree) (c : ℕ),
    costW t' ≤ costW desequilibre ∧
    ∃ π : List Bool, subtreeAt t' π = some (WTree.node (.leaf 1) (.leaf c)) ∧
      π.length + 1 = maxDepth t' := by
  obtain ⟨t', π, c, _, h1, h2, h3⟩ :=
    min_to_bottom desequilibre ⟨_, _, rfl⟩ 1 (by decide) (by decide)
  exact ⟨t', c, h1, π, h2, h3⟩

end CompressionLean
