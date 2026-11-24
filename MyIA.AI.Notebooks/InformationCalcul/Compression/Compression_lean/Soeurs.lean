/-
# Sœurs — paires profondes et échange de deux feuilles (pli 5f de #18706)

La dernière marche avant le théorème d'optimalité parle de POSITIONS, pas de
poids : « la feuille au bout de ce chemin » désigne une feuille unique, même
quand deux feuilles portent le même poids (le trie de Huffman de `[1, 1, 2, 4]`
a deux feuilles de poids 1 — un lemme énoncé sur « la feuille de poids x »
pourrait viser la mauvaise). Ce module pose l'adressage positionnel :
`subtreeAt` (le sous-arbre au bout d'un chemin), `replaceAt` (remplacer la
feuille visée), et leur facture — l'écart de poids fois la profondeur
(`costW_replaceAt_eq`, miroir positionnel de `costW_swapW_eq` : la cible paie
à chaque nœud ancêtre, donc exactement `π.length` fois).

Puis la paire de sœurs la plus profonde : `sisterPath` descend toujours vers
l'enfant le plus profond jusqu'à un nœud dont les deux enfants sont des
feuilles ; `sisterPath_spec` garantit qu'une telle paire existe EXACTEMENT à
la profondeur maximale — le réceptacle où le théorème d'optimalité voudra
voir vivre les deux minima.

Enfin l'échange de deux feuilles par poids, en un seul parcours (`exchangeW`)
— là où la composition de deux `swapW` dépendrait de l'ordre du parcours dès
que le remplaçant égale l'autre cible (échanger 4 et 1 : le premier `swapW`
déposerait un 1 que le second trouverait avant l'original) — et sa facture
(`costW_exchangeW_eq`), dont le corollaire strict (`costW_exchangeW_lt`)
relit l'inégalité de réarrangement du pli 5c sur l'arbre : échanger un poids
fort profond contre un poids léger superficiel diminue STRICTEMENT le coût.

Ancres du carnet `Compression-02` : sur l'arbre déséquilibré de la maille 21
(pli 5b), l'échange du poids 4 (profondeur 3) contre le poids 1 (profondeur
1) rend 21 − (4−1)·(3−1) = 15, puis l'échange du poids 2 (profondeur 3)
contre le poids 1 (profondeur 2) rend 14 — la descente complète
21 → 15 → 14 du carnet, jusqu'au coût du trie de Huffman.
-/
import Feuilles

namespace CompressionLean

/-! ## Adresser une feuille par son chemin -/

/-- Le sous-arbre au bout d'un chemin depuis la racine — `true` = enfant
gauche, `false` = enfant droit. `none` si le chemin quitte l'arbre. -/
def subtreeAt : WTree → List Bool → Option WTree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node l _, true :: π => subtreeAt l π
  | .node _ r, false :: π => subtreeAt r π

/-- Remplacer la feuille au bout du chemin par une feuille de poids `y`.
Hors cible — chemin invalide, ou nœud interne en bout de course — l'arbre
est inchangé : les lemmes ne lisent `replaceAt` que sous hypothèse de
cible-feuille, où la garde ne joue pas. -/
def replaceAt : WTree → List Bool → ℕ → WTree
  | .leaf _, [], y => .leaf y
  | .leaf v, _ :: _, _ => .leaf v
  | .node l r, [], _ => .node l r
  | .node l r, true :: π, y => .node (replaceAt l π y) r
  | .node l r, false :: π, y => .node l (replaceAt r π y)

/-- Le poids total paie exactement l'écart (forme sans soustraction). -/
theorem weight_replaceAt : ∀ (t : WTree) (π : List Bool) (x y : ℕ),
    subtreeAt t π = some (.leaf x) →
    weight (replaceAt t π y) + x = weight t + y := by
  intro t
  induction t with
  | leaf w =>
      intro π x y h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          simp only [replaceAt, weight]
          omega
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x y h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have h1 := ihl π' x y h
              simp only [replaceAt, weight]
              omega
          | false =>
              simp only [subtreeAt] at h
              have h1 := ihr π' x y h
              simp only [replaceAt, weight]
              omega

/-- **Facture positionnelle : remplacer la feuille au bout du chemin facture
l'écart à chaque nœud ancêtre — exactement la longueur du chemin.** Tous les
autres termes de `costW` sont inchangés : la cible de chemin `π` paie son
poids `π.length` fois, comme dans la facture par profondeur de `costW_swapW_eq`
(`depthOf` compte les mêmes arêtes). La feuille-racine, elle, ne paie rien —
aucun nœud au-dessus. -/
theorem costW_replaceAt_eq : ∀ (t : WTree) (π : List Bool) (x y : ℕ),
    subtreeAt t π = some (.leaf x) →
    costW (replaceAt t π y) + x * π.length = costW t + y * π.length := by
  intro t
  induction t with
  | leaf w =>
      intro π x y h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at h
          subst h
          simp [replaceAt, costW]
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π x y h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have h1 := ihl π' x y h
              have h2 := weight_replaceAt l π' x y h
              simp only [replaceAt, costW, List.length_cons, Nat.mul_add]
              omega
          | false =>
              simp only [subtreeAt] at h
              have h1 := ihr π' x y h
              have h2 := weight_replaceAt r π' x y h
              simp only [replaceAt, costW, List.length_cons, Nat.mul_add]
              omega

/-! ## La paire de sœurs la plus profonde -/

/-- Le chemin vers la première paire de feuilles sœurs à profondeur
maximale : descendre vers l'enfant le plus profond (à gauche en cas
d'égalité) ; l'enfant atteint n'est contourné que si c'est une feuille — et
alors son frère l'est aussi (la hauteur ne dépasse pas la sienne), et la
paire est trouvée. Sur une feuille isolée, le chemin vide (cas dégénéré,
hors hypothèse des lemmes). -/
def sisterPath : WTree → List Bool
  | .leaf _ => []
  | .node l r =>
      if maxDepth l ≥ maxDepth r then
        match l with
        | .leaf _ => []
        | .node _ _ => true :: sisterPath l
      else
        match r with
        | .leaf _ => []
        | .node _ _ => false :: sisterPath r

/-- **Tout arbre qui n'est pas une feuille porte une paire de feuilles sœurs
exactement à la profondeur maximale.** Un chemin y mène : ses deux enfants
sont des feuilles, et la longueur du chemin plus un est la hauteur — le
réceptacle où le théorème d'optimalité voudra voir vivre les deux minima. -/
theorem sisterPath_spec : ∀ (t : WTree), (∃ l r, t = WTree.node l r) →
    ∃ (π : List Bool) (a b : ℕ),
      subtreeAt t π = some (WTree.node (.leaf a) (.leaf b))
        ∧ π.length + 1 = maxDepth t := by
  intro t
  induction t with
  | leaf w =>
      intro hnode
      obtain ⟨l, r, ht⟩ := hnode
      exact absurd ht (by simp)
  | node l r ihl ihr =>
      intro _
      cases l with
      | leaf w =>
          cases r with
          | leaf w' =>
              refine ⟨[], w, w', by simp [subtreeAt], ?_⟩
              simp only [List.length_nil, maxDepth, Nat.zero_max]
          | node rl rr =>
              have hn : ¬ (maxDepth (.leaf w) ≥ maxDepth (.node rl rr)) := by
                simp only [maxDepth]; omega
              obtain ⟨π, a, b, hs, hl⟩ := ihr ⟨rl, rr, rfl⟩
              refine ⟨false :: π, a, b, ?_, ?_⟩
              · simp only [subtreeAt]
                exact hs
              · have hmax : maxDepth (WTree.node (.leaf w) (.node rl rr))
                    = 1 + maxDepth (.node rl rr) := by
                  simp only [maxDepth, Nat.zero_max]
                simp only [List.length_cons]
                omega
      | node ll lr =>
          cases r with
          | leaf w' =>
              have hp : maxDepth (.node ll lr) ≥ maxDepth (.leaf w') := by
                simp only [maxDepth]; omega
              obtain ⟨π, a, b, hs, hl⟩ := ihl ⟨ll, lr, rfl⟩
              refine ⟨true :: π, a, b, ?_, ?_⟩
              · simp only [subtreeAt]
                exact hs
              · have hmax : maxDepth (WTree.node (.node ll lr) (.leaf w'))
                    = 1 + maxDepth (.node ll lr) := by
                  simp only [maxDepth, Nat.max_zero]
                simp only [List.length_cons]
                omega
          | node rl rr =>
              by_cases hge : maxDepth (.node ll lr) ≥ maxDepth (.node rl rr)
              · obtain ⟨π, a, b, hs, hl⟩ := ihl ⟨ll, lr, rfl⟩
                refine ⟨true :: π, a, b, ?_, ?_⟩
                · simp only [subtreeAt]
                  exact hs
                · have hmax : maxDepth (WTree.node (.node ll lr) (.node rl rr))
                      = 1 + maxDepth (.node ll lr) := by
                    conv_lhs => rw [maxDepth]
                    rw [Nat.max_eq_left hge]
                  simp only [List.length_cons]
                  omega
              · obtain ⟨π, a, b, hs, hl⟩ := ihr ⟨rl, rr, rfl⟩
                refine ⟨false :: π, a, b, ?_, ?_⟩
                · simp only [subtreeAt]
                  exact hs
                · have hmax : maxDepth (WTree.node (.node ll lr) (.node rl rr))
                      = 1 + maxDepth (.node rl rr) := by
                    conv_lhs => rw [maxDepth]
                    rw [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hge))]
                  simp only [List.length_cons]
                  omega

/-! ## L'échange de deux feuilles par poids, en un parcours -/

/-- Remplacer la première feuille de poids `x` par une feuille de poids `a`
ET la première feuille de poids `y` par une feuille de poids `b`, en un seul
parcours. Les cas croisés (x d'un côté, y de l'autre) délèguent chaque côté
à `swapW` pour sa cible — la composition naïve de deux `swapW` dépendrait de
l'ordre du parcours dès que le remplaçant égale l'autre cible. -/
def exchangeW : WTree → ℕ → ℕ → ℕ → ℕ → WTree
  | .leaf w, x, y, a, b =>
      if w = x then .leaf a else if w = y then .leaf b else .leaf w
  | .node l r, x, y, a, b =>
      if x ∈ leafWeights l then
        if y ∈ leafWeights l then .node (exchangeW l x y a b) r
        else .node (swapW l x a) (swapW r y b)
      else
        if y ∈ leafWeights l then .node (swapW l y b) (swapW r x a)
        else .node l (exchangeW r x y a b)

/-- Garde : hors seconde cible, l'échange dégénère en substitution simple. -/
theorem exchangeW_swapW : ∀ (t : WTree) (x y a b : ℕ), y ∉ leafWeights t →
    exchangeW t x y a b = swapW t x a := by
  intro t
  induction t with
  | leaf w =>
      intro x y a b hy
      by_cases hx : w = x
      · rw [hx] at hy ⊢
        simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at hy
        simp only [exchangeW, swapW, if_true]
      · have hw : w ≠ y := by
          intro hwy
          apply hy
          simp only [leafWeights, hwy, List.mem_cons, List.not_mem_nil, or_false]
        simp only [exchangeW, swapW, if_neg hx, if_neg hw]
  | node l r ihl ihr =>
      intro x y a b hy
      simp only [exchangeW, swapW]
      by_cases hxl : x ∈ leafWeights l
      · have hyl : y ∉ leafWeights l := fun hm =>
          hy (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inl hm))
        have hyr : y ∉ leafWeights r := fun hm =>
          hy (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inr hm))
        simp only [if_pos hxl, if_neg hyl, swapW_self r y b hyr]
      · by_cases hyl : y ∈ leafWeights l
        · exact absurd hyl (fun hm =>
            hy (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inl hm)))
        · have hyr : y ∉ leafWeights r := fun hm =>
            hy (by simp only [leafWeights]; exact List.mem_append.mpr (Or.inr hm))
          simp only [if_neg hxl, if_neg hyl]
          exact congrArg (fun s => WTree.node l s) (ihr x y a b hyr)

/-- Le poids total paie exactement les deux écarts (forme sans
soustraction). -/
theorem weight_exchangeW : ∀ (t : WTree) (x y a b : ℕ),
    x ∈ leafWeights t → y ∈ leafWeights t → x ≠ y →
    weight (exchangeW t x y a b) + x + y = weight t + a + b := by
  intro t
  induction t with
  | leaf w =>
      intro x y a b hx hy hne
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      exact absurd (hx.trans hy.symm) hne
  | node l r ihl ihr =>
      intro x y a b h hy hne
      simp only [leafWeights, List.mem_append] at h hy
      by_cases hxl : x ∈ leafWeights l
      · by_cases hyl : y ∈ leafWeights l
        · have h1 := ihl x y a b hxl hyl hne
          simp only [exchangeW, if_pos hxl, if_pos hyl, weight]
          omega
        · have hyr : y ∈ leafWeights r := by
            rcases hy with hm | hm
            · exact absurd hm hyl
            · exact hm
          have hw1 := weight_swapW l x a hxl
          have hw2 := weight_swapW r y b hyr
          simp only [exchangeW, if_pos hxl, if_neg hyl, weight]
          omega
      · have hxr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hxl
          · exact hm
        by_cases hyl : y ∈ leafWeights l
        · have hw1 := weight_swapW l y b hyl
          have hw2 := weight_swapW r x a hxr
          simp only [exchangeW, if_neg hxl, if_pos hyl, weight]
          omega
        · have hyr : y ∈ leafWeights r := by
            rcases hy with hm | hm
            · exact absurd hm hyl
            · exact hm
          have h1 := ihr x y a b hxr hyr hne
          simp only [exchangeW, if_neg hxl, if_neg hyl, weight]
          omega

/-- **Facture de l'échange : chaque cible paie l'écart de poids à SA
profondeur.** Remplacer la première feuille de poids `x` (à profondeur
`depthOf t x`) par `a` et la première de poids `y` par `b` facture
`x·dₓ → a·dₓ` et `y·d_y → b·d_y`, tous les autres termes inchangés. -/
theorem costW_exchangeW_eq : ∀ (t : WTree) (x y a b : ℕ),
    x ∈ leafWeights t → y ∈ leafWeights t → x ≠ y →
    costW (exchangeW t x y a b) + x * depthOf t x + y * depthOf t y
      = costW t + a * depthOf t x + b * depthOf t y := by
  intro t
  induction t with
  | leaf w =>
      intro x y a b hx hy hne
      simp only [leafWeights, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      exact absurd (hx.trans hy.symm) hne
  | node l r ihl ihr =>
      intro x y a b h hy hne
      simp only [leafWeights, List.mem_append] at h hy
      by_cases hxl : x ∈ leafWeights l
      · by_cases hyl : y ∈ leafWeights l
        · have h1 := ihl x y a b hxl hyl hne
          have hw := weight_exchangeW l x y a b hxl hyl hne
          simp only [exchangeW, if_pos hxl, if_pos hyl, costW, depthOf, Nat.mul_add]
          omega
        · have hyr : y ∈ leafWeights r := by
            rcases hy with hm | hm
            · exact absurd hm hyl
            · exact hm
          have h1 := costW_swapW_eq l x a hxl
          have h2 := costW_swapW_eq r y b hyr
          have hw1 := weight_swapW l x a hxl
          have hw2 := weight_swapW r y b hyr
          simp only [exchangeW, if_pos hxl, if_neg hyl, costW, depthOf, Nat.mul_add]
          omega
      · have hxr : x ∈ leafWeights r := by
          rcases h with hm | hm
          · exact absurd hm hxl
          · exact hm
        by_cases hyl : y ∈ leafWeights l
        · have h1 := costW_swapW_eq l y b hyl
          have h2 := costW_swapW_eq r x a hxr
          have hw1 := weight_swapW l y b hyl
          have hw2 := weight_swapW r x a hxr
          simp only [exchangeW, if_neg hxl, if_pos hyl, costW, depthOf, Nat.mul_add]
          omega
        · have hyr : y ∈ leafWeights r := by
            rcases hy with hm | hm
            · exact absurd hm hyl
            · exact hm
          have h1 := ihr x y a b hxr hyr hne
          have hw := weight_exchangeW r x y a b hxr hyr hne
          simp only [exchangeW, if_neg hxl, if_neg hyl, costW, depthOf, Nat.mul_add]
          omega

/-- **L'inégalité de réarrangement du pli 5c lue sur l'arbre : échanger un
poids fort profond contre un poids léger superficiel diminue STRICTEMENT le
coût.** L'écart exact est le produit des écarts `(x − y)·(dₓ − d_y)` —
l'ingrédient de la descente du théorème d'optimalité : tant que les minima
ne sont pas en bas, l'échange strictement améliore. -/
theorem costW_exchangeW_lt : ∀ (t : WTree) (x y : ℕ),
    y < x → x ≠ y → x ∈ leafWeights t → y ∈ leafWeights t →
    depthOf t y < depthOf t x →
    costW (exchangeW t x y y x) < costW t := by
  intro t x y hlt hne hx hy hd
  have h1 := costW_exchangeW_eq t x y y x hx hy hne
  obtain ⟨k, hk⟩ : ∃ k, x = y + k := ⟨x - y, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, depthOf t x = depthOf t y + m :=
    ⟨depthOf t x - depthOf t y, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hm1 : 1 ≤ m := by omega
  have hkm : 1 ≤ k * m := Nat.mul_le_mul hk1 hm1
  simp only [hm] at h1
  simp only [hk, Nat.mul_add, Nat.add_mul] at h1 ⊢
  omega

/-! ## Ancres du carnet 02 : la descente 21 → 15 → 14 -/

/- Le chemin de la paire la plus profonde de l'arbre déséquilibré : deux
descentes à droite vers les feuilles 2 et 4, à la profondeur maximale 3. -/
#eval sisterPath desequilibre
-- [false, false]

#eval (sisterPath desequilibre).length + 1
-- 3

/-- La première maille : échanger le poids 4 (profondeur 3) contre le poids 1
(profondeur 1) rend 21 − (4−1)·(3−1) = 15. -/
example : costW (exchangeW desequilibre 4 1 1 4) = 15 := by decide

/-- La seconde maille : échanger le poids 2 (profondeur 3) contre le poids 1
(profondeur 2) rend 14 — la descente complète 21 → 15 → 14 du carnet 02,
jusqu'au coût du trie de Huffman pour [1, 1, 2, 4]. -/
example : costW (exchangeW (exchangeW desequilibre 4 1 1 4) 2 1 1 2) = 14 := by decide

/-- La seconde maille par le corollaire strict : le poids 2 vit à la
profondeur 3, le poids 1 à la profondeur 2 — l'échange améliore strictement. -/
example : costW (exchangeW (exchangeW desequilibre 4 1 1 4) 2 1 1 2)
    < costW (exchangeW desequilibre 4 1 1 4) :=
  costW_exchangeW_lt
    (exchangeW desequilibre 4 1 1 4) 2 1
    (by decide) (by decide)
    (by decide) (by decide)
    (by decide)

end CompressionLean
