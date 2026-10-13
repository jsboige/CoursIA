import Mathlib

/-!
# PrefixCodes — codes préfixes et inégalité de Kraft (pli 1/2, EPIC #18706)

Formalisation Lean du socle théorique de la série **Compression** : un code
préfixe binaire est l'ensemble des feuilles d'un arbre binaire fini, et la
**somme de Kraft** de ses mots — `Σ w, 2 ^ (- |w|)` — ne dépasse jamais `1`
(inégalité de Kraft). C'est la contrainte exacte qu'équilibrent le code de
Shannon–Fano (pli 1, `Compression-01-ShannonFano-Prefixe-Python.ipynb`) et le
code de Huffman canonique (pli 2, `Compression-02-HuffmanCanonique`), et la
raison pour laquelle un code préfixe ne peut pas raccourcir tous ses mots à la
fois : chaque bit économisé quelque part doit être payé ailleurs.

Tranche formalisation du jumeau Lean de l'EPIC **#18706** (décision D4 : lake
dédié `Compression_lean`, mathlib seule). Contenu distillé :

1. **Arbres de codes** (`CodeTree`) : un code binaire est vu comme un arbre
   fini — chaque feuille est un mot du code (`leafWords`), chaque arête un bit
   (`true` = gauche, `false` = droite). C'est la même structure que la coupe
   récursive de Shannon–Fano du carnet Python : couper la liste des symboles
   en deux moitiés de probabilité ~ égale, c'est construire `node l r`.
2. **Les feuilles forment un code préfixe** (`leafWords_prefixFree`) : deux
   mots distincts de feuilles ne sont jamais préfixes l'un de l'autre — un
   décodage préfixe n'est jamais ambigu. Preuve structurelle : deux feuilles
   d'un même sous-arbre héritent de la propriété par induction ; deux feuilles
   de sous-arbres différents divergent au premier bit.
3. **Inégalité de Kraft** (`kraft_le_one`) : `kraftSum t ≤ 1`, sur les
   rationnels exacts. Preuve : une feuille isolée pèse `1` ; un `node l r`
   divise chaque poids par `2` (un bit de plus par mot), donc
   `kraftSum (node l r) = kraftSum l / 2 + kraftSum r / 2 ≤ 1`. Chaque étage
   de l'arbre partage le même budget total — exactement le « partage du
   gâteau » binaire illustré par le diagramme en bâtons du carnet 01.
4. **Arbre complet** (`full k`) : l'arbre équilibré de profondeur `k` porte
   `2 ^ k` feuilles (`length_leafWords_full`) toutes de longueur `k`, et sa
   somme de Kraft vaut exactement `1` (`kraft_full`) : le code à longueur
   fixe de `2 ^ k` symboles (le code « naïf » du pli 1) sature la borne.
   Ancres numériques `#eval` : le code fixe 2 bits et le code de longueurs
   `(1, 2, 3, 3)` (lettres `a=0, b=10, c=110, d=111` du carnet) saturent
   aussi exactement `1`.

Roadmap (plis suivants de #18706, hors de cette tranche) : le théorème de
McMillan (réciproque — si `Σ 2 ^ (-ℓᵢ) ≤ 1` alors un code préfixe de ces
longueurs existe), le trie de décodage (tout code préfixe fini est l'ensemble
de feuilles d'un arbre), et l'optimalité de Huffman.

Sibling EN : `PrefixCodes_en.lean` (namespace `CompressionLean_en`), mêmes
énoncés et preuves, docstrings traduites — convention i18n #4980 pattern A.
-/

namespace CompressionLean

/-- Un arbre de code binaire fini : une feuille (mot vide) ou un nœud à deux
enfants (`true` = enfant gauche, `false` = enfant droit). -/
inductive CodeTree where
  /-- Feuille : fin d'un mot du code. -/
  | leaf : CodeTree
  /-- Nœud interne : les deux sous-arbres. -/
  | node : CodeTree → CodeTree → CodeTree
  deriving Repr

/-- `leafWords t` : la liste des mots binaires des feuilles de `t`, en
profondeur d'abord gauche. Chaque mot est l'arête-chemin de la racine à la
feuille : c'est le code lui-même. -/
def leafWords : CodeTree → List (List Bool)
  | .leaf => [[]]
  | .node l r => (leafWords l).map (true :: ·) ++ (leafWords r).map (false :: ·)

/-- `PrefixOf w v` : `w` est un préfixe de `v` (il existe un suffixe `t` tel
que `v = w ++ t`). Relation auto-contenue : elle évite de dépendre de la
définition par match de `List.IsPrefix` de Mathlib. -/
def PrefixOf (w v : List Bool) : Prop := ∃ t, v = w ++ t

/-- Un « code préfixe » : liste de mots dans laquelle aucun mot n'est un
préfixe d'un autre mot distinct — le décodage glouton est donc non ambigu. -/
def IsPrefixFree (C : List (List Bool)) : Prop :=
  ∀ w ∈ C, ∀ v ∈ C, PrefixOf w v → w = v

/-! ## Le lemme de propagation du préfixe -/

/-- Si `b :: w` est préfixe de `c :: v` alors les bits sont égaux et `w` est
préfixe de `v`. C'est la brique des sous-cas du théorème 1. -/
theorem prefixOf_cons {b c : Bool} {w v : List Bool}
    (h : PrefixOf (b :: w) (c :: v)) : b = c ∧ PrefixOf w v := by
  obtain ⟨t, ht⟩ := h
  injection ht with hbc hvt
  exact ⟨hbc.symm, ⟨t, hvt⟩⟩

/-! ## Théorème 1 : les feuilles d'un arbre forment un code préfixe -/

/-- **Les mots des feuilles d'un arbre forment toujours un code préfixe.**
Un décodeur glouton qui lit l'arbre feuille par feuille ne peut jamais
tomber sur une ambiguïté : deux mots distincts de feuilles divergent quelque
part et ne se préfixent jamais mutuellement. -/
theorem leafWords_prefixFree (t : CodeTree) : IsPrefixFree (leafWords t) := by
  induction t with
  | leaf =>
      intro w hw v hv _
      simp only [leafWords, List.mem_singleton] at hw hv
      rw [hw, hv]
  | node l r ihl ihr =>
      intro w hw v hv hp
      simp only [leafWords, List.mem_append, List.mem_map] at hw hv
      obtain ⟨w', hw', hw_eq⟩ | ⟨w', hw', hw_eq⟩ := hw
      · -- `w = true :: w'` : le mot vient du sous-arbre gauche
        obtain ⟨v', hv', hv_eq⟩ | ⟨v', hv', hv_eq⟩ := hv
        · -- `v = true :: v'` : les deux viennent de gauche
          subst hw_eq; subst hv_eq
          exact congrArg (fun x => true :: x) (ihl w' hw' v' hv' (prefixOf_cons hp).2)
        · -- `v = false :: v'` : divergence au premier bit
          subst hw_eq; subst hv_eq
          exact absurd (prefixOf_cons hp).1 (by decide)
      · -- `w = false :: w'` : le mot vient du sous-arbre droit
        obtain ⟨v', hv', hv_eq⟩ | ⟨v', hv', hv_eq⟩ := hv
        · -- `v = true :: v'` : divergence au premier bit
          subst hw_eq; subst hv_eq
          exact absurd (prefixOf_cons hp).1 (by decide)
        · -- `v = false :: v'` : les deux viennent de droite
          subst hw_eq; subst hv_eq
          exact congrArg (fun x => false :: x) (ihr w' hw' v' hv' (prefixOf_cons hp).2)

/-! ## La somme de Kraft -/

/-- `kraftSum t` : la somme de Kraft de l'arbre — chaque mot de code `w`
contribue `1 / 2 ^ |w|`. Sur les rationnels exacts, donc évaluable (`#eval`). -/
def kraftSum (t : CodeTree) : ℚ :=
  ((leafWords t).map fun w => (1 : ℚ) / 2 ^ w.length).sum

/-- Étape-clé de la récurrence de Kraft : ajouter un bit à tous les mots d'un
code divise sa somme de Kraft par exactement `2`. -/
theorem sum_map_bit_halves {b : Bool} {L : List (List Bool)} :
    ((L.map (b :: ·)).map fun w => (1 : ℚ) / 2 ^ w.length).sum
      = (1 / 2) * ((L.map fun w => (1 : ℚ) / 2 ^ w.length).sum) := by
  induction L with
  | nil => simp
  | cons w L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      have hstep : (1 : ℚ) / 2 ^ ((w.length : ℕ) + 1)
          = (1 / 2) * ((1 : ℚ) / 2 ^ w.length) := by
        rw [pow_succ]
        field_simp
      rw [hstep]
      ring

/-- Récurrence de la somme de Kraft sur un nœud : un bit de plus par mot
divise chaque côté par `2`. -/
theorem kraftSum_node (l r : CodeTree) :
    kraftSum (.node l r) = kraftSum l / 2 + kraftSum r / 2 := by
  simp only [kraftSum, leafWords, List.map_append, List.sum_append]
  rw [sum_map_bit_halves, sum_map_bit_halves]
  ring

/-! ## Théorème 2 : l'inégalité de Kraft -/

/-- **Inégalité de Kraft** : la somme de Kraft d'un code préfixe (vu comme
arbre) ne dépasse jamais `1`. Chaque feuille consomme une part du budget
unitaire `2 ^ (- |w|)` et les parts ne se chevauchent jamais. C'est la
contrainte que Shannon–Fano (pli 1) et Huffman (pli 2) saturent à l'optimum. -/
theorem kraft_le_one (t : CodeTree) : kraftSum t ≤ 1 := by
  induction t with
  | leaf =>
      simp only [kraftSum, leafWords, List.map_cons, List.sum_cons,
        List.length_nil, pow_zero, div_one]
      norm_num
  | node l r ihl ihr =>
      rw [kraftSum_node, div_eq_mul_one_div, div_eq_mul_one_div]
      have m1 : kraftSum l * ((1 : ℚ) / 2) ≤ 1 * ((1 : ℚ) / 2) :=
        mul_le_mul_of_nonneg_right ihl (by norm_num)
      have m2 : kraftSum r * ((1 : ℚ) / 2) ≤ 1 * ((1 : ℚ) / 2) :=
        mul_le_mul_of_nonneg_right ihr (by norm_num)
      linarith

/-! ## Théorème 3 : l'arbre complet sature exactement la borne -/

/-- `full k` : l'arbre binaire complet de profondeur `k` — le code à longueur
fixe de `2 ^ k` symboles (le code « naïf » du pli 1 du carnet Python). -/
def full : ℕ → CodeTree
  | 0 => .leaf
  | (k + 1) => .node (full k) (full k)

/-- L'arbre complet de profondeur `k` porte exactement `2 ^ k` feuilles. -/
theorem length_leafWords_full (k : ℕ) : (leafWords (full k)).length = 2 ^ k := by
  induction k with
  | zero => simp [leafWords, full]
  | succ k ih =>
      simp only [full, leafWords, List.length_append, List.length_map, ih]
      rw [pow_succ]
      omega

/-- La somme de Kraft de l'arbre complet vaut **exactement** `1` : le code à
longueur fixe sature la borne de Kraft. -/
theorem kraft_full (k : ℕ) : kraftSum (full k) = 1 := by
  induction k with
  | zero =>
      simp only [kraftSum, leafWords, full, List.map_cons, List.sum_cons,
        List.length_nil, pow_zero, div_one]
      norm_num
  | succ k ih =>
      have hf : full (k + 1) = CodeTree.node (full k) (full k) := rfl
      rw [hf, kraftSum_node, ih]
      norm_num

/-! ## Ancres numériques (exécutables) -/

/-- Le code fixe 2 bits (4 symboles) : `full 2`. -/
def fixed2 : CodeTree := full 2

/-- Le code des longueurs `(1, 2, 3, 3)` — lettres `a=0, b=10, c=110,
d=111` du carnet 01 (Shannon–Fano sur la distribution `1/2, 1/4, 1/8, 1/8`). -/
def sf4 : CodeTree := .node .leaf (.node .leaf (.node .leaf .leaf))

/-- Ancre : le code fixe 2 bits sature exactement Kraft. -/
example : kraftSum fixed2 = 1 := kraft_full 2

/-- Ancre : le code `(1, 2, 3, 3)` sature exactement Kraft
(`1/2 + 1/4 + 1/8 + 1/8 = 1`). -/
example : kraftSum sf4 = 1 := by
  have h1 : kraftSum (CodeTree.node .leaf .leaf) = 1 := kraft_full 1
  have h0 : kraftSum CodeTree.leaf = 1 := kraft_full 0
  simp only [sf4]
  rw [kraftSum_node, kraftSum_node, h0, h1]
  norm_num

#eval kraftSum fixed2  -- (1 : ℚ)
#eval kraftSum sf4     -- (1 : ℚ)
#eval (leafWords sf4).map List.length  -- [1, 2, 3, 3]

end CompressionLean
