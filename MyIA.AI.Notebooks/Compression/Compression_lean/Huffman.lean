import Mathlib
import PrefixCodes
import McMillan

/-!
# Huffman — le trie canonique depuis les fréquences (pli 4, EPIC #18706)

Les plis 1 et 3 (`PrefixCodes.lean`, `McMillan.lean`) ont établi le cadre :
un code préfixe vit sur un arbre (inégalité de Kraft), et toute bande de
longueurs admissible est **réalisée** par le code canonique (réciproque de
McMillan). Ce module boucle le circuit du carnet Python
`Compression-02-HuffmanCanonique` : partir des **fréquences**, construire le
**trie de Huffman** — l'arbre obtenu en fusionnant itérativement les deux
symboles de plus petites fréquences —, lire ses **profondeurs**, et rendre le
**code canonique** de ces profondeurs.

La chaîne complète :

1. **Arbres pondérés** (`WTree`) : chaque feuille porte la fréquence d'un
   symbole ; `depthsW` lit la bande de longueurs du code porté par l'arbre ;
   `toCodeTree` oublie les poids et rend l'arbre de codes du pli 1 — dont les
   feuilles forment un code préfixe (`leafWords_prefixFree`, théorème 1 du
   pli 1, invoqué tel quel).
2. **Kraft sur les profondeurs** (`mass_depths_le`) : la masse à l'échelle
   `2 ^ L` des profondeurs d'un arbre ne dépasse jamais `2 ^ L` — l'inégalité
   de Kraft du pli 1, redémontrée à l'échelle entière du pli 3 : un nœud
   ajoute un bit à chaque mot, donc divise chaque part du budget par `2`.
3. **Tri et masse** (`isort`, `mass_perm`) : le code canonique exige des
   longueurs **triées croissantes** ; le tri par insertion est une
   permutation, et la masse ne dépend que du multi-ensemble des longueurs.
4. **La construction de Huffman** (`insertT`, `build`, `huffman`) : la forêt
   de feuilles triée par poids ; chaque étape de `build` fusionne les deux
   arbres de plus petits poids (`sorted_two_min` — sur une forêt triée, les
   deux têtes sont bien les deux minima) et réinsère le résultat à sa place.
   Le poids total se conserve (`weight_build`) : la masse du code final est
   la somme des fréquences d'entrée.
5. **Le théorème capital** (`huffman_canonical`) : pour toute liste de
   fréquences, le code canonique des profondeurs du trie de Huffman existe et
   est préfixe-libre — obtenu en invoquant `mcmillan_converse` (pli 3) sur
   les profondeurs triées, dont l'admissibilité est le point 2.
6. Ancres `#eval` : les fréquences `1, 1, 2, 4` du carnet 02 — l'arbre de
   Huffman rend les profondeurs `[3, 3, 2, 1]`, le tri `[1, 2, 3, 3]`, et le
   code canonique `a = 0, b = 10, c = 110, d = 111` : exactement le code du
   carnet.

La question de l'**optimalité** — pourquoi fusionner les deux plus petits
donne le code de coût minimal — est le pli suivant de la roadmap ; ce module
établit la correction structurelle de la construction (forêt triée, fusion
des minima, conservation du poids) et l'existence du code canonique.

Sibling EN : `Huffman.lean` est FR-only à la livraison (même convention que
`Decode`/`McMillan` — la flotte i18n est drained, cf
`scripts/lean/check_i18n_siblings.py`).
-/

namespace CompressionLean

/-! ## Arbres pondérés et profondeurs -/

/-- Arbre binaire pondéré : chaque feuille porte la fréquence d'un symbole.
Le poids d'un nœud n'est pas étiqueté : il se calcule (`weight`), ce qui
évite de porter un invariant d'étiquette. -/
inductive WTree where
  /-- Feuille : un symbole de fréquence `w`. -/
  | leaf (w : ℕ) : WTree
  /-- Nœud interne : les deux sous-arbres. -/
  | node : WTree → WTree → WTree
  deriving Repr

/-- Poids d'un arbre : fréquence de la feuille, somme des poids des
sous-arbres. C'est le coût total du code : chaque feuille de profondeur `d`
paie son mot bit à bit. -/
def weight : WTree → ℕ
  | .leaf w => w
  | .node l r => weight l + weight r

/-- Profondeurs des feuilles, en profondeur d'abord gauche : la bande de
longueurs du code porté par l'arbre, dans l'ordre des mots de `leafWords`. -/
def depthsW : WTree → List ℕ
  | .leaf _ => [0]
  | .node l r => (depthsW l).map (· + 1) ++ (depthsW r).map (· + 1)

/-- Les profondeurs d'un arbre forment toujours une liste non vide. -/
theorem depthsW_ne (t : WTree) : depthsW t ≠ [] := by
  induction t with
  | leaf w => simp [depthsW]
  | node l r ihl ihr =>
      intro h
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ ihl
      simp only [depthsW] at h
      have hmem : d + 1 ∈ (depthsW l).map (· + 1) ++ (depthsW r).map (· + 1) :=
        List.mem_append_left _ (List.mem_map_of_mem hd)
      rw [h] at hmem
      exact absurd hmem (by simp)

/-- Tout élément des profondeurs d'un nœud est un successeur : descendre d'un
cran ajoute un bit, donc toute profondeur d'un sous-arbre non trivial est
`≥ 1`. -/
theorem depthsW_node_ge {l r : WTree} {d : ℕ} (h : d ∈ depthsW (.node l r)) :
    1 ≤ d := by
  simp only [depthsW, List.mem_append, List.mem_map] at h
  obtain ⟨x, hx, hxd⟩ | ⟨x, hx, hxd⟩ := h
  · subst hxd; omega
  · subst hxd; omega

/-- Oublier les poids : tout arbre pondéré est un arbre de codes du pli 1.
C'est le pont vers `leafWords` et `leafWords_prefixFree`. -/
def toCodeTree : WTree → CodeTree
  | .leaf _ => .leaf
  | .node l r => .node (toCodeTree l) (toCodeTree r)

/-- Ajouter un bit devant chaque mot ajoute `1` à chaque longueur. -/
theorem map_length_bit (b : Bool) (L : List (List Bool)) :
    (L.map (b :: ·)).map List.length = (L.map List.length).map (· + 1) := by
  simp [List.map_map, Function.comp]

/-- **Le pont de longueurs** : les mots de l'arbre de codes (pli 1) ont
exactement les profondeurs de l'arbre pondéré pour longueurs. Les deux vues
de l'arbre — mots (`leafWords ∘ toCodeTree`) et bande de longueurs
(`depthsW`) — portent la même information de longueur. -/
theorem leafWords_length_toCodeTree (t : WTree) :
    (leafWords (toCodeTree t)).map List.length = depthsW t := by
  induction t with
  | leaf w => simp [toCodeTree, leafWords, depthsW]
  | node l r ihl ihr =>
      simp only [toCodeTree, leafWords, depthsW, List.map_append]
      rw [map_length_bit, map_length_bit, ihl, ihr]

/-- **Le code porté par le trie est préfixe-libre** — invoqué du théorème 1
du pli 1 : deux mots de feuilles d'un même arbre ne se préfixent jamais.
Le trie de Huffman est un code de décodage non ambigu. -/
theorem trie_prefixFree (t : WTree) : IsPrefixFree (leafWords (toCodeTree t)) :=
  leafWords_prefixFree (toCodeTree t)

/-! ## Kraft sur les profondeurs, à l'échelle entière -/

/-- Ajouter un bit à toutes les longueurs divise la masse par `2` : passer de
`L` à `L + 1` décale chaque `2 ^ (L - ℓ)` d'un cran (forme dépliée de
`mass`, directement consommable par `simp only [mass]`). -/
theorem mass_map_succ (L : ℕ) : ∀ ds : List ℕ,
    ((ds.map (· + 1)).map (fun l => 2 ^ (L + 1 - l))).sum
      = (ds.map (fun l => 2 ^ (L - l))).sum := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show L + 1 - (d + 1) = L - d from by omega]
      rw [ih]

/-- **Kraft sur les profondeurs** : la masse à l'échelle `2 ^ L` des
profondeurs d'un arbre ne dépasse jamais `2 ^ L` dès que `L` les majore.
C'est l'inégalité de Kraft du pli 1, à l'échelle entière du pli 3 : une
feuille consomme sa part `2 ^ (L - 0)` ; un nœud ajoute un bit à chaque mot
de ses sous-arbres (`mass_map_succ`), donc consomme la moitié du budget de
chaque côté — et deux moitiés de `2 ^ L` refont `2 ^ L`. -/
theorem mass_depths_le : ∀ (t : WTree) (L : ℕ), (∀ d ∈ depthsW t, d ≤ L) →
    mass L (depthsW t) ≤ 2 ^ L := by
  intro t
  induction t with
  | leaf w =>
      intro L _
      simp only [depthsW, mass, List.map_cons, List.sum_cons, Nat.sub_zero]
      exact Nat.le_refl _
  | node l r ihl ihr =>
      intro L hbnd
      cases L with
      | zero =>
          obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (depthsW_ne (.node l r))
          have h1 := depthsW_node_ge hd
          have h0 := hbnd d hd
          omega
      | succ L' =>
          have hsplit :
              mass (L' + 1) (depthsW (.node l r))
                = mass L' (depthsW l) + mass L' (depthsW r) := by
            simp only [depthsW, mass, List.map_append, List.sum_append]
            rw [mass_map_succ, mass_map_succ]
          have hbl : ∀ d ∈ depthsW l, d ≤ L' := by
            intro d hd
            have hmem : d + 1 ∈ depthsW (.node l r) :=
              List.mem_append_left _ (List.mem_map_of_mem hd)
            have := hbnd (d + 1) hmem
            omega
          have hbr : ∀ d ∈ depthsW r, d ≤ L' := by
            intro d hd
            have hmem : d + 1 ∈ depthsW (.node l r) :=
              List.mem_append_right _ (List.mem_map_of_mem hd)
            have := hbnd (d + 1) hmem
            omega
          rw [hsplit]
          have hpow : 2 ^ (L' + 1) = 2 ^ L' + 2 ^ L' := by
            rw [Nat.pow_succ]
            ring
          rw [hpow]
          exact Nat.add_le_add (ihl L' hbl) (ihr L' hbr)

/-! ## Tri des longueurs : le tri par insertion est une permutation -/

/-- Insertion d'une longueur dans une bande triée croissante. -/
def insertN : ℕ → List ℕ → List ℕ
  | x, [] => [x]
  | x, y :: ys => if x ≤ y then x :: y :: ys else y :: insertN x ys

/-- Les éléments d'une bande insérée sont exactement l'élément inséré et les
éléments d'origine. -/
theorem mem_of_mem_insertN : ∀ (x z : ℕ) (ys : List ℕ),
    z ∈ insertN x ys → z ∈ x :: ys := by
  intro x z ys
  induction ys with
  | nil => intro h; exact h
  | cons v vs ih =>
      intro h
      by_cases hxv : x ≤ v
      · simp only [insertN, if_pos hxv] at h; exact h
      · simp only [insertN, if_neg hxv] at h
        rcases List.mem_cons.mp h with rfl | hmem
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.mp (ih hmem) with rfl | hmem'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem v hmem')

/-- Tri par insertion : la bande de longueurs que le code canonique exige. -/
def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertN x (isort xs)

theorem insertN_sorted : ∀ (x : ℕ) (ys : List ℕ), SortedLe ys →
    SortedLe (insertN x ys) := by
  intro x ys
  induction ys with
  | nil => intro _; exact List.pairwise_singleton _ _
  | cons y ys ih =>
      intro h
      by_cases hxy : x ≤ y
      · simp only [insertN, if_pos hxy]
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzmem
        · exact hxy
        · have hyz : y ≤ z := (List.pairwise_cons.mp h).1 z hzmem
          exact Nat.le_trans hxy hyz
      · simp only [insertN, if_neg hxy]
        refine List.pairwise_cons.mpr ⟨?_, ih h.tail⟩
        intro z hz
        rcases List.mem_cons.mp (mem_of_mem_insertN x z ys hz) with rfl | hzmem
        · omega
        · exact (List.pairwise_cons.mp h).1 z hzmem

/-- Le tri par insertion rend une bande triée croissante. -/
theorem isort_sorted (ls : List ℕ) : SortedLe (isort ls) := by
  induction ls with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact insertN_sorted x (isort xs) ih

theorem insertN_perm (x : ℕ) (ys : List ℕ) :
    List.Perm (insertN x ys) (x :: ys) := by
  induction ys with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp only [insertN, if_pos hxy]; exact List.Perm.refl _
      · simp only [insertN, if_neg hxy]
        exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

/-- Le tri par insertion est une permutation : il ne change ni le contenu ni
la masse de la bande. -/
theorem isort_perm (ls : List ℕ) : List.Perm (isort ls) ls := by
  induction ls with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact List.Perm.trans (insertN_perm x (isort xs)) (List.Perm.cons x ih)

/-- La masse ne dépend que du multi-ensemble des longueurs : elle est
invariante par permutation. -/
theorem mass_perm {ls₁ ls₂ : List ℕ} (h : List.Perm ls₁ ls₂) (L : ℕ) :
    mass L ls₁ = mass L ls₂ := by
  simp only [mass]
  exact List.Perm.sum_nat (List.Perm.map _ h)

/-- Le maximum d'une bande de longueurs. -/
def maxd : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (maxd xs)

theorem le_maxd : ∀ {x : ℕ} {ls : List ℕ}, x ∈ ls → x ≤ maxd ls := by
  intro x ls h
  induction ls with
  | nil => cases h
  | cons y ys ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · simp only [maxd, Nat.le_max_left]
      · simp only [maxd]
        exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-! ## La construction de Huffman : forêt triée, fusion des deux minima -/

/-- Forêt triée par ordre de poids croissant. -/
abbrev SortedTW (ts : List WTree) : Prop :=
  List.Pairwise (fun a b => weight a ≤ weight b) ts

/-- Insertion d'un arbre dans une forêt triée, à sa place par poids. -/
def insertT (t : WTree) : List WTree → List WTree
  | [] => [t]
  | u :: us => if weight t ≤ weight u then t :: u :: us else u :: insertT t us

theorem insertT_length (t : WTree) : ∀ ts : List WTree,
    (insertT t ts).length = ts.length + 1 := by
  intro ts
  induction ts with
  | nil => rfl
  | cons u ts ih =>
      by_cases h : weight t ≤ weight u
      · simp only [insertT, if_pos h, List.length_cons]
      · simp only [insertT, if_neg h, List.length_cons, ih]

/-- Les arbres d'une forêt insérée sont exactement l'arbre inséré et les
arbres d'origine. -/
theorem mem_of_mem_insertT : ∀ (t z : WTree) (us : List WTree),
    z ∈ insertT t us → z ∈ t :: us := by
  intro t z us
  induction us with
  | nil => intro h; exact h
  | cons v vs ih =>
      intro h
      by_cases htv : weight t ≤ weight v
      · simp only [insertT, if_pos htv] at h; exact h
      · simp only [insertT, if_neg htv] at h
        rcases List.mem_cons.mp h with rfl | hmem
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.mp (ih hmem) with rfl | hmem'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem v hmem')

theorem insertT_sorted : ∀ (t : WTree) (ts : List WTree), SortedTW ts →
    SortedTW (insertT t ts) := by
  intro t ts
  induction ts with
  | nil => intro _; exact List.pairwise_singleton _ _
  | cons u ts ih =>
      intro h
      by_cases htu : weight t ≤ weight u
      · simp only [insertT, if_pos htu]
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzmem
        · exact htu
        · have huz : weight u ≤ weight z := (List.pairwise_cons.mp h).1 z hzmem
          exact Nat.le_trans htu huz
      · simp only [insertT, if_neg htu]
        refine List.pairwise_cons.mpr ⟨?_, ih h.tail⟩
        intro z hz
        rcases List.mem_cons.mp (mem_of_mem_insertT t z ts hz) with rfl | hzmem
        · omega
        · exact (List.pairwise_cons.mp h).1 z hzmem

theorem insertT_perm (t : WTree) (ts : List WTree) :
    List.Perm (insertT t ts) (t :: ts) := by
  induction ts with
  | nil => exact List.Perm.refl _
  | cons u ts ih =>
      by_cases h : weight t ≤ weight u
      · simp only [insertT, if_pos h]; exact List.Perm.refl _
      · simp only [insertT, if_neg h]
        exact List.Perm.trans (List.Perm.cons u ih) (List.Perm.swap t u ts)

/-- **La construction de Huffman.** Sur une forêt **triée** par poids
croissant, chaque étape retire les deux têtes — les deux arbres de plus
petits poids (`sorted_two_min`) — les fusionne en un nœud, et réinsère le
résultat à sa place. Itérée jusqu'à forêt singleton, c'est le trie de
Huffman. Le cas `[]` est dégénéré et hors contrat : `huffman` l'évite
(forêt initiale non vide dès que la liste de fréquences l'est). -/
def build : List WTree → WTree
  | [] => .leaf 0
  | [t] => t
  | t1 :: t2 :: ts => build (insertT (.node t1 t2) ts)
termination_by ts => ts.length
decreasing_by
  have h := insertT_length (.node t1 t2) ts
  simp only [List.length_cons]
  omega

/-- Sur une forêt triée, la tête est minimale. -/
theorem sorted_head_min {t : WTree} {ts : List WTree} (h : SortedTW (t :: ts)) :
    ∀ u ∈ ts, weight t ≤ weight u :=
  fun u hu => (List.pairwise_cons.mp h).1 u hu

/-- **Les deux têtes d'une forêt triée sont les deux minima** : `t1` majore
tout le monde et `t2` majore le reste. C'est ce qui fait de `build` la
construction de Huffman — chaque fusion marie bien les deux symboles de plus
petites fréquences, la propriété dont l'optimalité (pli suivant) découlera. -/
theorem sorted_two_min {t1 t2 : WTree} {ts : List WTree}
    (h : SortedTW (t1 :: t2 :: ts)) :
    (∀ u ∈ t2 :: ts, weight t1 ≤ weight u) ∧ (∀ v ∈ ts, weight t2 ≤ weight v) :=
  ⟨fun u hu => (List.pairwise_cons.mp h).1 u hu,
   fun v hv => (List.pairwise_cons.mp h.tail).1 v hv⟩

/-- La forêt initiale de `huffman` — les feuilles des fréquences, insérées
une à une — est triée. -/
theorem forest_sorted (ws : List ℕ) :
    SortedTW ((ws.map WTree.leaf).foldr insertT []) := by
  induction ws with
  | nil => exact List.Pairwise.nil
  | cons w ws ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact insertT_sorted _ _ ih

/-- Le trie de Huffman d'une liste de fréquences : forêt de feuilles triée
par poids, puis construction par fusions successives. -/
def huffman (ws : List ℕ) : WTree :=
  build ((ws.map WTree.leaf).foldr insertT [])

/-- La forêt de fusion n'est jamais vide quand les fréquences ne le sont
pas : chaque insertion ajoute exactement un arbre. -/
theorem forest_ne {ws : List ℕ} (hne : ws ≠ []) :
    (ws.map WTree.leaf).foldr insertT [] ≠ [] := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons w ws =>
      intro h
      simp only [List.map_cons, List.foldr_cons] at h
      have h0 : (insertT (WTree.leaf w) ((ws.map WTree.leaf).foldr insertT [])).length
          = 0 := by simp [h]
      rw [insertT_length] at h0
      omega

/-- **Conservation du poids total** : le poids du trie construit est la somme
des fréquences d'entrée. Chaque fusion remplace deux arbres par leur union
pondérée — la masse totale ne bouge jamais. -/
theorem weight_build : ∀ (n : ℕ) (f : List WTree), f.length ≤ n → f ≠ [] →
    weight (build f) = (f.map weight).sum := by
  intro n
  induction n with
  | zero =>
      intro f hlen hne
      cases f with
      | nil => exact absurd rfl hne
      | cons t ts =>
          cases ts with
          | nil => simp [build]
          | cons u us =>
              simp only [List.length_cons] at hlen
              exact absurd hlen (by omega)
  | succ n ih =>
      intro f hlen hne
      cases f with
      | nil => exact absurd rfl hne
      | cons t ts =>
          cases ts with
          | nil => simp [build]
          | cons u us =>
              have hlen' : (insertT (.node t u) us).length ≤ n := by
                rw [insertT_length]
                simp only [List.length_cons] at hlen
                omega
              have hne' : insertT (.node t u) us ≠ [] := by
                intro h
                have h0 : (insertT (.node t u) us).length = 0 := by simp [h]
                rw [insertT_length] at h0
                omega
              simp only [build]
              rw [ih _ hlen' hne']
              rw [List.Perm.sum_nat
                (List.Perm.map weight (insertT_perm (.node t u) us))]
              simp only [List.map_cons, List.sum_cons, weight]
              omega

/-! ## Le théorème capital : le code canonique du trie de Huffman -/

/-- **Le code canonique de Huffman existe et est préfixe-libre.** Pour toute
liste de fréquences, les profondeurs du trie de Huffman, triées croissantes,
sont admissibles au sens de Kraft (`mass_depths_le`) — donc le code canonique
de McMillan (pli 3) les réalise : préfixe-libre, longueurs exactes. C'est la
garantie formelle du carnet 02 : n'importe quelle table de fréquences mène à
un code de décodage non ambigu. -/
theorem huffman_canonical (ws : List ℕ) :
    ∃ ws' : List (List Bool),
      ws'.Pairwise PrefixFreeR ∧ ws'.map List.length = isort (depthsW (huffman ws)) := by
  have hsort : SortedLe (isort (depthsW (huffman ws))) := isort_sorted _
  have hL : ∀ d ∈ isort (depthsW (huffman ws)),
      d ≤ maxd (isort (depthsW (huffman ws))) := fun d hd => le_maxd hd
  have hmass : mass (maxd (isort (depthsW (huffman ws))))
      (isort (depthsW (huffman ws)))
      ≤ 2 ^ maxd (isort (depthsW (huffman ws))) := by
    rw [mass_perm (isort_perm _)]
    refine mass_depths_le _ _ ?_
    intro d hd
    exact le_maxd ((List.Perm.mem_iff (isort_perm _)).mpr hd)
  exact mcmillan_converse _ _ hsort hL hmass

/-! ## Ancres d'exécution -/

/- Les fréquences du carnet 02 : `1, 1, 2, 4` (a, b, c, d). Le trie de
Huffman fusionne d'abord `1 + 1` (a, b), puis le résultat avec `2` (c), puis
avec `4` (d) : les feuilles a et b tombent à profondeur 3, c à 2, d à 1. -/
#eval depthsW (huffman [1, 1, 2, 4])
-- [3, 3, 2, 1]

/- Le poids total se conserve : la somme des fréquences d'entrée. -/
#eval weight (huffman [1, 1, 2, 4])
-- 8

/- La bande de longueurs triée attendue par le code canonique. -/
#eval isort (depthsW (huffman [1, 1, 2, 4]))
-- [1, 2, 3, 3]

/- Le code canonique du trie : exactement le code du carnet 02,
`a = 0, b = 10, c = 110, d = 111` (masse de Kraft saturée, 8 = 2 ^ 3). -/
#eval canon (isort (depthsW (huffman [1, 1, 2, 4]))) 0
-- [[false], [true, false], [true, true, false], [true, true, true]]

/- Les mots portés par le trie lui-même (l'ordre des feuilles) : une autre
numérotation des mêmes longueurs — c'est la leçon du pli 3, l'arbre décide
des longueurs, la numérotation canonique décide des mots. -/
#eval leafWords (toCodeTree (huffman [1, 1, 2, 4]))
-- [[true, true, true], [true, true, false], [true, false], [false]]

/- La masse des profondeurs à l'échelle `2 ^ 3` :
`2^0 + 2^0 + 2^1 + 2^2 = 1 + 1 + 2 + 4 = 8 = 2 ^ 3` : Kraft saturé. -/
#eval mass 3 (isort (depthsW (huffman [1, 1, 2, 4])))
-- 8

end CompressionLean
