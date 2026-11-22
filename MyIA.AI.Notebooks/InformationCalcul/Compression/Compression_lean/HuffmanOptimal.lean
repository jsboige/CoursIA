/-
# HuffmanOptimal — le théorème d'optimalité complet (pli 5i de #18706)

Ce pli referme la question ouverte au pli 4 : **pourquoi fusionner les deux
plus petits donne-t-il le code de coût minimal ?** La réponse est le théorème
`huffman_optimal` : pour toute liste de fréquences, le trie de Huffman coûte
moins que tout arbre portant les mêmes feuilles.

La preuve assemble les trois morceaux accumulés par la série :

1. **Le lemme des sœurs** (plis 5g-5h) : tout arbre se réorganise, sans
   augmenter le coût, pour porter ses deux plus petits poids en paire de
   feuilles sœurs — multiplicités comprises (`both_mins_to_bottom`).
2. **La contraction** (ce pli) : remplacer cette paire par une feuille de
   masse `w₁ + w₂` rembourse exactement `w₁ + w₂` — c'est le lemme
   `costW_replaceAtW`, version sous-arbre de la facture positionnelle : la
   lecture construction de `costW` facture chaque fusion au poids du nœud
   construit, indépendamment de la profondeur, donc rouvrir ou refermer un
   nœud ne fait jamais qu'y facturer ou rembourser sa masse.
3. **L'induction** : le problème réduit vit sur `rest ++ [w₁ + w₂]` (une
   feuille de moins) ; l'hypothèse de récurrence s'y applique, et la
   **commutation** `huffman_expand` — le trie du problème complet coûte
   exactement le trie du problème réduit plus la masse mariée — referme la
   chaîne d'inégalités.

La commutation est le morceau technique : la construction de `build` est un
processus itératif dont rien ne garantit a priori qu'il se comporte bien
quand on échange une feuille contre un nœud de même masse. Le pli le résout
par une **lecture en facture** (`costW_build_charge`) : le coût d'un `build`
est la somme des coûts internes de la forêt de départ plus la charge des
fusions successives (`fusionCharge`) — et cette charge ne lit que la bande
des poids de la forêt (`fusionCharge_map_weight`), pas sa structure. Échanger
`leaf (w₁ + w₂)` contre `node (leaf w₁) (leaf w₂)` ne change ni la bande ni
la charge : seule la différence de coût interne `w₁ + w₂` passe à la caisse.

Il reste à savoir que deux forêts triées de même multi-ensemble ont la même
bande de poids : le tri d'un multi-ensemble est **unique** (`sortedLe_perm_eq`)
— deux tris croissants d'une même bande sont égaux, position par position.
C'est ce qui identifie les deux têtes de la forêt initiale de `huffman` aux
deux minima `w₁`, `w₂` sans aucun calcul : leurs poids le sont, par le tri.

Ancres du carnet `Compression-02` : sur les fréquences `1, 1, 2, 4`, le trie
coûte 14 et aucun arbre des mêmes feuilles ne fait mieux — l'arbre
déséquilibré de coût 21 (maille du pli 5g) et sa réorganisation à 16 (pli 5h)
en sont deux témoins battus.
-/
import DeuxMinima

namespace CompressionLean

/-! ## Une permutation vers la liste vide est absurde -/

/-- Aucune liste non vide n'est une permutation de la liste vide. -/
theorem cons_perm_nil_absurd {α : Type} {a : α} {t : List α} :
    (a :: t).Perm ([] : List α) → False := by
  intro hp
  have hlen := hp.length_eq
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-! ## Remplacer un sous-arbre : le pendant d'arbre de `replaceAt` -/

/-- Remplacer le sous-arbre au bout du chemin par l'arbre `u` donné — là où
`replaceAt` (pli 5f) ne sait substituer qu'un poids de feuille à une feuille,
`replaceAtW` substitue un arbre arbitraire à un sous-arbre arbitraire : c'est
le geste de la **contraction**, qui referme la paire de sœurs en une feuille
de masse fusionnée. Hors cible (chemin qui quitte l'arbre), l'arbre est
inchangé : les lemmes ne lisent `replaceAtW` que sous hypothèse de cible
atteinte, où la garde ne joue pas. -/
def replaceAtW : WTree → List Bool → WTree → WTree
  | _, [], u => u
  | .leaf v, _ :: _, _ => .leaf v
  | .node l r, true :: π, u => .node (replaceAtW l π u) r
  | .node l r, false :: π, u => .node l (replaceAtW r π u)

/-- Le poids total paie l'écart des masses (forme sans soustraction) : la
version sous-arbre de `weight_replaceAt` (pli 5f). -/
theorem weight_replaceAtW : ∀ (t : WTree) (π : List Bool) (s u : WTree),
    subtreeAt t π = some s →
    weight (replaceAtW t π u) + weight s = weight t + weight u := by
  intro t
  induction t with
  | leaf w =>
      intro π s u h
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          simp only [replaceAtW, weight]
          omega
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π s u h
      cases π with
      | nil =>
          -- la cible est la racine : le remplacement est entier
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          simp only [replaceAtW]
          omega
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have h1 := ihl π' s u h
              simp only [replaceAtW, weight]
              omega
          | false =>
              simp only [subtreeAt] at h
              have h1 := ihr π' s u h
              simp only [replaceAtW, weight]
              omega

/-- **La facture du remplacement ne lit que les masses internes.** Remplacer
le sous-arbre `s` par un arbre `u` de même masse ne change aucun poids sur le
chemin — donc le coût ne bouge que des coûts internes échangés : `costW`
facture chaque nœud au poids construit (`cost_node_charge`, pli 5), et les
poids construits sont les mêmes de part et d'autre. C'est le levier de la
contraction : refermer `node (leaf w₁) (leaf w₂)` en `leaf (w₁ + w₂)` y
rembourse exactement `w₁ + w₂`, le poids du nœud refermé. -/
theorem costW_replaceAtW : ∀ (t : WTree) (π : List Bool) (s u : WTree),
    subtreeAt t π = some s → weight u = weight s →
    costW t + costW u = costW (replaceAtW t π u) + costW s := by
  intro t
  induction t with
  | leaf w =>
      intro π s u h hw
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          simp only [replaceAtW, costW]
          omega
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π s u h hw
      cases π with
      | nil =>
          -- la cible est la racine : le remplacement est entier
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          simp only [replaceAtW]
          omega
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              have h1 := ihl π' s u h hw
              have h2 : weight (replaceAtW l π' u) = weight l := by
                have := weight_replaceAtW l π' s u h
                omega
              simp only [replaceAtW, costW]
              omega
          | false =>
              simp only [subtreeAt] at h
              have h1 := ihr π' s u h hw
              have h2 : weight (replaceAtW r π' u) = weight r := by
                have := weight_replaceAtW r π' s u h
                omega
              simp only [replaceAtW, costW]
              omega

/-- Tout poids d'un sous-arbre atteint est un poids de l'arbre : l'appar-
tenance remonte les chemins. Version sous-arbre de `subtreeAt_mem`. -/
theorem leafWeights_subtree_of : ∀ (t : WTree) (π : List Bool) (s : WTree),
    subtreeAt t π = some s → ∀ x ∈ leafWeights s, x ∈ leafWeights t := by
  intro t
  induction t with
  | leaf w =>
      intro π s h x hx
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          exact hx
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π s h x hx
      cases π with
      | nil =>
          simp only [subtreeAt, Option.some.injEq] at h
          subst s
          exact hx
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              simp only [leafWeights]
              exact List.mem_append_left _ (ihl π' s h x hx)
          | false =>
              simp only [subtreeAt] at h
              simp only [leafWeights]
              exact List.mem_append_right _ (ihr π' s h x hx)

/-- **La contraction préserve le multi-ensemble des feuilles.** Refermer la
paire `node (leaf a) (leaf b)` en une feuille de poids `c` retire une
occurrence de `a`, une de `b`, et ajoute `c`. Le cas des multiplicités
égalées (`a = b`, la maille `[1, 1, 2, 4]` du carnet 02) passe par le comptage
positionnel du pli 5h : deux positions distinctes portant le même poids
attestent qu'il en reste une après effacement. -/
theorem leafWeights_replaceAtW_pair : ∀ (t : WTree) (π : List Bool) (a b c : ℕ),
    subtreeAt t π = some (WTree.node (.leaf a) (.leaf b)) →
    List.Perm (leafWeights (replaceAtW t π (.leaf c)))
      (((leafWeights t).erase a).erase b ++ [c]) := by
  intro t
  induction t with
  | leaf w =>
      intro π a b c h
      cases π with
      | nil => simp [subtreeAt] at h
      | cons go π' => simp [subtreeAt] at h
  | node l r ihl ihr =>
      intro π a b c h
      cases π with
      | nil =>
          -- la cible est la racine : leafWeights t = [a, b], tout se déplie
          simp only [subtreeAt, Option.some.injEq] at h
          obtain ⟨hl, hr⟩ := WTree.node.inj h
          subst hl
          subst hr
          simp only [replaceAtW, leafWeights, List.cons_append, List.nil_append,
            List.erase_cons_head]
          exact List.Perm.refl _
      | cons go π' =>
          cases go with
          | true =>
              simp only [subtreeAt] at h
              -- a et b vivent dans le sous-arbre gauche
              have hma : a ∈ leafWeights l := by
                have := leafWeights_subtree_of l π' _ h a (by
                  simp [leafWeights])
                exact this
              have hmb : b ∈ leafWeights l := by
                have := leafWeights_subtree_of l π' _ h b (by
                  simp [leafWeights])
                exact this
              -- b survit à l'effacement de a : distinct, ou doublé (pli 5h)
              have hmb' : b ∈ (leafWeights l).erase a := by
                by_cases hab : b ≠ a
                · exact (List.mem_erase_of_ne hab).mpr hmb
                ·
                  push Not at hab
                  -- b = a : le même poids porté par les deux sœurs. On réécrit
                  -- `h` (la paire) avec `hab` pour que les deux feuilles lisent `a`.
                  rw [hab] at h
                  have hπa : subtreeAt l (π' ++ [true]) = some (.leaf a) := by
                    rw [subtreeAt_congr l π' [true]
                      (WTree.node (.leaf a) (.leaf a)) h]
                    rfl
                  have hπb : subtreeAt l (π' ++ [false]) = some (.leaf a) := by
                    rw [subtreeAt_congr l π' [false]
                      (WTree.node (.leaf a) (.leaf a)) h]
                    rfl
                  have hne : (π' ++ [true]) ≠ (π' ++ [false]) := by
                    intro he
                    have h2 : [true] = [false] := (List.append_right_inj π').mp he
                    simp at h2
                  have hcount := count_two_positions l (π' ++ [true])
                    (π' ++ [false]) a hπa hπb hne
                  have hcs : List.count a ((leafWeights l).erase a)
                      = List.count a (leafWeights l) - 1 := List.count_erase_self
                  have hgoal : a ∈ (leafWeights l).erase a :=
                    List.count_pos_iff.mp (by omega)
                  rw [hab]
                  exact hgoal
              -- Égalité (pas seulement Perm) : effacer a puis b de (l++r),
              -- avec a ∈ l et b ∈ (l.erase a), rend ((l.erase a).erase b) ++ r.
              have hkey : ((leafWeights l ++ leafWeights r).erase a).erase b
                  = ((leafWeights l).erase a).erase b ++ leafWeights r := by
                rw [List.erase_append_left _ hma, List.erase_append_left _ hmb']
              -- Le but (via ihl) est ((l.erase a).erase b ++ [c]) ++ r ;
              -- l'énoncé attend (((l++r).erase a).erase b) ++ [c] — même chose à
              -- réassociation près de [c] et r (Perm).
              have key : (((leafWeights l).erase a).erase b ++ [c] ++ leafWeights r).Perm
                  (((leafWeights l ++ leafWeights r).erase a).erase b ++ [c]) := by
                rw [hkey]
                -- (X ++ [c]) ++ r ~ (X ++ r) ++ [c], X = (l.erase a).erase b
                have hassoc : ∀ (X : List ℕ),
                    ((X ++ [c]) ++ leafWeights r).Perm ((X ++ leafWeights r) ++ [c]) := by
                  intro X
                  rw [List.append_assoc, List.append_assoc]
                  exact List.Perm.append_left X List.perm_append_comm
                exact hassoc _
              simp only [replaceAtW, leafWeights, List.append_assoc]
              exact List.Perm.trans
                (List.Perm.append_right _ (ihl π' a b c h)) key
          | false =>
              simp only [subtreeAt] at h
              have hma : a ∈ leafWeights r := by
                have := leafWeights_subtree_of r π' _ h a (by
                  simp [leafWeights])
                exact this
              have hmb : b ∈ leafWeights r := by
                have := leafWeights_subtree_of r π' _ h b (by
                  simp [leafWeights])
                exact this
              have hmb' : b ∈ (leafWeights r).erase a := by
                by_cases hab : b ≠ a
                · exact (List.mem_erase_of_ne hab).mpr hmb
                ·
                  push Not at hab
                  rw [hab] at h
                  have hπa : subtreeAt r (π' ++ [true]) = some (.leaf a) := by
                    rw [subtreeAt_congr r π' [true]
                      (WTree.node (.leaf a) (.leaf a)) h]
                    rfl
                  have hπb : subtreeAt r (π' ++ [false]) = some (.leaf a) := by
                    rw [subtreeAt_congr r π' [false]
                      (WTree.node (.leaf a) (.leaf a)) h]
                    rfl
                  have hne : (π' ++ [true]) ≠ (π' ++ [false]) := by
                    intro he
                    have h2 : [true] = [false] := (List.append_right_inj π').mp he
                    simp at h2
                  have hcount := count_two_positions r (π' ++ [true])
                    (π' ++ [false]) a hπa hπb hne
                  have hcs : List.count a ((leafWeights r).erase a)
                      = List.count a (leafWeights r) - 1 := List.count_erase_self
                  have hgoal : a ∈ (leafWeights r).erase a :=
                    List.count_pos_iff.mp (by omega)
                  rw [hab]
                  exact hgoal
              -- Égalité via commutation : (l++r) ~ (r++l), et effacer a puis b
              -- de (r++l), avec a ∈ r et b ∈ (r.erase a), rend
              -- ((r.erase a).erase b) ++ l.
              have hcom : (leafWeights l ++ leafWeights r).Perm
                  (leafWeights r ++ leafWeights l) := List.perm_append_comm
              have hkey : ((leafWeights r ++ leafWeights l).erase a).erase b
                  = ((leafWeights r).erase a).erase b ++ leafWeights l := by
                rw [List.erase_append_left _ hma, List.erase_append_left _ hmb']
              -- Le but (via ihr) est l ++ ((r.erase a).erase b ++ [c]) ;
              -- l'énoncé attend (((l++r).erase a).erase b) ++ [c] — Perm par
              -- commutation et réassociation.
              have key : (leafWeights l ++ (((leafWeights r).erase a).erase b ++ [c])).Perm
                  (((leafWeights l ++ leafWeights r).erase a).erase b ++ [c]) := by
                apply List.Perm.trans _ (List.Perm.append_right [c]
                  ((hcom.erase a).erase b)).symm
                rw [hkey]
                -- l ++ (Y ++ [c]) ~ (Y ++ l) ++ [c], Y = (r.erase a).erase b
                have hassoc : ∀ (Y : List ℕ),
                    (leafWeights l ++ (Y ++ [c])).Perm ((Y ++ leafWeights l) ++ [c]) := by
                  intro Y
                  rw [← List.append_assoc (leafWeights l) Y [c]]
                  exact List.Perm.append_right [c] List.perm_append_comm
                -- but : l ++ (Y ++ [c]) ; cible : (Y ++ l) ++ [c]
                exact hassoc _
              simp only [replaceAtW, leafWeights, List.append_assoc]
              exact List.Perm.trans
                (List.Perm.append_left _ (ihr π' a b c h)) key

/-! ## Deux faits de structure sur les feuilles -/

/-- Un arbre a toujours au moins une feuille. -/
theorem leafWeights_ne : ∀ t : WTree, leafWeights t ≠ [] := by
  intro t
  induction t with
  | leaf w => simp [leafWeights]
  | node l r ihl ihr =>
      intro h
      cases hll : leafWeights l with
      | nil => exact absurd hll ihl
      | cons x xs =>
          simp only [leafWeights, hll, List.cons_append] at h
          exact List.cons_ne_nil _ _ h

/-- **Aucun arbre n'a zéro feuille** (forme utilisable par contradiction sur
une permutation vers la liste vide). -/
theorem leafWeights_perm_nil (t : WTree) :
    (leafWeights t).Perm ([] : List ℕ) → False :=
  fun hperm => leafWeights_ne t
    (List.eq_nil_iff_forall_not_mem.mpr
      (fun x hx => nomatch hperm.mem_iff.mp hx))

/-- Un arbre à une seule feuille est une feuille. -/
theorem leafWeights_eq_singleton : ∀ (t : WTree) (w : ℕ),
    leafWeights t = [w] → t = .leaf w := by
  intro t
  induction t with
  | leaf v =>
      intro w h
      simp only [leafWeights, List.cons.injEq] at h
      rw [h.1]
  | node l r ihl ihr =>
      intro w h
      cases hl : leafWeights l with
      | nil => exact absurd hl (leafWeights_ne l)
      | cons x xs =>
          cases hr : leafWeights r with
          | nil => exact absurd hr (leafWeights_ne r)
          | cons y ys =>
              simp only [leafWeights, hl, hr, List.cons_append] at h
              simp at h

/-! ## La facture de la construction : somme des coûts internes + fusions -/

/-- La forêt obtenue par insertions successives est une permutation de la
forêt de départ : le tri par insertion déplace, il ne crée ni ne perd. -/
theorem foldr_insertT_perm : ∀ ts : List WTree,
    (ts.foldr insertT []).Perm ts := by
  intro ts
  induction ts with
  | nil => exact List.Perm.refl _
  | cons t ts ih =>
      simp only [List.foldr_cons]
      exact (insertT_perm t _).trans (List.Perm.cons t ih)

/-- Les insertions successives préservent le nombre d'arbres. -/
theorem foldr_insertT_length : ∀ ts : List WTree,
    (ts.foldr insertT []).length = ts.length := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.foldr_cons, insertT_length, ih, List.length_cons]

/-- **La position d'insertion ne lit que le poids** : insérer `u` dans une
forêt triée donne une forêt dont la bande de poids est l'insertion du poids
de `u` dans la bande de poids — le même `insertN` que le tri des longueurs
du pli 4. La structure de `u` ne joue aucun rôle dans sa position. -/
theorem insertT_map_weight (u : WTree) : ∀ ts : List WTree,
    (insertT u ts).map weight = insertN (weight u) (ts.map weight) := by
  intro ts
  induction ts with
  | nil => rfl
  | cons v vs ih =>
      by_cases h : weight u ≤ weight v
      · simp only [insertT, if_pos h, List.map_cons, insertN, if_pos h]
      · simp only [insertT, if_neg h, List.map_cons, insertN, if_neg h, ih]

/-- Tout arbre de la forêt d'insertions successives de feuilles est une
feuille : le tri par insertion déplace ses éléments, il n'en fabrique pas. -/
theorem mem_foldr_insertT_leaf : ∀ (ws : List ℕ) (x : WTree),
    x ∈ (ws.map WTree.leaf).foldr insertT [] → ∃ w, x = .leaf w := by
  intro ws x hx
  have hmem : x ∈ ws.map WTree.leaf := (foldr_insertT_perm _).mem_iff.mp hx
  obtain ⟨w, _, hwx⟩ := List.mem_map.mp hmem
  exact ⟨w, hwx.symm⟩

/-- La charge des fusions d'un `build` : chaque étape facture le poids du
nœud qu'elle construit — la masse des deux têtes mariées. Cette charge ne
dépend que de la suite des poids, jamais des structures mariées. -/
def fusionCharge : List WTree → ℕ
  | [] => 0
  | [_] => 0
  | t1 :: t2 :: ts => (weight t1 + weight t2) + fusionCharge (insertT (.node t1 t2) ts)
termination_by ts => ts.length
decreasing_by
  have h := insertT_length (.node t1 t2) ts
  simp only [List.length_cons]
  omega

/-- Marier les deux têtes facture leur masse en plus de la charge du reste
inséré — forme dépliée de `fusionCharge` sur un cons-cons. -/
theorem fusionCharge_cons (t u : WTree) (ts : List WTree) :
    fusionCharge (t :: u :: ts)
      = weight t + weight u + fusionCharge (insertT (.node t u) ts) := by
  simp only [fusionCharge]

/-- **Théorème central de la facture : le coût d'un `build` est la somme des
coûts internes de la forêt de départ plus la charge des fusions.** Chaque
fusion préserve le multi-ensemble des arbres (`insertT_perm`) et le poids
total, donc le coût interne de la forêt se transporte intact d'une étape à
la suivante ; ce que chaque fusion ajoute est exactement le poids du nœud
construit (`cost_node_charge`). C'est la lecture construction du coût, mise
en équation sur le processus itératif lui-même. -/
theorem costW_build_charge : ∀ (n : ℕ) (f : List WTree), f.length ≤ n → f ≠ [] →
    costW (build f) = (f.map costW).sum + fusionCharge f := by
  intro n
  induction n with
  | zero =>
      intro f hlen hne
      cases f with
      | nil => exact absurd rfl hne
      | cons t ts =>
          cases ts with
          | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
          | cons u us =>
              simp only [List.length_cons, List.length_cons] at hlen
              omega
  | succ n ih =>
      intro f hlen hne
      cases f with
      | nil => exact absurd rfl hne
      | cons t ts =>
          cases ts with
          | nil =>
              simp only [build, fusionCharge, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil]
              omega
          | cons u us =>
              have hlen' : (insertT (.node t u) us).length ≤ n := by
                rw [insertT_length]
                simp only [List.length_cons, List.length_cons] at hlen
                omega
              have hne' : insertT (.node t u) us ≠ [] := by
                intro h
                have h0 : (insertT (.node t u) us).length = 0 := by simp [h]
                rw [insertT_length] at h0
                omega
              simp only [build]
              rw [ih _ hlen' hne']
              rw [List.Perm.sum_nat (List.Perm.map costW (insertT_perm _ us))]
              simp only [List.map_cons, List.sum_cons, List.sum_nil,
                fusionCharge, cost_node_charge, weight]
              omega

/-- **La charge des fusions ne lit que la bande des poids.** Deux forêts de
même longueur et de même bande de poids — position par position — ont des
constructions parallèles : mêmes têtes en poids, mêmes nœuds insérés en
poids (`insertT_map_weight`), donc mêmes factures d'étape. -/
theorem fusionCharge_map_weight : ∀ (n : ℕ) (f g : List WTree), f.length ≤ n →
    f.map weight = g.map weight → fusionCharge f = fusionCharge g := by
  intro n
  induction n with
  | zero =>
      intro f g hlen hw
      have hle := congrArg List.length hw
      simp only [List.length_map] at hle
      cases f with
      | nil =>
          cases g with
          | nil => rfl
          | cons v vs =>
              simp only [List.length_cons, List.length_nil] at hle
              omega
      | cons t ts =>
          cases ts with
          | nil =>
              cases g with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at hle
                  omega
              | cons v vs =>
                  cases vs with
                  | nil => simp only [fusionCharge]
                  | cons w ws =>
                      simp only [List.length_cons, List.length_nil] at hle
                      omega
          | cons u us =>
              simp only [List.length_cons, List.length_cons, List.length_nil] at hlen
              omega
  | succ n ih =>
      intro f g hlen hw
      have hle := congrArg List.length hw
      simp only [List.length_map] at hle
      cases f with
      | nil =>
          cases g with
          | nil => rfl
          | cons v vs =>
              simp only [List.length_cons, List.length_nil] at hle
              omega
      | cons t ts =>
          cases ts with
          | nil =>
              cases g with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at hle
                  omega
              | cons v vs =>
                  cases vs with
                  | nil => simp only [fusionCharge]
                  | cons w ws =>
                      simp only [List.length_cons, List.length_cons,
                        List.length_nil] at hle
                      omega
          | cons u us =>
              cases g with
              | nil =>
                  simp only [List.length_cons, List.length_cons,
                    List.length_nil] at hle
                  omega
              | cons v vs =>
                  cases vs with
                  | nil =>
                      simp only [List.length_cons, List.length_cons,
                        List.length_nil] at hle
                      omega
                  | cons w ws =>
                      -- les têtes en poids coïncident, position par position
                      simp only [List.map_cons, List.cons.injEq] at hw
                      obtain ⟨ht1, ht2, hrest⟩ := hw
                      have hpar : (insertT (.node t u) us).map weight
                          = (insertT (.node v w) ws).map weight := by
                        rw [insertT_map_weight, insertT_map_weight]
                        simp only [weight, ← hrest, ← ht1, ← ht2]
                      have hlen' : (insertT (.node t u) us).length ≤ n := by
                        rw [insertT_length]
                        simp only [List.length_cons, List.length_cons,
                          List.length_cons] at hlen
                        omega
                      have hrec := ih _ _ hlen' hpar
                      simp only [fusionCharge, ← ht1, ← ht2]
                      rw [hrec]

/-! ## Le tri d'un multi-ensemble est unique -/

/-- La tête d'une bande triée majore toute la bande. -/
theorem sortedLe_head_min {a : ℕ} {l : List ℕ} (h : SortedLe (a :: l)) :
    ∀ x ∈ a :: l, a ≤ x := by
  intro x hx
  rcases List.mem_cons.mp hx with he | hx'
  · omega
  · exact (List.pairwise_cons.mp h).1 x hx'

/-- **Deux tris croissants d'un même multi-ensemble sont égaux.** Les têtes
se majorent mutuellement (chacune est le minimum de sa bande, et la
permutation transporte l'appartenance), donc coïncident ; l'effacement de la
tête commune préserve la permutation des restes, et la récurrence referme
l'égalité position par position. C'est ce qui donne aux deux têtes de la
forêt initiale de `huffman` l'identité des deux minima : sans calcul, par le
tri. -/
theorem sortedLe_perm_eq : ∀ (l₁ l₂ : List ℕ), SortedLe l₁ → SortedLe l₂ →
    l₁.Perm l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ hp
      cases l₂ with
      | nil => rfl
      | cons b t => exact absurd hp.symm cons_perm_nil_absurd
  | cons a t ih =>
      intro l₂ h1 h2 hp
      cases l₂ with
      | nil => exact absurd hp cons_perm_nil_absurd
      | cons b t2 =>
          have hb_le : b ≤ a := by
            have hbm : ∀ x ∈ b :: t2, b ≤ x := sortedLe_head_min h2
            have ham : a ∈ b :: t2 := hp.mem_iff.mp List.mem_cons_self
            exact hbm a ham
          have ha_le : a ≤ b := by
            have ham : ∀ x ∈ a :: t, a ≤ x := sortedLe_head_min h1
            have hbm : b ∈ a :: t := hp.mem_iff.mpr List.mem_cons_self
            exact ham b hbm
          have hab : a = b := Nat.le_antisymm ha_le hb_le
          have hrest : t.Perm t2 := by
            have h1e : (a :: t).erase a = t := List.erase_cons_head a t
            have h2e : (b :: t2).erase b = t2 := List.erase_cons_head b t2
            have hpe := hp.erase a
            rw [h1e, hab] at hpe
            exact h2e ▸ hpe
          have hteq : t = t2 := ih t2 h1.tail h2.tail hrest
          rw [hab, hteq]

/-- La bande des poids d'une forêt triée est triée. -/
theorem sortedTW_map_weight : ∀ f : List WTree, SortedTW f →
    SortedLe (f.map weight) := by
  intro f
  induction f with
  | nil => exact fun _ => List.Pairwise.nil
  | cons t ts ih =>
      intro h
      simp only [List.map_cons]
      refine List.pairwise_cons.mpr ⟨?_, ih h.tail⟩
      intro x hx
      obtain ⟨u, hu, hux⟩ := List.mem_map.mp hx
      rw [← hux]
      exact (List.pairwise_cons.mp h).1 u hu

/-- **Le coût d'un `build` ne dépend que du multi-ensemble de sa forêt**
(dès lors qu'elle est triée) : la somme des coûts internes est invariante par
permutation, et les bandes de poids — triées et permutées — coïncident par
unicité du tri, donc les charges de fusion aussi. -/
theorem costW_build_perm : ∀ (f g : List WTree), SortedTW f → SortedTW g →
    f ≠ [] → f.Perm g → costW (build f) = costW (build g) := by
  intro f g hf hg hne hperm
  have hnel : g ≠ [] := by
    intro h
    rw [h] at hperm
    have hfnil : f = [] := by
      cases f with
      | nil => rfl
      | cons t ts => exact absurd hperm cons_perm_nil_absurd
    exact hne hfnil
  have hwf : SortedLe (f.map weight) := sortedTW_map_weight f hf
  have hwg : SortedLe (g.map weight) := sortedTW_map_weight g hg
  have hwp : (f.map weight).Perm (g.map weight) := List.Perm.map weight hperm
  have hweq : f.map weight = g.map weight := sortedLe_perm_eq _ _ hwf hwg hwp
  rw [costW_build_charge f.length f (Nat.le_refl _) hne,
    costW_build_charge g.length g (Nat.le_refl _) hnel]
  rw [List.Perm.sum_nat (List.Perm.map costW hperm),
    fusionCharge_map_weight f.length f g (Nat.le_refl _) hweq]

/-! ## La commutation : marier d'abord, c'est payer la masse une fois -/

/-- **La commutation huffman/expansion.** Le trie du problème complet coûte
exactement le trie du problème réduit plus la masse mariée : échanger dans
la forêt la paire de feuilles `w₁, w₂` contre la feuille `w₁ + w₂` ne change
ni la position d'insertion (elle ne lit que le poids), ni la charge des
fusions (elle ne lit que la bande des poids) — seule la différence de coût
interne `w₁ + w₂` (le nœud refermé) passe à la caisse. C'est le théorème
`costW_subst` du pli 5d, lu sur la construction elle-même au lieu d'un
arbre fini. -/
theorem huffman_expand : ∀ (ws : List ℕ) (w₁ w₂ : ℕ) (rest : List ℕ),
    isort ws = w₁ :: w₂ :: rest →
    costW (huffman ws) = costW (huffman (rest ++ [w₁ + w₂])) + (w₁ + w₂) := by
  intro ws w₁ w₂ rest hiso
  -- la bande des poids de la forêt initiale est le tri de ws
  have hFp : ((ws.map WTree.leaf).foldr insertT []).Perm (ws.map WTree.leaf) :=
    foldr_insertT_perm _
  have hFs : SortedTW ((ws.map WTree.leaf).foldr insertT []) := forest_sorted ws
  have hp2 : ((ws.map WTree.leaf).map weight).Perm ws := by
    have hfun : (weight ∘ WTree.leaf) = id := by funext w; rfl
    rw [List.map_map, hfun, List.map_id]
  have hp3 : (((ws.map WTree.leaf).foldr insertT []).map weight).Perm
      (isort ws) :=
    (List.Perm.map weight hFp).trans (hp2.trans (isort_perm ws).symm)
  have hFw : (((ws.map WTree.leaf).foldr insertT []).map weight)
      = w₁ :: w₂ :: rest :=
    (sortedLe_perm_eq _ _ (sortedTW_map_weight _ hFs) (isort_sorted ws)
      hp3).trans hiso
  have hpw : ws.Perm (w₁ :: w₂ :: rest) := by
    have h := isort_perm ws
    rw [hiso] at h
    exact h.symm
  -- le corps : décomposer la forêt, identifier les têtes, facturer
  have key : ∀ F : List WTree,
      F = (ws.map WTree.leaf).foldr insertT [] →
      SortedTW F →
      F.Perm (ws.map WTree.leaf) →
      F.map weight = w₁ :: w₂ :: rest →
      costW (huffman ws) = costW (huffman (rest ++ [w₁ + w₂])) + (w₁ + w₂) := by
    intro F hF0 hFs hFp hFw
    have hF2 : 2 ≤ F.length := by
      have h := congrArg List.length hFw
      simp only [List.length_map, List.length_cons, List.length_cons] at h
      omega
    cases F with
    | nil => simp at hF2
    | cons t1 Ft =>
        cases Ft with
        | nil => simp at hF2
        | cons t2 F_rest =>
            -- décomposition de la bande des poids
            simp only [List.map_cons, List.cons.injEq] at hFw
            obtain ⟨ht1, ht2, _⟩ := hFw
            -- les têtes sont des feuilles (la forêt n'en contient qu')
            obtain ⟨v1, hv1⟩ := mem_foldr_insertT_leaf ws t1 (by
              rw [← hF0]; exact List.mem_cons_self)
            obtain ⟨v2, hv2⟩ := mem_foldr_insertT_leaf ws t2 (by
              rw [← hF0]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            rw [hv1] at ht1
            rw [hv2] at ht2
            simp only [weight] at ht1 ht2
            rw [hv1, hv2, ht1, ht2] at hFp
            -- la forêt restante est triée
            have hFrest_sorted : SortedTW F_rest :=
              (List.pairwise_cons.mp (List.pairwise_cons.mp hFs).2).2
            have hneA : insertT (WTree.leaf (w₁ + w₂)) F_rest ≠ [] := by
              intro h
              have h0 : (insertT (WTree.leaf (w₁ + w₂)) F_rest).length = 0 := by
                simp [h]
              rw [insertT_length] at h0
              omega
            -- la charge est la même des deux côtés : mêmes bandes de poids
            have hchg : fusionCharge (insertT (WTree.leaf (w₁ + w₂)) F_rest)
                = fusionCharge (insertT
                  (WTree.node (WTree.leaf w₁) (WTree.leaf w₂)) F_rest) := by
              refine fusionCharge_map_weight _ _ _ (Nat.le_refl _) ?_
              rw [insertT_map_weight, insertT_map_weight]
              rfl
            -- facture du run complet : dépliée en masse + reste inséré
            have hfull : costW (build (WTree.leaf w₁ :: WTree.leaf w₂ :: F_rest))
                = w₁ + w₂ + ((F_rest.map costW).sum
                  + fusionCharge (insertT
                    (WTree.node (WTree.leaf w₁) (WTree.leaf w₂)) F_rest)) := by
              have h := costW_build_charge _
                (WTree.leaf w₁ :: WTree.leaf w₂ :: F_rest) (Nat.le_refl _)
                (by simp)
              rw [h, fusionCharge_cons]
              simp only [List.map_cons, List.sum_cons, costW, weight]
              omega
            -- facture du run réduit (feuille fusionnée)
            have hred := costW_build_charge _
              (insertT (WTree.leaf (w₁ + w₂)) F_rest) (Nat.le_refl _) hneA
            have hred' : (List.map costW
                  (insertT (WTree.leaf (w₁ + w₂)) F_rest)).sum
                = (List.map costW (WTree.leaf (w₁ + w₂) :: F_rest)).sum :=
              List.Perm.sum_nat
                (List.Perm.map costW (insertT_perm (WTree.leaf (w₁ + w₂)) F_rest))
            -- le run réduit est un huffman du problème réduit
            have hreds : costW (build (insertT (WTree.leaf (w₁ + w₂)) F_rest))
                = costW (huffman (rest ++ [w₁ + w₂])) := by
              have hAsorted : SortedTW (insertT (WTree.leaf (w₁ + w₂)) F_rest) :=
                insertT_sorted _ _ hFrest_sorted
              have hBsorted : SortedTW (((rest ++ [w₁ + w₂]).map
                  WTree.leaf).foldr insertT []) := forest_sorted _
              have hAB : (insertT (WTree.leaf (w₁ + w₂)) F_rest).Perm
                  (((rest ++ [w₁ + w₂]).map WTree.leaf).foldr insertT []) := by
                -- feuille mariée + reste ≡ₚ feuille fusionnée + reste trié
                have h1 : (insertT (WTree.leaf (w₁ + w₂)) F_rest).Perm
                    (WTree.leaf (w₁ + w₂) :: F_rest) := insertT_perm _ _
                -- F_rest ≡ₚ rest.map leaf, par effacements successifs
                have hwsp : (ws.map WTree.leaf).Perm
                    (WTree.leaf w₁ :: WTree.leaf w₂ :: rest.map WTree.leaf) := by
                  simpa only [List.map_cons] using List.Perm.map WTree.leaf hpw
                have hFrest : F_rest.Perm (rest.map WTree.leaf) := by
                  have hp0 := hFp.trans hwsp
                  exact List.Perm.cons_inv (List.Perm.cons_inv hp0)
                have h2 : (WTree.leaf (w₁ + w₂) :: F_rest).Perm
                    (WTree.leaf (w₁ + w₂) :: rest.map WTree.leaf) :=
                  List.Perm.cons _ hFrest
                have h3 : (WTree.leaf (w₁ + w₂) :: rest.map WTree.leaf).Perm
                    ((rest ++ [w₁ + w₂]).map WTree.leaf) := by
                  simp only [List.map_append, List.map_cons, List.map_nil]
                  -- `perm_middle : [] ++ a :: l ~ a :: ([] ++ l)` ; ici a = la
                  -- feuille mariée, l = rest.map leaf, et le but est lu à
                  -- l'envers (sym).
                  have hm := (List.perm_middle (l₁ := rest.map WTree.leaf)
                    (l₂ := []) (a := WTree.leaf (w₁ + w₂))).symm
                  simpa only [List.append_nil] using hm
                exact h1.trans (h2.trans (h3.trans (foldr_insertT_perm _).symm))
              rw [show huffman (rest ++ [w₁ + w₂])
                  = build (((rest ++ [w₁ + w₂]).map WTree.leaf).foldr insertT [])
                  from rfl]
              exact costW_build_perm _ _ hAsorted hBsorted hneA hAB
            -- assemblage : l'écart des deux runs est exactement la masse
            have hmapd : (List.map costW (WTree.leaf (w₁ + w₂) :: F_rest)).sum
                = (F_rest.map costW).sum := by simp [costW]
            have hA : costW (build (WTree.leaf w₁ :: WTree.leaf w₂ :: F_rest))
                = costW (build (insertT (WTree.leaf (w₁ + w₂)) F_rest))
                  + (w₁ + w₂) := by
              rw [hfull, hred]
              omega
            rw [show huffman ws = build ((ws.map WTree.leaf).foldr insertT [])
              from rfl, ← hF0, hv1, hv2, ht1, ht2, hA, hreds]
  exact key _ rfl hFs hFp hFw

/-- Toute liste d'au moins deux éléments se décompose en deux têtes et un
reste. Contournement positionnel de `cases` sur un terme non-variable
(`isort ws`), que l'élimination dépendante refuse au pin courant. -/
theorem list_decompose : ∀ (l : List ℕ), 2 ≤ l.length →
    ∃ w₁ w₂ rest, l = w₁ :: w₂ :: rest := by
  intro l h
  cases l with
  | nil =>
      simp only [List.length_nil] at h
      omega
  | cons a t =>
      cases t with
      | nil =>
          simp only [List.length_cons, List.length_nil] at h
          omega
      | cons b t2 => exact ⟨a, b, t2, rfl⟩

/-! ## Le théorème d'optimalité -/

/-- **Le trie de Huffman est optimal.** Pour toute liste de fréquences et
tout arbre portant ces fréquences en feuilles, le trie de Huffman coûte
moins cher. La preuve assemble la série : les deux minima descendent en
paire de sœurs sans augmenter le coût (plis 5g-5h), la paire se referme en
une feuille de masse `w₁ + w₂` qui rembourse exactement sa masse
(`costW_replaceAtW`), le problème réduit se résout par l'hypothèse de
récurrence, et la commutation (`huffman_expand`) facture au trie complet
exactement la masse mariée en plus du trie réduit — chaque maillon est
une égalité ou une inégalité déjà établie, le théorème est leur chaîne. -/
theorem huffman_optimal : ∀ (n : ℕ) (ws : List ℕ), ws.length ≤ n →
    ∀ t : WTree, List.Perm (leafWeights t) ws → costW (huffman ws) ≤ costW t := by
  intro n
  induction n with
  | zero =>
      intro ws hlen t hperm
      cases ws with
      | nil => exact absurd hperm (leafWeights_perm_nil t)
      | cons w ws' => simp at hlen
  | succ n ih =>
      intro ws hlen t hperm
      cases ws with
      | nil => exact absurd hperm (leafWeights_perm_nil t)
      | cons w ws' =>
          cases ws' with
          | nil =>
              -- une seule fréquence : l'arbre est la feuille, coût nul
              have htleaf : t = .leaf w := by
                cases t with
                | leaf v =>
                    simp only [leafWeights] at hperm
                    have hwv : w = v := by
                      have h1 : w ∈ [v] := hperm.mem_iff.mpr (by simp)
                      rcases List.mem_cons.mp h1 with he | hx'
                      · exact he
                      · nomatch hx'
                    rw [hwv]
                | node l r =>
                    have hlen2 : (leafWeights l ++ leafWeights r).length = 1 := by
                      have h0 := hperm.length_eq
                      simpa only [leafWeights, List.length_singleton] using h0
                    cases hll : leafWeights l with
                    | nil => exact absurd hll (leafWeights_ne l)
                    | cons x xs =>
                        cases hrr : leafWeights r with
                        | nil => exact absurd hrr (leafWeights_ne r)
                        | cons y ys =>
                            rw [hll, hrr] at hlen2
                            simp only [List.length_append, List.length_cons,
                              List.length_nil] at hlen2
                            omega
              rw [htleaf]
              simp only [huffman, List.map_cons, List.map_nil, List.foldr_cons,
                List.foldr_nil, insertT, build, costW]
              omega
          | cons w' ws'' =>
              -- au moins deux fréquences : la chaîne complète
              -- re-abstraction : les théorèmes aval parlent de la liste entière
              obtain ⟨ws, hws⟩ : ∃ l : List ℕ, l = w :: w' :: ws'' := ⟨_, rfl⟩
              rw [← hws] at hperm hlen ⊢
              have hliso : (isort ws).length = ws.length := (isort_perm ws).length_eq
              have hlen2 : 2 ≤ ws.length := by
                rw [hws]
                simp only [List.length_cons, List.length_nil]
                omega
              obtain ⟨w₁, w₂, rest, hiso⟩ := list_decompose (isort ws) (by omega)
              -- l'arbre est un nœud (une feuille seule contredit deux fréquences)
              obtain ⟨l, r, htnode⟩ : ∃ l r, t = WTree.node l r := by
                cases t with
                | leaf v =>
                    have hlen1 : ws.length = 1 := by
                      have h0 := hperm.length_eq
                      simpa only [leafWeights, List.length_singleton] using h0.symm
                    rw [hws] at hlen1
                    simp only [List.length_cons, List.length_nil] at hlen1
                    omega
                | node l r => exact ⟨l, r, rfl⟩
              -- les minima, transportés aux feuilles de t
              have hpw : ws.Perm (w₁ :: w₂ :: rest) := by
                have h := isort_perm ws
                rw [hiso] at h
                exact h.symm
              have hsort : SortedLe (w₁ :: w₂ :: rest) := by
                have h := isort_sorted ws
                rw [hiso] at h
                exact h
              have hmin₁ : ∀ v ∈ leafWeights t, w₁ ≤ v := by
                intro v hv
                have hvws : v ∈ ws := hperm.mem_iff.mp hv
                have hvsw : v ∈ w₁ :: w₂ :: rest :=
                  hpw.mem_iff.mp hvws
                exact sortedLe_head_min hsort v hvsw
              have hw₁ : w₁ ∈ leafWeights t :=
                hperm.mem_iff.mpr (hpw.symm.mem_iff.mp (by simp))
              have herase : ((leafWeights t).erase w₁).Perm
                  (w₂ :: rest) := by
                have hp1 := hperm.erase w₁
                have hp2 := hpw.erase w₁
                rw [List.erase_cons_head] at hp2
                exact hp1.trans hp2
              have hmin₂ : ∀ v ∈ (leafWeights t).erase w₁, w₂ ≤ v := by
                intro v hv
                have hvw : v ∈ w₂ :: rest := herase.mem_iff.mp hv
                exact sortedLe_head_min hsort.tail v hvw
              have hw₂ : w₂ ∈ (leafWeights t).erase w₁ :=
                herase.symm.mem_iff.mp (by simp)
              -- le lemme des sœurs (plis 5g-5h)
              obtain ⟨t'', π, hperm2, hcost2, hpair, _⟩ :=
                both_mins_to_bottom t ⟨l, r, htnode⟩ w₁ w₂ hmin₁ hw₁
                  hmin₂ hw₂
              -- la contraction rembourse la masse mariée
              have hsc : subtreeAt t'' π
                  = some (WTree.node (.leaf w₁) (.leaf w₂)) := hpair
              have hwleaf : weight (WTree.leaf (w₁ + w₂))
                  = weight (WTree.node (.leaf w₁) (.leaf w₂)) := by
                simp only [weight]
              have hcostc := costW_replaceAtW t'' π
                (WTree.node (.leaf w₁) (.leaf w₂))
                (WTree.leaf (w₁ + w₂)) hsc hwleaf
              simp only [costW, weight] at hcostc
              -- le multi-ensemble du problème réduit
              have hperm_t_c : (leafWeights (replaceAtW t'' π
                  (.leaf (w₁ + w₂)))).Perm (rest ++ [w₁ + w₂]) := by
                have hp1 := leafWeights_replaceAtW_pair t'' π w₁ w₂
                  (w₁ + w₂) hsc
                have hpa : (leafWeights t'').Perm
                    (w₁ :: w₂ :: rest) :=
                  (hperm2.trans hperm).trans hpw
                have p1 := hpa.erase w₁
                rw [List.erase_cons_head] at p1
                have p2 := p1.erase w₂
                rw [List.erase_cons_head] at p2
                exact List.Perm.trans hp1
                  (List.Perm.append_right _ p2)
              -- l'hypothèse de récurrence sur le problème réduit
              have hlenrest : (rest ++ [w₁ + w₂]).length ≤ n := by
                have hwl : ws.length = rest.length + 2 := by
                  have h0 := (isort_perm ws).length_eq
                  rw [hiso] at h0
                  simp only [List.length_cons, List.length_nil] at h0
                  omega
                simp only [List.length_append, List.length_cons,
                  List.length_nil] at hlen ⊢
                omega
              have hIH := ih (rest ++ [w₁ + w₂]) hlenrest
                (replaceAtW t'' π (.leaf (w₁ + w₂))) hperm_t_c
              -- la commutation, et la chaîne
              have hcom := huffman_expand ws w₁ w₂ rest hiso
              omega

/-! ## Ancres du carnet 02 : le trie de 14 n'est pas battu -/

/- Le coût du trie de Huffman des fréquences du carnet : 14 (ancre du pli 5,
retrouvée par le théorème — c'est le minimum). -/
#eval costW (huffman [1, 1, 2, 4])
-- 14

/-- **Aucun arbre des feuilles 1, 1, 2, 4 ne coûte moins de 14** : le trie
de Huffman est optimal, l'ancre 14 du pli 5 est un minimum. -/
example (t : WTree) (h : List.Perm (leafWeights t) [1, 1, 2, 4]) :
    14 ≤ costW t := by
  have h14 : costW (huffman [1, 1, 2, 4]) = 14 := by
    simp [huffman, build, insertT, weight, costW]
  have hopt := huffman_optimal 4 [1, 1, 2, 4] (by decide) t h
  rwa [h14] at hopt

/-- L'arbre déséquilibré de la maille 21 (plis 5e-5g) est un témoin battu :
le trie de Huffman fait mieux que lui, en vertu du théorème. -/
example : costW (huffman [1, 1, 2, 4]) ≤ costW desequilibre := by
  have hp : List.Perm (leafWeights desequilibre) [1, 1, 2, 4] := by
    simp [desequilibre, leafWeights]
  exact huffman_optimal 4 [1, 1, 2, 4] (by decide) desequilibre hp

/- Le témoin 16 du pli 5h (le second 1 descendu) : battu lui aussi — le
théorème couvre tous les arbres des mêmes feuilles. -/
#eval costW (exchPos (exchPos desequilibre [false, false, true] [true] 2 1)
    [false, false, false] [false, true] 4 1)
-- 16

end CompressionLean
