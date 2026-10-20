import PrefixCodes

/-!
# Decode — décodage préfixe et table de décodage (pli 2, EPIC #18706)

Le module `PrefixCodes` établit la théorie statique : les feuilles d'un
`CodeTree` forment un code préfixe, et leur somme de Kraft reste sous `1`.
Ce module installe la **machine dynamique** que le carnet Python du pli 2
(`Compression-02-HuffmanCanonique`, « tables de décodage ») manipule à la
main : étant donné un flux de bits et l'arbre du code, retrouver la suite de
mots qui l'a produit.

Contenu distillé :

1. **Un pas de décodage** (`decode1`) : depuis la racine, suivre les bits
   (`true` = gauche, `false` = droite) jusqu'à une feuille ; rendre le mot
   consommé et le reste du flux. Un flux épuisé en chemin (`none`) ou une
   racine-feuille (mot vide) sont les deux cas dégénérés, traités
   explicitement plutôt que maquillés.
2. **Correction et complétude du pas** (`decode1_sound`,
   `decode1_complete`) : `decode1` rend `some (w, rest)` exactement quand
   le flux commence par le mot de feuille `w` suivi de `rest` — le
   décodeur ni n'invente, ni ne perd. C'est la version dynamique de
   l'absence d'ambiguïté de `leafWords_prefixFree`.
3. **Décodage complet** (`decode`) : itérer le pas jusqu'à épuiser le
   flux ; l'itération termine parce qu'un pas consomme au moins un bit
   dès que l'arbre n'est pas une racine-feuille (`decode1_shorter`).
   Le flux vide décode en message vide ; la racine-feuille (code du mot
   vide) est rejetée explicitement.
4. **Théorème de round-trip** (`decode_encode`) : décoder la
   concaténation d'une liste de mots de feuilles redonne exactement cette
   liste — le contrat d'une table de décodage : ce que l'émetteur a
   coupé, le récepteur le recolle, dans l'ordre, sans reste.
5. **Ancres numériques** (`#eval`) : le code de longueurs `(1, 2, 3, 3)`
   du carnet 01 (`sf4` : `a=0, b=10, c=110, d=111`), un flux tronqué
   (`none`), et le round-trip intégral du code lui-même.

Roadmap (plis suivants de #18706, hors de cette tranche) : le théorème de
McMillan (réciproque de Kraft), le trie canonique de Huffman, et
l'optimalité de Huffman.
-/

namespace CompressionLean

/-! ## Un pas de décodage -/

/-- `decode1 t bits` : un pas de décodage — suivre `bits` depuis la racine
de `t` jusqu'à la première feuille, rendre le mot consommé (le chemin
d'arêtes) et le reste du flux. `none` si le flux se termine avant une
feuille. Cas dégénéré assumé : une racine-feuille rend le mot vide sans
consommer aucun bit (voir `decode`, qui rejette ce code). -/
def decode1 : CodeTree → List Bool → Option (List Bool × List Bool)
  | .leaf, rest => some ([], rest)
  | .node _ _, [] => none
  | .node l _, true :: rest =>
      (decode1 l rest).map (fun p => (true :: p.1, p.2))
  | .node _ r, false :: rest =>
      (decode1 r rest).map (fun p => (false :: p.1, p.2))

/-- Un pas ne grandit jamais le flux, et le raccourcit strictement dès que
l'arbre n'est pas une racine-feuille. Forme à hypothèse unique (la
référence à `t ≠ leaf` vit dans la conclusion), pour que l'induction
s'applique aux sous-arbres sans exigence sur eux. -/
theorem decode1_len {t : CodeTree} {w rest bits : List Bool}
    (h : decode1 t bits = some (w, rest)) :
    rest.length ≤ bits.length ∧ (t ≠ .leaf → rest.length < bits.length) := by
  induction t generalizing w rest bits with
  | leaf =>
    simp only [decode1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun hcon => absurd rfl hcon⟩
  | node l r ihl ihr =>
    cases bits with
    | nil => simp [decode1] at h
    | cons b bs =>
      cases b with
      | true =>
        simp only [decode1, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, hp, heq⟩ := h
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨hle, _⟩ := ihl hp
        simp only [List.length_cons]
        exact ⟨by omega, fun _ => by omega⟩
      | false =>
        simp only [decode1, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, hp, heq⟩ := h
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨hle, _⟩ := ihr hp
        simp only [List.length_cons]
        exact ⟨by omega, fun _ => by omega⟩

/-- Un pas ne consomme rien sur une racine-feuille ; partout ailleurs il
consomme au moins un bit : l'itération de `decode1` termine. -/
theorem decode1_shorter {t : CodeTree} {w rest bits : List Bool}
    (ht : t ≠ .leaf) (h : decode1 t bits = some (w, rest)) :
    rest.length < bits.length :=
  (decode1_len h).2 ht

/-! ## Correction et complétude du pas -/

/-- **Correction du pas** : si `w` est un mot de feuille de `t`, décoder
`w ++ rest` rend exactement `(w, rest)` — le mot et son suffixe, intacts. -/
theorem decode1_sound {t : CodeTree} {w rest : List Bool}
    (hw : w ∈ leafWords t) : decode1 t (w ++ rest) = some (w, rest) := by
  induction t generalizing w rest with
  | leaf =>
    rw [List.mem_singleton.mp hw]
    simp [decode1]
  | node l r ihl ihr =>
    simp only [leafWords, List.mem_append, List.mem_map] at hw
    obtain ⟨w', hw', hw_eq⟩ | ⟨w', hw', hw_eq⟩ := hw
    · subst hw_eq
      rw [List.cons_append]
      simp only [decode1]
      rw [ihl hw']
      rfl
    · subst hw_eq
      rw [List.cons_append]
      simp only [decode1]
      rw [ihr hw']
      rfl

/-- **Complétude du pas** : tout décodage réussi sépare le flux en un mot
de feuille et son suffixe exact — le décodeur n'invente rien. -/
theorem decode1_complete {t : CodeTree} {w rest bits : List Bool}
    (h : decode1 t bits = some (w, rest)) :
    bits = w ++ rest ∧ w ∈ leafWords t := by
  induction t generalizing w rest bits with
  | leaf =>
    simp only [decode1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [leafWords]⟩
  | node l r ihl ihr =>
    cases bits with
    | nil => simp [decode1] at h
    | cons b bs =>
      cases b with
      | true =>
        simp only [decode1, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, hp, heq⟩ := h
        obtain ⟨hbits, hmem⟩ := ihl hp
        obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by rw [hbits, ← List.cons_append], ?_⟩
        simp only [leafWords, List.mem_append, List.mem_map]
        exact Or.inl ⟨p.1, hmem, rfl⟩
      | false =>
        simp only [decode1, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, hp, heq⟩ := h
        obtain ⟨hbits, hmem⟩ := ihr hp
        obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by rw [hbits, ← List.cons_append], ?_⟩
        simp only [leafWords, List.mem_append, List.mem_map]
        exact Or.inr ⟨p.1, hmem, rfl⟩

/-! ## Décodage complet -/

/-- Hors racine-feuille, tous les mots de feuilles sont non vides : chaque
mot de code coûte au moins un bit. -/
theorem leafWords_ne_nil {t : CodeTree} (ht : t ≠ .leaf)
    {w : List Bool} (hw : w ∈ leafWords t) : w ≠ [] := by
  induction t with
  | leaf => exact absurd rfl ht
  | node l r ihl ihr =>
    simp only [leafWords, List.mem_append, List.mem_map] at hw
    obtain ⟨w', _, hw_eq⟩ | ⟨w', _, hw_eq⟩ := hw
    · subst hw_eq; exact List.cons_ne_nil _ _
    · subst hw_eq; exact List.cons_ne_nil _ _

/-- Décodage itéré pour un arbre qui n'est pas une racine-feuille (hypothèse
passée en argument, donc sans test d'égalité sur l'arbre). Le flux vide
rend le message vide ; sinon un pas de `decode1`, puis on recommence sur le
reste — la terminaison vient de `decode1_shorter`. -/
def decodeNode : (t : CodeTree) → t ≠ .leaf → List Bool → Option (List (List Bool))
  | _, _, [] => some []
  | t, ht, bits =>
      match _h : decode1 t bits with
      | none => none
      | some (w, rest) => (w :: ·) <$> decodeNode t ht rest
termination_by _ _ bits => bits.length
decreasing_by
  exact decode1_shorter ht _h

/-- `decode t bits` : décoder un flux complet — itérer `decode1` jusqu'à
épuiser le flux. Le flux vide décode en message vide. `none` si le flux se
termine en chemin, ou si le code est la racine-feuille (le mot vide
bouclerait sans rien consommer). -/
def decode (t : CodeTree) (bits : List Bool) : Option (List (List Bool)) :=
  match t with
  | .leaf => none
  | .node l r => decodeNode (.node l r) (fun h => nomatch h) bits

/-- Cas du flux vide : hors racine-feuille, il décode en message vide. -/
theorem decode_nil (t : CodeTree) (ht : t ≠ .leaf) : decode t [] = some [] := by
  cases t with
  | leaf => exact absurd rfl ht
  | node => rw [decode, decodeNode]

/-- Le pas récursif de `decodeNode`, isolé : si un premier pas de `decode1`
réussit sur un flux non vide, décoder le flux revient à décaler le mot lu
en tête du décodage du reste. -/
theorem decodeNode_step {t : CodeTree} (ht : t ≠ .leaf) {bits : List Bool}
    (hne : bits ≠ []) {w rest : List Bool} (h : decode1 t bits = some (w, rest)) :
    decodeNode t ht bits = (w :: ·) <$> decodeNode t ht rest := by
  cases bits with
  | nil => exact absurd rfl hne
  | cons b bs =>
    rw [decodeNode.eq_def]
    dsimp only
    split
    · next hnone => rw [h] at hnone; simp at hnone
    · next w' rest' hsome =>
      rw [h] at hsome
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      rfl

/-- Le pas récursif de `decode`, isolé : si un premier pas de `decode1`
réussit sur un flux non vide, décoder le flux revient à décaler le mot lu
en tête du décodage du reste. -/
theorem decode_step {t : CodeTree} {bits : List Bool} (ht : t ≠ .leaf)
    (hne : bits ≠ []) {w rest : List Bool} (h : decode1 t bits = some (w, rest)) :
    decode t bits = (w :: ·) <$> decode t rest := by
  cases t with
  | leaf => exact absurd rfl ht
  | node l r =>
    rw [decode, decode]
    exact decodeNode_step ht hne h

/-- Étape-clé du round-trip : décoder `w ++ rest` quand `w` est un mot de
feuille, c'est décaler `w` en tête du décodage de `rest`. -/
theorem decode_cons {t : CodeTree} {w rest : List Bool} (ht : t ≠ .leaf)
    (hw : w ∈ leafWords t) :
    decode t (w ++ rest) = (w :: ·) <$> decode t rest :=
  have hwne : w ≠ [] := leafWords_ne_nil ht hw
  decode_step ht (fun h => hwne ((List.append_eq_nil_iff.mp h).1))
    (decode1_sound hw)

/-! ## Théorème de round-trip -/

/-- **Round-trip** : décoder la concaténation d'une liste de mots de
feuilles de `t` redonne exactement cette liste, dans l'ordre. C'est le
contrat d'une table de décodage : ce que l'émetteur a coupé, le récepteur
le recolle, sans reste ni réordonnancement. -/
theorem decode_encode (t : CodeTree) (ws : List (List Bool))
    (ht : t ≠ .leaf) (h : ∀ w ∈ ws, w ∈ leafWords t) :
    decode t ws.flatten = some ws := by
  induction ws with
  | nil => simpa using decode_nil t ht
  | cons w ws ih =>
    rw [List.flatten_cons, decode_cons ht (h w (by simp)),
      ih (fun w' hw' => h w' (by simp [hw']))]
    simp

/-! ## Ancres numériques des carnets frères -/

/- Le code de longueurs `(1, 2, 3, 3)` du carnet 01 (`a=0, b=10, c=110,
d=111`) décode le message `a b c` sans reste. -/
#eval decode sf4 [true, false, true, false, false, true]
-- some [[true], [false, true], [false, false, true]]

/- Un flux tronqué en chemin (le `1` de `10` sans son `0`) échoue :
`none`, pas de décodage inventé. -/
#eval decode sf4 [false]
-- none

/- Round-trip intégral : le flux formé de tous les mots du code, pris
dans l'ordre des feuilles, redonne le code lui-même. -/
#eval decode sf4 (leafWords sf4).flatten
-- some [[true], [false, true], [false, false, true], [false, false, false]]

/- Le code fixe 2 bits (`fixed2`) round-trip sur ses quatre mots. -/
#eval decode fixed2 (leafWords fixed2).flatten
-- some [[true, true], [true, false], [false, true], [false, false]]

end CompressionLean
