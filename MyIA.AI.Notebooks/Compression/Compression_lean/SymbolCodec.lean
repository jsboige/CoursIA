import Mathlib
import PrefixCodes
import Decode
import Huffman

/-!
# SymbolCodec — codec etiquete : le symbole, pas seulement son poids (EPIC #18706)

Les plis precedents ont construit le code, jamais l'**alphabet**. `WTree`
(`Huffman.lean`) porte un poids par feuille et `toCodeTree` l'oublie ;
`depthsW` rend une bande de longueurs ; `Decode.lean` prouve le round-trip sur
une liste de **mots** de feuilles. Aucun de ces objets ne relie un mot a un
**symbole** : deux symboles de poids egal y sont indiscernables, et une
permutation d'etiquettes laisse le cout et Kraft invariants.

Ce module ajoute la couche etiquetee, et elle seule : il ne redemontre ni
Kraft, ni McMillan, ni l'optimalite de Huffman, et il ne duplique pas la
theorie du decodage — il l'**appelle**.

1. **Arbre etiquete** (`LTree n`) : chaque feuille porte un symbole de `Fin n`.
   `pairs` lit l'arbre en profondeur d'abord gauche et rend, **alignes sur le
   meme parcours**, le mot et son etiquette. C'est cet alignement qui porte le
   contrat : `wordsOf` et `labels` sont les deux projections de la meme liste,
   donc l'association symbole / mot / profondeur ne peut pas deriver.
2. **Fonctions d'oubli** (`forget`, `toWTree`) : oublier les etiquettes rend le
   `CodeTree` du pli 1 — `wordsOf_forget` prouve que les mots sont **les
   memes**, pas seulement de meme longueur ; oublier vers un `WTree` rend les
   poids par symbole, et `depthsW_toWTree` rend la profondeur de chaque mot
   **dans l'ordre des symboles**.
3. **Encodage et decodage etiquetes** (`encodeMsg`, `decodeL`) : `encodeMsg`
   suit le chemin d'un symbole (`pathTo`), `decodeL` decode le flux avec le
   decodeur du pli 2 (`decode`) puis relit l'etiquette de chaque mot lu
   (`labelAt`). Le round-trip `decodeL_encode` compose les deux sous des
   hypotheses explicites : arbre non reduit a une feuille, encodage reussi.
4. **Contrat du mot vide et du singleton** : une racine feuille porte le mot
   vide, et `Decode.decode` la **rejette** (`decode .leaf _ = none`). Ce module
   garde cette convention sans la contourner : `leaf_root_contract` la rend
   explicite, et aucun theoreme d'ici ne reclame a la fois l'optimalite non
   contrainte du mot vide et la convention Python a un bit.
5. **Controles negatifs** : un arbre **n'est pas** un mecanisme d'integrite.
   `Nodup` (unicite des etiquettes) et `pairs_fst_inj` disent ce qu'un codec
   garantit — un mot ne code qu'un symbole, un symbole n'a qu'un mot — et rien
   de plus : une permutation d'etiquettes de meme poids conserve cout et Kraft
   tout en changeant le message (`swap_labels_message`).

Sibling EN : `SymbolCodec_en.lean` (namespace `CompressionLean_en`), memes
enonces et preuves, docstrings traduites — convention i18n #4980 pattern A.

Voir #22377 (part of #18706).
-/

namespace CompressionLean

/-! ## Arbre etiquete et parcours aligne -/

/-- Arbre binaire dont chaque feuille porte un symbole de l'alphabet `Fin n`.
Le poids et la profondeur ne sont pas des champs : ils se lisent par le
parcours (`pairs`), ce qui interdit de porter une etiquette que le parcours
contredirait. -/
inductive LTree (n : Nat) where
  /-- Feuille : un symbole de l'alphabet. -/
  | leaf (s : Fin n) : LTree n
  /-- Noeud interne : les deux sous-arbres. -/
  | node : LTree n → LTree n → LTree n
  deriving DecidableEq, Repr

/-- Renommer les symboles par une application de l'alphabet dans lui-meme.
Sert au controle negatif : une permutation laisse le code intact. -/
def mapSym {n : Nat} (σ : Fin n → Fin n) : LTree n → LTree n
  | .leaf s => .leaf (σ s)
  | .node l r => .node (mapSym σ l) (mapSym σ r)

/-- Parcours en profondeur d'abord gauche : pour chaque feuille, son mot (le
chemin depuis la racine, `true` = gauche comme dans `leafWords`) **et** son
etiquette, dans la meme entree de liste. Toute la suite projette cette liste
unique. -/
def pairs {n : Nat} : LTree n → List (List Bool × Fin n)
  | .leaf s => [([], s)]
  | .node l r =>
      (pairs l).map (fun p => (true :: p.1, p.2)) ++
      (pairs r).map (fun p => (false :: p.1, p.2))

/-- Les mots du code portes par l'arbre etiquete, dans l'ordre du parcours. -/
def wordsOf {n : Nat} (t : LTree n) : List (List Bool) := (pairs t).map Prod.fst

/-- Les etiquettes des feuilles, dans l'ordre du parcours : `labels t` et
`wordsOf t` ont la meme longueur et se correspondent indice a indice. -/
def labels {n : Nat} (t : LTree n) : List (Fin n) := (pairs t).map Prod.snd

/-- **Unicite des etiquettes** : une etiquette ne designe qu'un seul mot.
C'est la condition qui fait d'un arbre etiquete un *code* sur l'alphabet et non
une simple liste de feuilles ; elle est ecrite dans la forme dont le codec se
sert (injectivite etiquette -> mot), pas dans une forme de liste qui
demanderait de compter les occurrences. -/
def Nodup {n : Nat} (t : LTree n) : Prop :=
  ∀ (p q : List Bool) (s : Fin n), (p, s) ∈ pairs t → (q, s) ∈ pairs t → p = q

/-! ## Fonctions d'oubli -/

/-- Oublier les etiquettes : l'arbre de codes du pli 1. -/
def forget {n : Nat} : LTree n → CodeTree
  | .leaf _ => .leaf
  | .node l r => .node (forget l) (forget r)

/-- Oublier les etiquettes en gardant les poids : l'arbre pondere du pli 4, ou
le poids d'une feuille est la frequence de son symbole. -/
def toWTree {n : Nat} (wt : Fin n → Nat) : LTree n → WTree
  | .leaf s => .leaf (wt s)
  | .node l r => .node (toWTree wt l) (toWTree wt r)

/-! ## Lemmes de parcours -/

/-- Projeter le mot apres avoir prefixe un bit, c'est projeter puis prefixer —
la forme qui aligne `pairs` et `leafWords`. -/
theorem map_fst_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map Prod.fst =
    (l.map Prod.fst).map (b :: ·) := by
  simp [List.map_map, Function.comp_def]

/-- Projeter l'etiquette apres avoir prefixe un bit ne change pas les
etiquettes : la profondeur n'est jamais une etiquette. -/
theorem map_snd_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map Prod.snd = l.map Prod.snd := by
  simp [List.map_map, Function.comp_def]

/-- Projeter la longueur apres avoir prefixe un bit ajoute `1` a chaque
longueur — l'association symbole / profondeur, cote longueur. -/
theorem map_length_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map (fun p => p.1.length) =
    (l.map (fun p => p.1.length)).map (· + 1) := by
  simp [List.map_map, Function.comp_def]

/-- **Les mots de l'arbre etiquete sont ceux de son oubli** : la couche
etiquetee n'invente ni ne perd aucun mot. C'est le pont vers
`leafWords_prefixFree` et `decode_encode` du pli 2. -/
theorem wordsOf_forget {n : Nat} (t : LTree n) :
    wordsOf t = leafWords (forget t) := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      simp only [wordsOf, pairs, forget, leafWords, List.map_append,
        List.map_map, Function.comp_def]
      rw [show leafWords (forget l) = (pairs l).map Prod.fst from ihl.symm,
        show leafWords (forget r) = (pairs r).map Prod.fst from ihr.symm]
      simp [List.map_map, Function.comp_def]

/-- **Les profondeurs dans l'ordre des symboles** : oublier vers un arbre
pondere rend exactement les longueurs des mots de `pairs`, feuille par
feuille. L'association symbole / profondeur est donc portee par la meme liste
que les mots. -/
theorem depthsW_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    depthsW (toWTree wt t) = (pairs t).map (fun p => p.1.length) := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      simp only [toWTree, depthsW, pairs, List.map_append, map_length_prefix,
        ihl, ihr]

/-- **Le poids de l'arbre pondere est la somme des frequences des symboles
portes** : oublier vers `WTree` ne perd aucun poids en route. -/
theorem weight_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    weight (toWTree wt t) = ((labels t).map wt).sum := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      simp only [toWTree, weight, labels, pairs, List.map_append,
        map_snd_prefix, List.sum_append, ihl, ihr]

/-- Renommer les symboles ne change pas les mots : la permutation d'etiquettes
est invisible au code lui-meme. -/
theorem wordsOf_mapSym {n : Nat} (σ : Fin n → Fin n) (t : LTree n) :
    wordsOf (mapSym σ t) = wordsOf t := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      have h1 : (pairs (mapSym σ l)).map Prod.fst = (pairs l).map Prod.fst := ihl
      have h2 : (pairs (mapSym σ r)).map Prod.fst = (pairs r).map Prod.fst := ihr
      simp only [mapSym, wordsOf, pairs, List.map_append]
      rw [map_fst_prefix, map_fst_prefix, map_fst_prefix, map_fst_prefix, h1, h2]

/-- Renommer les symboles renomme les etiquettes, dans le meme ordre : c'est
la moitie « message » du controle negatif. -/
theorem labels_mapSym {n : Nat} (σ : Fin n → Fin n) (t : LTree n) :
    labels (mapSym σ t) = (labels t).map σ := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      have h1 : (pairs (mapSym σ l)).map Prod.snd = ((pairs l).map Prod.snd).map σ := ihl
      have h2 : (pairs (mapSym σ r)).map Prod.snd = ((pairs r).map Prod.snd).map σ := ihr
      simp only [mapSym, labels, pairs, List.map_append]
      rw [map_snd_prefix, map_snd_prefix, map_snd_prefix, map_snd_prefix, h1, h2]

/-! ## Decomposition du parcours d'un noeud -/

/-- Le parcours d'un noeud, lu par mot : un mot du sous-arbre gauche commence
par `true`, un mot du sous-arbre droit par `false`. C'est la forme qui rend
les cas d'un noeud decidables. -/
theorem mem_pairs_node {n : Nat} (l r : LTree n) (w : List Bool) (s : Fin n) :
    (w, s) ∈ pairs (.node l r) ↔
      (∃ w', w = true :: w' ∧ (w', s) ∈ pairs l) ∨
      (∃ w', w = false :: w' ∧ (w', s) ∈ pairs r) := by
  simp only [pairs, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨p, hp, hpe⟩ | ⟨p, hp, hpe⟩)
    · have hs : p.2 = s := (Prod.mk.injEq _ _ _ _).mp hpe |>.2
      refine Or.inl ⟨p.1, (congrArg Prod.fst hpe).symm, ?_⟩
      simpa [← hs] using hp
    · have hs : p.2 = s := (Prod.mk.injEq _ _ _ _).mp hpe |>.2
      refine Or.inr ⟨p.1, (congrArg Prod.fst hpe).symm, ?_⟩
      simpa [← hs] using hp
  · rintro (⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩)
    · exact Or.inl ⟨(w', s), hw', rfl⟩
    · exact Or.inr ⟨(w', s), hw', rfl⟩

/-- Un noeud ne porte jamais le mot vide : ses mots commencent tous par un
bit. C'est ce qui separe la racine-feuille (code singleton) du reste. -/
theorem node_fst_ne_nil {n : Nat} {l r : LTree n} {w : List Bool} {s : Fin n}
    (h : (w, s) ∈ pairs (.node l r)) : w ≠ [] := by
  rcases (mem_pairs_node l r w s).mp h with ⟨w', rfl, _⟩ | ⟨w', rfl, _⟩ <;> simp

/-- **Chaque mot ne code qu'un symbole** : deux feuilles de meme mot portent la
meme etiquette. Propriete structurelle du parcours, sans aucune hypothese —
c'est ce qui rend le decodage deterministe. -/
theorem pairs_fst_inj {n : Nat} (t : LTree n) {p : List Bool} {s s' : Fin n}
    (h : (p, s) ∈ pairs t) (h' : (p, s') ∈ pairs t) : s = s' := by
  induction t generalizing p s s' with
  | leaf u =>
      simp only [pairs, List.mem_singleton, Prod.mk.injEq] at h h'
      rw [h.2, h'.2]
  | node l r ihl ihr =>
      rcases (mem_pairs_node l r p s).mp h with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩
      · rcases (mem_pairs_node l r (true :: w) s').mp h' with
          ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
        · injection hu with _ hwu
          exact ihl hw (by rw [← hwu] at hu'; exact hu')
        · exact absurd hu (by simp)
      · rcases (mem_pairs_node l r (false :: w) s').mp h' with
          ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
        · exact absurd hu (by simp)
        · injection hu with _ hwu
          exact ihr hw (by rw [← hwu] at hu'; exact hu')

/-! ## Unicite des etiquettes : ce qu'elle achete -/

/-- Une feuille n'a qu'une etiquette : `Nodup` y est immediat. -/
theorem nodup_leaf {n : Nat} (s : Fin n) : Nodup (.leaf s) := by
  intro p q s' hp hq
  simp only [pairs, List.mem_singleton, Prod.mk.injEq] at hp hq
  rw [hp.1, hq.1]

/-- Sous unicite des etiquettes, deux feuilles de meme etiquette sont la meme
feuille : le code est **injectif sur l'alphabet**. Sans elle, un symbole peut
apparaitre sous deux mots (`LTree` l'autorise), et `pathTo` n'en choisirait
qu'un. -/
theorem pairs_snd_inj {n : Nat} {t : LTree n} (h : Nodup t) {p q : List Bool}
    {s : Fin n} (hp : (p, s) ∈ pairs t) (hq : (q, s) ∈ pairs t) : p = q :=
  h p q s hp hq

/-! ## Chemins : encoder un symbole -/

/-- Chemin d'un symbole dans l'arbre : `some p` si `s` est une feuille de `p`,
`none` si le symbole n'est pas dans l'alphabet porte. Premier parcours en
profondeur d'abord : sous `Nodup`, l'occurrence est unique. -/
def pathTo {n : Nat} : LTree n → Fin n → Option (List Bool)
  | .leaf s, s' => if s = s' then some [] else none
  | .node l r, s' =>
      match pathTo l s' with
      | some p => some (true :: p)
      | none => (pathTo r s').map (false :: ·)

/-- Tout chemin rendu par `pathTo` est un mot du code. -/
theorem pathTo_mem {n : Nat} {t : LTree n} {s : Fin n} {p : List Bool}
    (h : pathTo t s = some p) : (p, s) ∈ pairs t := by
  induction t generalizing p with
  | leaf u =>
      simp only [pathTo] at h
      split at h
      · next hu =>
          simp only [Option.some.injEq] at h
          subst h
          simp [pairs, hu]
      · simp at h
  | node l r ihl ihr =>
      simp only [pathTo] at h
      cases hl : pathTo l s with
      | some q =>
          rw [hl] at h
          simp only [Option.some.injEq] at h
          subst h
          exact (mem_pairs_node l r (true :: q) s).mpr (Or.inl ⟨q, rfl, ihl hl⟩)
      | none =>
          rw [hl] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨q, hq, hqe⟩ := h
          subst hqe
          exact (mem_pairs_node l r (false :: q) s).mpr (Or.inr ⟨q, rfl, ihr hq⟩)

/-- Aucune etiquette n'est egaree : un symbole present dans l'arbre a un
chemin. -/
theorem pathTo_ne_none_of_mem {n : Nat} {t : LTree n} {s : Fin n}
    {p : List Bool} (h : (p, s) ∈ pairs t) : pathTo t s ≠ none := by
  induction t generalizing p with
  | leaf u =>
      simp only [pairs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [pathTo]
  | node l r ihl ihr =>
      rcases (mem_pairs_node l r p s).mp h with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩
      · cases hl : pathTo l s with
        | none => exact absurd hl (ihl hw)
        | some q => simp [pathTo, hl]
      · have hr : pathTo r s ≠ none := ihr hw
        cases hl : pathTo l s with
        | some q => simp [pathTo, hl]
        | none =>
            cases hr' : pathTo r s with
            | none => exact absurd hr' hr
            | some q => simp [pathTo, hl, hr']

/-! ## Etiquettes : decoder un mot -/

/-- Etiquette portee par un mot : descendre le chemin, rendre l'etiquette de
la feuille atteinte. `none` si le chemin ne se termine pas sur une feuille
(prefixe d'un mot, ou mot trop long) — le rejet est explicite, jamais un
symbole par defaut. -/
def labelAt {n : Nat} : LTree n → List Bool → Option (Fin n)
  | .leaf s, [] => some s
  | .leaf _, _ :: _ => none
  | .node _ _, [] => none
  | .node l _, true :: bs => labelAt l bs
  | .node _ r, false :: bs => labelAt r bs

/-- **`labelAt` et `pairs` decrivent la meme correspondance** : un mot porte
l'etiquette `s` si et seulement si la paire figure au parcours. Aucune
hypothese : c'est une propriete du parcours, pas du code. -/
theorem labelAt_iff {n : Nat} (t : LTree n) (bs : List Bool) (s : Fin n) :
    labelAt t bs = some s ↔ (bs, s) ∈ pairs t := by
  induction t generalizing bs s with
  | leaf u =>
      cases bs with
      | nil => simp [labelAt, pairs, eq_comm]
      | cons b bs => simp [labelAt, pairs]
  | node l r ihl ihr =>
      cases bs with
      | nil =>
          have hnone : (([] : List Bool), s) ∉ pairs (.node l r) := fun hm =>
            node_fst_ne_nil hm rfl
          simp [labelAt, hnone]
      | cons b bs =>
          cases b with
          | true =>
              simp only [labelAt]
              rw [ihl, mem_pairs_node]
              constructor
              · intro hm; exact Or.inl ⟨bs, rfl, hm⟩
              · rintro (⟨w', hw', hm⟩ | ⟨w', hw', _⟩)
                · injection hw' with _ hbs
                  simpa [hbs] using hm
                · exact absurd hw' (by simp)
          | false =>
              simp only [labelAt]
              rw [ihr, mem_pairs_node]
              constructor
              · intro hm; exact Or.inr ⟨bs, rfl, hm⟩
              · rintro (⟨w', hw', _⟩ | ⟨w', hw', hm⟩)
                · exact absurd hw' (by simp)
                · injection hw' with _ hbs
                  simpa [hbs] using hm

/-- Le couple (mot, etiquette) lu par `pathTo` est relu par `labelAt` : les
deux fonctions sont inverses sur le code porte par l'arbre. -/
theorem labelAt_pathTo {n : Nat} (t : LTree n) {s : Fin n} {p : List Bool}
    (h : pathTo t s = some p) : labelAt t p = some s :=
  (labelAt_iff t p s).mpr (pathTo_mem h)

/-- Le contrat du code singleton, ecrit plutot que contourne : une racine
feuille porte le mot vide, et le decodeur du pli 2 refuse une racine feuille.
Le singleton n'est donc pas decode par `decode` — c'est la convention Python a
un bit qui doit le traiter, et elle est explicite ici. -/
theorem leaf_root_contract {n : Nat} (s : Fin n) (bits : List Bool) :
    pairs (.leaf s) = [([], s)] ∧ decode (forget (.leaf s)) bits = none := by
  refine ⟨rfl, ?_⟩
  simp [forget, decode]

/-! ## Round-trip etiquete -/

/-- Encodage d'un message de symboles : suivre le chemin de chacun et
concatener. `none` des qu'un symbole est absent de l'arbre — l'absence est un
echec explicite de l'encodeur, jamais un mot par defaut. -/
def encodeMsg {n : Nat} (t : LTree n) : List (Fin n) → Option (List Bool)
  | [] => some []
  | s :: rest =>
      match pathTo t s with
      | none => none
      | some p => (encodeMsg t rest).map (fun r => p ++ r)

/-- Traduction d'une liste de mots en liste de symboles : echec explicite des
qu'un mot ne finit pas sur une feuille. Ecrite par recursion structurelle
plutot que par `List.mapM`, pour que l'etape `labelAll_cons` se prouve par
reduction. -/
def labelAll {n : Nat} (t : LTree n) : List (List Bool) → Option (List (Fin n))
  | [] => some []
  | w :: ws =>
      match labelAt t w with
      | none => none
      | some s => (labelAll t ws).map (s :: ·)

/-- Etape de traduction : un mot dont l'etiquette est connue passe en tete des
symboles, le reste est traduit a l'identique. -/
theorem labelAll_cons {n : Nat} (t : LTree n) {w : List Bool} {s : Fin n}
    (hw : labelAt t w = some s) (ws : List (List Bool)) :
    labelAll t (w :: ws) = (s :: ·) <$> labelAll t ws := by
  simp only [labelAll, hw]
  rfl

/-- Decodage etiquete : le decodeur du pli 2 rend les mots, `labelAll` les
retraduit en symboles. Le `bind` porte l'echec de bout en bout : un mot du
flux qui ne finit pas sur une feuille fait echouer tout le message. -/
def decodeL {n : Nat} (t : LTree n) (bits : List Bool) : Option (List (Fin n)) :=
  (decode (forget t) bits).bind (labelAll t)

/-- **Etape du round-trip etiquete** : lire un mot `p` du code puis le reste
du flux rend le symbole de `p` en tete des symboles du reste. C'est la forme
etiquetee de `decode_cons`, qui reste l'unique preuve de decodage. -/
theorem decodeL_cons {n : Nat} {t : LTree n} (hf : forget t ≠ .leaf)
    {p : List Bool} {s : Fin n} (hp : pathTo t s = some p) (rest : List Bool) :
    decodeL t (p ++ rest) = (s :: ·) <$> decodeL t rest := by
  have hmem : (p, s) ∈ pairs t := pathTo_mem hp
  have hwleaf : p ∈ leafWords (forget t) := by
    rw [← wordsOf_forget]
    exact List.mem_map_of_mem hmem
  have hstep : decode (forget t) (p ++ rest) =
      (p :: ·) <$> decode (forget t) rest :=
    decode_cons hf hwleaf
  have hlab : labelAt t p = some s := labelAt_pathTo t hp
  simp only [decodeL]
  rw [hstep]
  cases hD : decode (forget t) rest with
  | none => simp
  | some ws => simp [labelAll_cons t hlab ws]

/-- **Round-trip etiquete** : encoder puis decoder un message rend le message,
symbole pour symbole. Les hypotheses sont celles du contrat, aucune autre :
l'arbre n'est pas une feuille (sinon le mot vide boucle) et l'encodage
reussit (sinon un symbole n'a pas de mot). -/
theorem decodeL_encode {n : Nat} {t : LTree n} (hf : forget t ≠ .leaf)
    (msg : List (Fin n)) (bits : List Bool) (h : encodeMsg t msg = some bits) :
    decodeL t bits = some msg := by
  induction msg generalizing bits with
  | nil =>
      simp [encodeMsg] at h
      subst h
      simp [decodeL, decode_nil (forget t) hf, labelAll]
  | cons s rest ih =>
      simp only [encodeMsg] at h
      cases hp : pathTo t s with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some p =>
          rw [hp] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨r, hr, hbits⟩ := h
          rw [← hbits, decodeL_cons hf hp r]
          exact congrArg (fun x => (s :: ·) <$> x) (ih r hr)

/-! ## Ancres d'execution -/

/- Le code canonique a quatre symboles du carnet 02, en arbre etiquete :
longueurs 1, 2, 3, 3 pour a, b, c, d — `a = 1`, `b = 01`, `c = 001`,
`d = 000`. -/
def demoTree : LTree 4 :=
  .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))

#eval wordsOf demoTree
-- [[true], [false, true], [false, false, true], [false, false, false]]

#eval labels demoTree
-- [0, 1, 2, 3]

/- Le message `a d` s'encode en `1 000` puis se relit `a d` : le round-trip
sur un arbre etiquete, execute. -/
#eval encodeMsg demoTree [0, 3]
-- some [true, false, false, false]

#eval decodeL demoTree [true, false, false, false]
-- some [0, 3]

/- Un mot qui ne finit pas sur une feuille n'a pas de symbole : `01` est un
mot, `0` seul est un prefixe interne. -/
#eval labelAt demoTree [false]
-- none

end CompressionLean
