import Mathlib
import PrefixCodes
import Decode
import Huffman
import Optimalite
import HuffmanOptimal

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
   de plus : deux arbres de meme multiensemble de longueurs (meme Kraft) peuvent
   encoder le meme message differemment (`same_multiset_different_message`,
   jalon 2).
6. **Canonisation par etiquette** (jalon 2) : `canonPairs` porte la paire
   (longueur, symbole) — l'ordre total explicite du carnet 02 — avec la
   longueur qui suit le symbole (`canonPairs_fst`), la completude
   (`mem_canonOrder`) et le round-trip canonique prouve par le decodeur du
   jalon 1.
7. **Cout etiquete et optimalite par oubli** (jalon 3) : `costL` lit le cout
   dans `pairs`, `costL_eq_costW` le relie au cout pondere du pli 5 apres
   oubli, et `costL_ge_huffman` obtient l'optimalite en appelant
   `huffman_optimal` — sans redemontrer un pli. **Cas limites** (jalon 4) :
   alphabet vide sans aucun arbre (`no_LTree_zero`), singleton en deux
   conventions mesurees — mot vide a cout nul (Huffman,
   `costL_singleton_empty_word`) contre un bit a deux fois le poids (Python,
   `pythonSingleton`).
8. **Reconstruction canonique** (jalon 5) : `buildCanon` remonte le chemin
   inverse — d'un vecteur de longueurs par symbole vers l'arbre. La
   construction passe par un arbre a trous (`PTree`) et **refuse** les trous a
   la conversion : `LTree` etant total, un code incomplet (Kraft < 1) ne s'y
   represente pas sans etiquette factice. Le compteur est celui du carnet 02
   (`canonWords`), et les deux refus — collision (`buildCanon_refuses_nonKraft`)
   et trou (`buildCanon_refuses_incomplete`) — sont des theoremes, pas des
   commentaires.

Sibling EN : `SymbolCodec_en.lean`, miroir auto-contenu dans le meme
namespace `CompressionLean` (il n'importe pas le fichier FR) — memes enonces
et preuves, docstrings traduites — convention i18n #4980 pattern A.

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

/-! ## Jalon 2 : canonisation par etiquette

Le carnet 02 trie les symboles par `(longueur, symbole)` avant d'attribuer les
mots. Un multiensemble de longueurs ne suffit pas : il ne dit pas **quel**
symbole recoit quelle longueur. Les objets ci-dessous portent la paire, et les
theoremes disent ce que la paire garantit. -/

/-- Longueur maximale sur l'alphabet : borne du balayage qui construit l'ordre
canonique. -/
def maxLen {n : Nat} (len : Fin n → Nat) : Nat :=
  (List.finRange n).foldr (fun s acc => max (len s) acc) 0

/-- Les symboles de longueur `L`, dans l'ordre de l'alphabet. -/
def ofLength {n : Nat} (len : Fin n → Nat) (L : Nat) : List (Fin n) :=
  (List.finRange n).filter (fun s => len s == L)

/-- **Ordre canonique** : longueur croissante, puis indice de symbole croissant
pour les egalites de longueur. C'est l'ordre total explicite sans lequel deux
symboles de meme longueur pourraient etre echanges. -/
def canonPairs {n : Nat} (len : Fin n → Nat) : List (Nat × Fin n) :=
  (List.range (maxLen len + 1)).flatMap
    (fun L => (ofLength len L).map (fun s => (L, s)))

/-- Les symboles dans l'ordre canonique, longueurs croissantes. -/
def canonOrder {n : Nat} (len : Fin n → Nat) : List (Fin n) :=
  (canonPairs len).map Prod.snd

/-- L'image de tout element d'une liste est majoree par le pliage qui prend
le maximum des images. -/
theorem le_foldr_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat) (x : α), x ∈ l →
      f x ≤ l.foldr (fun y acc => max (f y) acc) a
  | [], _, _, hx => by simp at hx
  | y :: t, a, x, hx => by
      show f x ≤ max (f y) (List.foldr (fun y acc => max (f y) acc) a t)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max f t a x hx) (le_max_right _ _)

/-- Toute longueur est majoree par `maxLen`. -/
theorem len_le_maxLen {n : Nat} (len : Fin n → Nat) (s : Fin n) :
    len s ≤ maxLen len :=
  le_foldr_max len (List.finRange n) 0 s (List.mem_finRange s)

/-- Un symbole est dans la classe de longueur `L` si et seulement si sa
longueur est `L`. -/
theorem mem_ofLength {n : Nat} (len : Fin n → Nat) (L : Nat) (s : Fin n) :
    s ∈ ofLength len L ↔ len s = L := by
  unfold ofLength
  simp only [List.mem_filter, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange s, h⟩⟩

/-- **La longueur suit le symbole.** Dans l'ordre canonique, la longueur portee
par une entree est celle de son symbole : c'est le contrat qu'un multiensemble
de longueurs n'etablit pas. -/
theorem canonPairs_fst {n : Nat} {len : Fin n → Nat} {L : Nat} {s : Fin n}
    (h : (L, s) ∈ canonPairs len) : len s = L := by
  unfold canonPairs at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨L', _, s', hs', heq⟩ := h
  cases heq
  exact (mem_ofLength len L s).mp hs'

/-- Aucun symbole de l'alphabet ne manque a l'ordre canonique. -/
theorem mem_canonOrder {n : Nat} (len : Fin n → Nat) (s : Fin n) :
    s ∈ canonOrder len := by
  unfold canonOrder canonPairs
  rw [List.mem_map]
  refine ⟨(len s, s), ?_, rfl⟩
  rw [List.mem_flatMap]
  refine ⟨len s, ?_, ?_⟩
  · rw [List.mem_range]
    exact Nat.lt_succ_of_le (len_le_maxLen len s)
  · rw [List.mem_map]
    exact ⟨s, (mem_ofLength len (len s) s).mpr rfl, rfl⟩

/-! ## Jalon 3 : cout etiquete et cout pondere

Le cout etiquete lit le poids de chaque symbole dans le parcours (`pairs`) :
chaque feuille paie le poids de son symbole fois la longueur de son mot. Le
lien avec le cout pondere du pli 5 est une **egalite apres oubli**
(`costL_eq_costW`), jamais une bijection de symboles : elle compare l'arbre
etiquete a l'arbre pondere qu'il oublie. L'optimalite de Huffman s'obtient
alors **par oubli** (`costL_ge_huffman`) : le trie de `huffman` sur les poids
des etiquettes bat tout arbre etiquete, sans redemontrer un seul pli de la
serie. La terminaison de l'encodeur est structurelle sur le message, celle du
decodeur herite de `Decode.decode` ; le rejet d'un symbole absent est un
echec explicite (`encodeMsg_none_of_absent`). -/

/-- Congruence ponctuelle de `List.map`, prouvee ici pour ne pas dependre
d'un nom de Mathlib. -/
theorem map_congr_pointwise {α β : Type} {f g : α → β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      have hx : f x = g x := h x (by simp)
      have hrest : List.map f t = List.map g t := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, hx, hrest]

/-- La somme d'une somme de fonctions se scinde en deux sommes. -/
theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Preparer un bit devant chaque mot d'un parcours facture exactement une
unite de longueur par feuille : la part du cout par longueur de mot passe
telle quelle, la part par feuille ajoute le poids de chaque etiquette. -/
theorem sum_cost_prefix {n : Nat} (wt : Fin n → Nat) (b : Bool)
    (ls : List (List Bool × Fin n)) :
    ((ls.map (fun p => (b :: p.1, p.2))).map (fun p => wt p.2 * p.1.length)).sum
      = ((ls.map (fun p => wt p.2 * p.1.length)).sum
          + ((ls.map Prod.snd).map wt).sum) := by
  have hcomp : (ls.map (fun p => (b :: p.1, p.2))).map (fun p => wt p.2 * p.1.length)
      = ls.map (fun p => wt p.2 * (b :: p.1).length) := by
    rw [List.map_map]; rfl
  have hcongr : ls.map (fun p => wt p.2 * (b :: p.1).length)
      = ls.map (fun p => wt p.2 * p.1.length + wt p.2) :=
    map_congr_pointwise (fun p _ => by simp only [List.length_cons]; ring)
  have hmap : ls.map (fun p => wt p.2) = ls.map (wt ∘ Prod.snd) :=
    map_congr_pointwise (fun p _ => rfl)
  rw [hcomp, hcongr, sum_map_add, hmap, List.map_map]

/-- **Cout etiquete** : chaque feuille paie le poids de son symbole fois la
longueur de son mot — lu dans `pairs`, donc sur l'association
symbole / mot effectivement portee par l'arbre. -/
def costL {n : Nat} (wt : Fin n → Nat) (t : LTree n) : Nat :=
  ((pairs t).map (fun p => wt p.2 * p.1.length)).sum

/-- Un noeud facture ses deux sous-arbres plus, pour chacun, une unite de
longueur par symbole : descendre d'un cran allonge tous les mots de la
branche. -/
theorem costL_node {n : Nat} (wt : Fin n → Nat) (l r : LTree n) :
    costL wt (.node l r)
      = costL wt l + ((labels l).map wt).sum + costL wt r + ((labels r).map wt).sum := by
  simp only [costL, pairs, labels, List.map_append, List.sum_append]
  rw [sum_cost_prefix wt true (pairs l), sum_cost_prefix wt false (pairs r)]
  omega

/-- **Le cout etiquete est le cout pondere de l'arbre oublie.** Egalite
exacte, pas une borne : le pli 5 (`Optimalite.lean`) definit `costW` par les
fusions, le codec etiquete le lit par les mots — meme nombre, deux lectures. -/
theorem costL_eq_costW {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    costL wt t = costW (toWTree wt t) := by
  induction t with
  | leaf s => simp [costL, pairs, toWTree, costW]
  | node l r ihl ihr =>
      rw [costL_node, ihl, ihr]
      simp only [toWTree, costW]
      rw [weight_toWTree, weight_toWTree]

/-- Les feuilles ponderees de l'arbre oublie sont les poids des etiquettes,
dans l'ordre du parcours. -/
theorem leafWeights_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    List.Perm (leafWeights (toWTree wt t)) ((labels t).map wt) := by
  induction t with
  | leaf s => simp [toWTree, leafWeights, labels, pairs]
  | node l r ihl ihr =>
      simp only [labels, pairs, map_snd_prefix, toWTree, leafWeights,
                 List.map_append]
      exact List.Perm.append ihl ihr

/-- **Optimalite par oubli** : le trie de `huffman` sur les poids des
etiquettes coute moins que tout arbre etiquete portant ces etiquettes. La
preuve est un appel a `huffman_optimal` apres oubli — ce module n'ajoute
AUCUN argument d'optimalite. Et l'inegalite compare des **couts**, pas des
codes : elle ne dit pas que le trie de Huffman realise la meme bijection de
symboles. -/
theorem costL_ge_huffman {n : Nat} (wt : Fin n → Nat) (t : LTree n) :
    costW (huffman ((labels t).map wt)) ≤ costL wt t := by
  rw [costL_eq_costW]
  exact huffman_optimal ((labels t).map wt).length ((labels t).map wt)
    (Nat.le_refl _) (toWTree wt t) (leafWeights_toWTree t wt)

/-- **Le rejet d'une etiquette absente est explicite** : encoder un message
qui contient un symbole sans chemin dans l'arbre echoue sur `none` — jamais
un mot par defaut, jamais un message tronque. -/
theorem encodeMsg_none_of_absent {n : Nat} (t : LTree n) (s : Fin n)
    (habs : pathTo t s = none) :
    ∀ {msg : List (Fin n)}, s ∈ msg → encodeMsg t msg = none := by
  intro msg hmem
  induction msg with
  | nil => simp at hmem
  | cons m rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp only [encodeMsg]
        rw [habs]
      · simp only [encodeMsg]
        cases hp : pathTo t m with
        | none => rfl
        | some p =>
            rw [ih hmem']
            rfl

/-! ## Jalon 4 : alphabet vide et singleton

Les deux cas limites que le carnet Python tranche par convention sont
tranches ici par theoreme. Sur l'alphabet vide, la question ne se pose pas :
aucun arbre n'existe. Sur le singleton, les DEUX conventions coexistent avec
leurs couts mesures : le code prefixe injectif (feuille-racine, mot vide,
cout nul — celui de `huffman` et de `leaf_root_contract`) et la convention
Python a un bit, qui n'est PAS un code injectif et paie deux fois le poids. -/

/-- **Alphabet vide : aucun arbre etiquete n'existe.** La feuille exigerait
un symbole de `Fin 0` (type vide) et le noeud herite de l'impossible sur son
fils gauche. La question d'un code sur alphabet vide est vide de contenu. -/
theorem no_LTree_zero : ∀ t : LTree 0, False
  | .leaf s => s.elim0
  | .node l _ => no_LTree_zero l

/-- **Convention Huffman du singleton** : le code prefixe injectif d'un
alphabet a un symbole est la feuille-racine — mot vide, cout nul. C'est le
cas `ws = [w]` de la preuve d'optimalite (le trie est la feuille, cout
nul), et le contrat que `Decode.decode` rejette (`leaf_root_contract`). -/
theorem costL_singleton_empty_word (wt : Fin 1 → Nat) :
    costL wt (.leaf 0) = 0 := by
  simp [costL, pairs]

/-- **Convention Python du singleton, realisee** : un bit par symbole. Sa
seule realisation arborescente met le symbole sur les DEUX fils — chaque bit
decode vers 0. -/
def pythonSingleton : LTree 1 := .node (.leaf 0) (.leaf 0)

/-- La convention Python a un bit n'est pas un code injectif : le meme
symbole y a deux mots. -/
theorem pythonSingleton_not_nodup : ¬ Nodup pythonSingleton := fun h =>
  absurd (h [true] [false] 0
    (by simp [pythonSingleton, pairs]) (by simp [pythonSingleton, pairs]))
    (by simp)

/-- Et son cout etiquete paie chaque bit : deux fois le poids du symbole,
contre zero pour la convention Huffman. La difference est mesuree, pas
gommee : ce module ne reclame ni l'une ni l'autre comme « la » convention —
il expose les deux. -/
theorem costL_pythonSingleton (wt : Fin 1 → Nat) :
    costL wt pythonSingleton = 2 * wt 0 := by
  rw [pythonSingleton, costL_node, costL_singleton_empty_word]
  simp [labels, pairs]
  omega

#print axioms map_congr_pointwise
#print axioms sum_cost_prefix
#print axioms costL_eq_costW
#print axioms leafWeights_toWTree
#print axioms costL_ge_huffman
#print axioms encodeMsg_none_of_absent
#print axioms no_LTree_zero
#print axioms costL_singleton_empty_word
#print axioms pythonSingleton_not_nodup
#print axioms costL_pythonSingleton

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

/-! ## Jalon 2 : executions et ancres -/

/-- Le code canonique a quatre symboles du carnet 02 : symbole 0 sur un bit,
1 sur deux, 2 et 3 sur trois. L'arbre `demoTree` ci-dessus est exactement ce
code. -/
def demoLengths : Fin 4 → Nat := ![1, 2, 3, 3]

/-- Memes longueurs, mais le symbole 0 est plus long que le 1 : l'ordre
canonique doit les departager par la longueur, pas par l'indice. -/
def demoLengthsSwapped : Fin 4 → Nat := ![2, 1, 3, 3]

#eval canonOrder demoLengths
-- [0, 1, 2, 3]

/- L'ordre trie par longueur, pas par indice : le symbole 1, plus court,
passe devant le 0. Les egalites de longueur (2 et 3) restent dans l'ordre de
l'alphabet. -/
#eval canonOrder demoLengthsSwapped
-- [1, 0, 2, 3]

#eval (canonPairs demoLengthsSwapped).map Prod.fst
-- [1, 2, 3, 3]

/-- **Round-trip canonique** : le message integral se relit apres encodage par
l'arbre canonique. -/
theorem demoTree_roundtrip :
    decodeL demoTree [true, false, true, false, false, true, false, false, false]
      = some [0, 1, 2, 3] :=
  decodeL_encode (by intro h; exact CodeTree.noConfusion h) [0, 1, 2, 3]
    [true, false, true, false, false, true, false, false, false] (by rfl)

/-- **Controle negatif : un multiensemble de longueurs ne fixe pas le codec.**
`swapTree` a la meme forme que `demoTree` — memes mots aux memes positions,
donc meme liste de longueurs et meme Kraft — mais les symboles 1 et 2 sont
echanges, et le message encode change. Un code prefixe n'est pas un mecanisme
d'integrite : il ne detecte pas cette permutation. -/
def swapTree : LTree 4 :=
  .node (.leaf 0) (.node (.leaf 2) (.node (.leaf 1) (.leaf 3)))

theorem same_multiset_different_message :
    (wordsOf swapTree).map List.length = (wordsOf demoTree).map List.length
      ∧ encodeMsg swapTree [1, 2] ≠ encodeMsg demoTree [1, 2] := by
  decide

#print axioms le_foldr_max
#print axioms len_le_maxLen
#print axioms mem_ofLength
#print axioms canonPairs_fst
#print axioms mem_canonOrder
#print axioms demoTree_roundtrip
#print axioms same_multiset_different_message

/-! ## Jalon 5 : reconstruction d'un arbre canonique

Les jalons precedents partent d'un arbre pour en lire les longueurs. Celui-ci
remonte le chemin : etant donne un **vecteur de longueurs par symbole**, il
reconstruit le code canonique du carnet 02.

Une limite de representation gouverne la construction : `LTree` est **total**
(chaque feuille porte un symbole), donc il ne peut representer qu'un code
**complet** — Kraft exactement 1. Un vecteur incomplet ne s'y ecrit pas sans
inventer des etiquettes factices. La reconstruction passe donc par un arbre a
trous, et la conversion finale **refuse** les trous au lieu de les combler. -/

/-- Arbre d'insertion : une feuille est soit un symbole, soit un trou encore
inoccupe. -/
inductive PTree (n : Nat) where
  /-- Feuille : un symbole, ou un trou. -/
  | tip : Option (Fin n) → PTree n
  /-- Noeud interne. -/
  | node : PTree n → PTree n → PTree n
  deriving DecidableEq, Repr

/-- Insertion d'un mot dans l'arbre a trous. Chaque collision est un echec
**explicite** : un mot deja pris (`tip (some _)`) comme un mot qui prefixe un
noeud (`node`, mot vide) rendent `none` — jamais un ecrasement silencieux. Le
bit `true` descend a gauche, la convention de `pairs`. -/
def pinsert {n : Nat} : PTree n → List Bool → Fin n → Option (PTree n)
  | .tip none, [], s => some (.tip (some s))
  | .tip none, b :: rest, s =>
      (pinsert (.tip none) rest s).map fun t =>
        if b then .node t (.tip none) else .node (.tip none) t
  | .tip (some _), _, _ => none
  | .node _ _, [], _ => none
  | .node l r, b :: rest, s =>
      if b then (pinsert l rest s).map fun l' => .node l' r
      else (pinsert r rest s).map fun r' => .node l r'

/-- Conversion finale : un trou est un **refus**. C'est ici qu'un code
incomplet echoue, et non plus loin sous une feuille inventee. -/
def toLTree {n : Nat} : PTree n → Option (LTree n)
  | .tip none => none
  | .tip (some s) => some (.leaf s)
  | .node l r => (toLTree l).bind fun l' => (toLTree r).map fun r' => .node l' r'

/-- Les `width` bits de `mot`, poids fort en tete ; une largeur superieure a la
taille binaire du nombre complete a gauche par des zeros. C'est la convention
du carnet 02 (`format(mot, "0{length}b")`). -/
def bitsOfNat : (width : Nat) → Nat → List Bool
  | 0, _ => []
  | width + 1, mot => bitsOfNat width (mot >>> 1) ++ [mot % 2 == 1]

/-- Le compteur canonique du carnet 02, applique dans l'ordre `canonOrder` :
chaque symbole decale le compteur de `longueur - longueurPrecedente`, prend la
fenetre basse comme mot, puis incremente. -/
def canonWordsAux {n : Nat} (len : Fin n → Nat) :
    Nat → Nat → List (Fin n) → List (List Bool)
  | _, _, [] => []
  | mot, prevLen, s :: rest =>
      let m := mot <<< (len s - prevLen)
      bitsOfNat (len s) m :: canonWordsAux len (m + 1) (len s) rest

/-- Les mots canoniques d'un vecteur de longueurs, dans l'ordre des symboles
de `canonOrder`. -/
def canonWords {n : Nat} (len : Fin n → Nat) : List (List Bool) :=
  canonWordsAux len 0 0 (canonOrder len)

/-- **Reconstruction canonique** : etant donne un vecteur de longueurs par
symbole, rend l'arbre du code canonique, ou `none` des qu'une insertion
collisionne ou qu'un trou subsiste — c'est-a-dire des que le vecteur n'est pas
complet. -/
def buildCanon {n : Nat} (len : Fin n → Nat) : Option (LTree n) :=
  let step (acc : Option (PTree n)) (p : Fin n × List Bool) : Option (PTree n) :=
    acc.bind fun t => pinsert t p.2 p.1
  (((canonOrder len).zip (canonWords len)).foldl step (some (.tip none))).bind
    toLTree

/-- L'arbre que la reconstruction doit rendre pour `demoLengths` : le code
canonique du carnet, ecrit a la main pour que la preuve ait une cible. `true`
descend a gauche, donc le mot « 0 » du carnet (faux) est le fils **droit**. -/
def demoCanonTree : LTree 4 :=
  .node (.node (.node (.leaf 3) (.leaf 2)) (.leaf 1)) (.leaf 0)

/-- **La reconstruction retrouve le code du carnet** : pour les longueurs
1-2-3-3, le symbole 0 prend « 0 », 1 prend « 10 », 2 prend « 110 » et 3 prend
« 111 ». Prouve par evaluation complete du compteur et des insertions — c'est
l'arbre entier qui est fige, pas seulement ses longueurs. -/
theorem buildCanon_demo : buildCanon demoLengths = some demoCanonTree := by
  decide

/-- **Controle positif minimal** : deux symboles de longueur 1 (Kraft = 1) se
reconstruisent en un noeud a deux feuilles, dans l'ordre du compteur. -/
theorem buildCanon_two : buildCanon ![1, 1] = some (.node (.leaf 1) (.leaf 0)) := by
  decide

/-- **Le singleton retombe sur la convention Huffman** : longueur 0, mot vide,
feuille-racine — la meme que `costL_singleton_empty_word`, et non le bit
double de `pythonSingleton`. -/
theorem buildCanon_singleton : buildCanon ![0] = some (.leaf 0) := by
  decide

/-- **Refus par collision** : trois symboles de longueur 1 reclament
3/2 > 1 ; le troisieme mot retombe sur un mot deja pose et la reconstruction
rend `none`. -/
theorem buildCanon_refuses_nonKraft : buildCanon ![1, 1, 1] = none := by
  decide

/-- **Refus par trou** : `![1, 2, 3]` a Kraft 7/8 — aucun mot ne collisionne,
mais une feuille manque, et `LTree` ne sait pas la representer. La
reconstruction refuse plutot que de fabriquer une etiquette. -/
theorem buildCanon_refuses_incomplete : buildCanon ![1, 2, 3] = none := by
  decide

/-- Coherent avec `no_LTree_zero` : sur l'alphabet vide, il n'y a rien a
reconstruire et la reconstruction refuse. -/
theorem buildCanon_zero_alphabet :
    buildCanon (fun _ : Fin 0 => 0) = none := by
  decide

/-- **Longueurs preservees** : relues dans l'arbre reconstruit, les longueurs
sont celles du vecteur, symbole par symbole. La preuve porte sur l'instance
concrete — le cas general « tout vecteur complet » n'est pas reclame ici. -/
theorem demoCanon_lengths :
    ((pairs demoCanonTree).map fun p => (p.2, p.1.length))
      = [(3, 3), (2, 3), (1, 2), (0, 1)] := by
  decide

/-- **Round-trip apres reconstruction** : le message encode par l'arbre
reconstruit se relit, avec le moteur du jalon 1 (`decodeL_encode`) et non par
evaluation ; le message couvre les quatre feuilles. -/
theorem demoCanon_roundtrip :
    decodeL demoCanonTree [true, true, true, true, true, false, true, false, false]
      = some [3, 2, 1, 0] :=
  decodeL_encode (by intro h; exact CodeTree.noConfusion h) [3, 2, 1, 0]
    [true, true, true, true, true, false, true, false, false] (by rfl)

/-! ### Ancres de la reconstruction -/

/- Les mots du compteur canonique pour les longueurs 1-2-3-3 : c'est
exactement la table du carnet 02 (`code_canonique`), ecrite en bits. -/
#eval canonWords demoLengths

/- L'arbre reconstruit, puis ses mots relus par le parcours du jalon 1. -/
#eval buildCanon demoLengths
#eval wordsOf demoCanonTree

/- Les trois refus, a l'execution : collision, trou, alphabet vide. -/
#eval buildCanon ![1, 1, 1]
#eval buildCanon ![1, 2, 3]
#eval buildCanon (fun _ : Fin 0 => 0)

#print axioms buildCanon_demo
#print axioms buildCanon_two
#print axioms buildCanon_singleton
#print axioms buildCanon_refuses_nonKraft
#print axioms buildCanon_refuses_incomplete
#print axioms buildCanon_zero_alphabet
#print axioms demoCanon_lengths
#print axioms demoCanon_roundtrip

end CompressionLean
