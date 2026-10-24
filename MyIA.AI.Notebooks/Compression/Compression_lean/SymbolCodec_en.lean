import SymbolCodec

open CompressionLean

/-!
# SymbolCodec — labelled codec: the symbol, not only its weight (EPIC #18706)

The previous folds built the code, never the **alphabet**. `WTree`
(`Huffman.lean`) carries a weight per leaf and `toCodeTree` forgets it;
`depthsW` returns a band of lengths; `Decode.lean` proves the round-trip on a
list of leaf **words**. None of these objects links a word to a **symbol**:
two symbols of equal weight are indistinguishable there, and a permutation of
labels leaves both cost and Kraft invariant.

This module adds the labelled layer, and only that layer: it re-proves neither
Kraft, nor McMillan, nor Huffman optimality, and it does not duplicate the
decoding theory — it **calls** it.

1. **Labelled tree** (`LTree n`): each leaf carries a symbol of `Fin n`.
   `pairs` walks the tree depth-first left and returns the word and its label
   **aligned on the same walk**. That alignment carries the contract: `wordsOf`
   and `labels` are the two projections of one single list, so the association
   symbol / word / depth cannot drift.
2. **Forgetful maps** (`forget`, `toWTree`): forgetting the labels yields the
   `CodeTree` of fold 1 — `wordsOf_forget` proves the words are **the same**,
   not merely of the same length; forgetting into a `WTree` yields the weights
   per symbol, and `depthsW_toWTree` yields each word's depth **in symbol
   order**.
3. **Labelled encoding and decoding** (`encodeMsg`, `decodeL`): `encodeMsg`
   follows a symbol's path (`pathTo`), `decodeL` decodes the stream with the
   fold-2 decoder (`decode`) then reads back the label of each word it read
   (`labelAt`). The round-trip `decodeL_encode` composes the two under
   explicit hypotheses: the tree is not reduced to a leaf, and encoding
   succeeds.
4. **The empty-word and singleton contract**: a leaf root carries the empty
   word, and `Decode.decode` **rejects** it (`decode .leaf _ = none`). This
   module keeps that convention instead of working around it:
   `leaf_root_contract` states it, and no theorem here claims at once the
   unconstrained optimality of the empty word and the one-bit Python
   convention.
5. **Negative controls**: a tree is **not** an integrity mechanism. `Nodup`
   (unique labels) and `pairs_fst_inj` state what a codec guarantees — a word
   encodes only one symbol, a symbol has only one word — and nothing more: a
   permutation of labels of equal weight keeps cost and Kraft while changing
   the message (`swap_labels_message`).

EN sibling of `SymbolCodec.lean` (namespace `CompressionLean_en`), consumer
pattern: the FR module is imported and its identifiers reused — convention
i18n #4980.

See #22377 (part of #18706).
-/

namespace CompressionLean_en

/-! ## Labelled tree and aligned walk -/

/-- Binary tree whose every leaf carries a symbol of the alphabet `Fin n`.
Weight and depth are not fields: they are read from the walk (`pairs`), which
forbids carrying a label the walk would contradict. -/
inductive LTree (n : Nat) where
  /-- Leaf: a symbol of the alphabet. -/
  | leaf (s : Fin n) : LTree n
  /-- Internal node: the two subtrees. -/
  | node : LTree n → LTree n → LTree n
  deriving DecidableEq, Repr

/-- Rename the symbols by a map of the alphabet into itself. Used for the
negative control: a permutation leaves the code intact. -/
def mapSym {n : Nat} (σ : Fin n → Fin n) : LTree n → LTree n
  | .leaf s => .leaf (σ s)
  | .node l r => .node (mapSym σ l) (mapSym σ r)

/-- Depth-first left walk: for each leaf, its word (the path from the root,
`true` = left as in `leafWords`) **and** its label, in the same list entry.
Everything below projects that single list. -/
def pairs {n : Nat} : LTree n → List (List Bool × Fin n)
  | .leaf s => [([], s)]
  | .node l r =>
      (pairs l).map (fun p => (true :: p.1, p.2)) ++
      (pairs r).map (fun p => (false :: p.1, p.2))

/-- The codewords carried by the labelled tree, in walk order. -/
def wordsOf {n : Nat} (t : LTree n) : List (List Bool) := (pairs t).map Prod.fst

/-- The leaf labels, in walk order: `labels t` and `wordsOf t` have the same
length and correspond index by index. -/
def labels {n : Nat} (t : LTree n) : List (Fin n) := (pairs t).map Prod.snd

/-- **Unique labels**: each symbol occurs at most once in the tree. This is
what makes a labelled tree a *code* over the alphabet rather than a plain list
of leaves. -/
def Nodup {n : Nat} (t : LTree n) : Prop :=
  ∀ (p q : List Bool) (s : Fin n), (p, s) ∈ pairs t → (q, s) ∈ pairs t → p = q

/-! ## Forgetful maps -/

/-- Forget the labels: the code tree of fold 1. -/
def forget {n : Nat} : LTree n → CodeTree
  | .leaf _ => .leaf
  | .node l r => .node (forget l) (forget r)

/-- Forget the labels while keeping the weights: the weighted tree of fold 4,
where a leaf's weight is the frequency of its symbol. -/
def toWTree {n : Nat} (wt : Fin n → Nat) : LTree n → WTree
  | .leaf s => .leaf (wt s)
  | .node l r => .node (toWTree wt l) (toWTree wt r)

/-! ## Walk lemmas -/

/-- Projecting the word after prefixing a bit is projecting then prefixing —
the form that aligns `pairs` and `leafWords`. -/
theorem map_fst_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map Prod.fst =
    (l.map Prod.fst).map (b :: ·) := by
  simp [List.map_map, Function.comp_def]

/-- Projecting the label after prefixing a bit leaves the labels unchanged:
depth is never a label. -/
theorem map_snd_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map Prod.snd = l.map Prod.snd := by
  simp [List.map_map, Function.comp_def]

/-- Projecting the length after prefixing a bit adds `1` to every length —
the symbol / depth association, on the length side. -/
theorem map_length_prefix {n : Nat} (b : Bool) (l : List (List Bool × Fin n)) :
    (l.map (fun p => (b :: p.1, p.2))).map (fun p => p.1.length) =
    (l.map (fun p => p.1.length)).map (· + 1) := by
  simp [List.map_map, Function.comp_def]

/-- **The words of the labelled tree are those of its forgetful image**: the
labelled layer neither invents nor loses any word. This is the bridge to
`leafWords_prefixFree` and `decode_encode` of fold 2. -/
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

/-- **Depths in symbol order**: forgetting into a weighted tree yields exactly
the word lengths of `pairs`, leaf by leaf. The symbol / depth association is
therefore carried by the same list as the words. -/
theorem depthsW_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    depthsW (toWTree wt t) = (pairs t).map (fun p => p.1.length) := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      simp only [toWTree, depthsW, pairs, List.map_append, map_length_prefix,
        ihl, ihr]

/-- **The weighted tree's weight is the sum of the frequencies of the symbols
it carries**: forgetting into `WTree` loses no weight on the way. -/
theorem weight_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    weight (toWTree wt t) = ((labels t).map wt).sum := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      simp only [toWTree, weight, labels, pairs, List.map_append,
        map_snd_prefix, List.sum_append, ihl, ihr]

/-- Renaming the symbols leaves the words unchanged: the label permutation is
invisible to the code itself. -/
theorem wordsOf_mapSym {n : Nat} (σ : Fin n → Fin n) (t : LTree n) :
    wordsOf (mapSym σ t) = wordsOf t := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      have h1 : (pairs (mapSym σ l)).map Prod.fst = (pairs l).map Prod.fst := ihl
      have h2 : (pairs (mapSym σ r)).map Prod.fst = (pairs r).map Prod.fst := ihr
      simp only [mapSym, wordsOf, pairs, List.map_append]
      rw [map_fst_prefix, map_fst_prefix, map_fst_prefix, map_fst_prefix, h1, h2]

/-- Renaming the symbols renames the labels, in the same order: the message
half of the negative control. -/
theorem labels_mapSym {n : Nat} (σ : Fin n → Fin n) (t : LTree n) :
    labels (mapSym σ t) = (labels t).map σ := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
      have h1 : (pairs (mapSym σ l)).map Prod.snd = ((pairs l).map Prod.snd).map σ := ihl
      have h2 : (pairs (mapSym σ r)).map Prod.snd = ((pairs r).map Prod.snd).map σ := ihr
      simp only [mapSym, labels, pairs, List.map_append]
      rw [map_snd_prefix, map_snd_prefix, map_snd_prefix, map_snd_prefix, h1, h2]

/-! ## Decomposing the walk of a node -/

/-- The walk of a node, read by word: a word of the left subtree starts with
`true`, a word of the right subtree with `false`. This is the form that makes
the cases of a node decidable. -/
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

/-- A node never carries the empty word: all its words start with a bit. This
is what separates the leaf root (singleton code) from the rest. -/
theorem node_fst_ne_nil {n : Nat} {l r : LTree n} {w : List Bool} {s : Fin n}
    (h : (w, s) ∈ pairs (.node l r)) : w ≠ [] := by
  rcases (mem_pairs_node l r w s).mp h with ⟨w', rfl, _⟩ | ⟨w', rfl, _⟩ <;> simp

/-- **Each word encodes only one symbol**: two leaves of the same word carry
the same label. A structural property of the walk, with no hypothesis — this
is what makes decoding deterministic. -/
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

/-! ## Unique labels: what they buy -/

/-- A leaf has a single label: `Nodup` is immediate there. -/
theorem nodup_leaf {n : Nat} (s : Fin n) : Nodup (.leaf s) := by
  intro p q s' hp hq
  simp only [pairs, List.mem_singleton, Prod.mk.injEq] at hp hq
  rw [hp.1, hq.1]

/-- Under unique labels, two leaves of the same label are the same leaf: the
code is **injective over the alphabet**. Without it, a symbol may occur under
two words (`LTree` allows it), and `pathTo` would pick only one. -/
theorem pairs_snd_inj {n : Nat} {t : LTree n} (h : Nodup t) {p q : List Bool}
    {s : Fin n} (hp : (p, s) ∈ pairs t) (hq : (q, s) ∈ pairs t) : p = q :=
  h p q s hp hq

/-! ## Paths: encoding a symbol -/

/-- A symbol's path in the tree: `some p` if `s` is the leaf of `p`, `none` if
the symbol is not in the carried alphabet. Depth-first first occurrence: under
`Nodup`, the occurrence is unique. -/
def pathTo {n : Nat} : LTree n → Fin n → Option (List Bool)
  | .leaf s, s' => if s = s' then some [] else none
  | .node l r, s' =>
      match pathTo l s' with
      | some p => some (true :: p)
      | none => (pathTo r s').map (false :: ·)

/-- Every path returned by `pathTo` is a word of the code. -/
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

/-- No label is lost: a symbol present in the tree has a path. -/
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

/-! ## Labels: decoding a word -/

/-- The label carried by a word: walk the path down, return the reached leaf's
label. `none` if the path does not end on a leaf (a strict prefix of a word, or
an over-long word) — rejection is explicit, never a default symbol. -/
def labelAt {n : Nat} : LTree n → List Bool → Option (Fin n)
  | .leaf s, [] => some s
  | .leaf _, _ :: _ => none
  | .node _ _, [] => none
  | .node l _, true :: bs => labelAt l bs
  | .node _ r, false :: bs => labelAt r bs

/-- **`labelAt` and `pairs` describe the same correspondence**: a word carries
the label `s` if and only if the pair occurs in the walk. No hypothesis: it is
a property of the walk, not of the code. -/
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

/-- The (word, label) pair read by `pathTo` is read back by `labelAt`: the two
functions are inverses on the code carried by the tree. -/
theorem labelAt_pathTo {n : Nat} (t : LTree n) {s : Fin n} {p : List Bool}
    (h : pathTo t s = some p) : labelAt t p = some s :=
  (labelAt_iff t p s).mpr (pathTo_mem h)

/-- The singleton-code contract, stated instead of worked around: a leaf root
carries the empty word, and the fold-2 decoder rejects a leaf root. The
singleton is therefore not decoded by `decode` — the one-bit Python convention
must handle it, and that is explicit here. -/
theorem leaf_root_contract {n : Nat} (s : Fin n) (bits : List Bool) :
    pairs (.leaf s) = [([], s)] ∧ decode (forget (.leaf s)) bits = none := by
  refine ⟨rfl, ?_⟩
  simp [forget, decode]

/-! ## Labelled round-trip -/

/-- Encoding a message of symbols: follow each one's path and concatenate.
`none` as soon as a symbol is absent from the tree — absence is an explicit
encoder failure, never a default word. -/
def encodeMsg {n : Nat} (t : LTree n) : List (Fin n) → Option (List Bool)
  | [] => some []
  | s :: rest =>
      match pathTo t s with
      | none => none
      | some p => (encodeMsg t rest).map (fun r => p ++ r)

/-- Translating a list of words into a list of symbols: each word is looked up
by `labelAt`. The walk is structural on the list of words, so it composes with
the structural walk of the fold-2 decoder; `none` anywhere fails the whole
message. -/
def labelAll {n : Nat} (t : LTree n) : List (List Bool) → Option (List (Fin n))
  | [] => some []
  | w :: ws =>
      match labelAt t w with
      | none => none
      | some s => (labelAll t ws).map (s :: ·)

/-- **Translation step**: a word whose label is `s` yields `s` in front of the
symbols of the remaining words. -/
theorem labelAll_cons {n : Nat} (t : LTree n) {w : List Bool} {s : Fin n}
    (hw : labelAt t w = some s) (ws : List (List Bool)) :
    labelAll t (w :: ws) = (s :: ·) <$> labelAll t ws := by
  simp only [labelAll, hw]
  rfl

/-- Labelled decoding: the fold-2 decoder yields the words, `labelAt`
translates them back into symbols. The `bind` carries failure end to end: a
word of the stream that does not end on a leaf fails the whole message. -/
def decodeL {n : Nat} (t : LTree n) (bits : List Bool) : Option (List (Fin n)) :=
  (decode (forget t) bits).bind (labelAll t)

/-- **Labelled round-trip step**: reading a codeword `p` and then the rest of
the stream yields the symbol of `p` in front of the symbols of the rest. This
is the labelled form of `decode_cons`, which remains the only decoding proof. -/
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

/-- **Labelled round-trip**: encoding then decoding a message yields the
message, symbol by symbol. The hypotheses are the contract's, no others: the
tree is not a leaf (otherwise the empty word loops) and encoding succeeds
(otherwise some symbol has no word). -/
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

/-! ## Execution anchors -/

/- The canonical four-symbol code of notebook 02, as a labelled tree: lengths
1, 2, 3, 3 for a, b, c, d — `a = 1`, `b = 01`, `c = 001`, `d = 000`. -/
def demoTree : LTree 4 :=
  .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))

#eval wordsOf demoTree
-- [[true], [false, true], [false, false, true], [false, false, false]]

#eval labels demoTree
-- [0, 1, 2, 3]

/- The message `a d` encodes to `1 000` and reads back as `a d`: the
round-trip on a labelled tree, executed. -/
#eval encodeMsg demoTree [0, 3]
-- some [true, false, false, false]

#eval decodeL demoTree [true, false, false, false]
-- some [0, 3]

/- A word that does not end on a leaf has no symbol: `01` is a word, `0` alone
is an internal prefix. -/
#eval labelAt demoTree [false]
-- none

end CompressionLean_en
