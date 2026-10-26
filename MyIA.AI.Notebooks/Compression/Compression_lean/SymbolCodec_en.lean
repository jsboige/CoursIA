import Mathlib
import PrefixCodes
import Decode
import Huffman
import Optimalite
import HuffmanOptimal

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
   encodes only one symbol, a symbol has only one word — and nothing more:
   two trees with the same multiset of lengths (same Kraft) can encode the
   same message differently (`same_multiset_different_message`, milestone 2).
6. **Canonicalization by label** (milestone 2): `canonPairs` carries the pair
   (length, symbol) — the explicit total order of notebook 02 — with the
   length following the symbol (`canonPairs_fst`), completeness
   (`mem_canonOrder`), and the canonical round-trip proved through the
   milestone-1 decoder.
7. **Labelled cost and optimality by forgetting** (milestone 3): `costL` reads
   the cost from `pairs`, `costL_eq_costW` relates it to the weighted cost
   of fold 5 after forgetting, and `costL_ge_huffman` obtains optimality by
   calling `huffman_optimal` — without re-proving a single fold. **Edge
   cases** (milestone 4): the empty alphabet has no tree at all
   (`no_LTree_zero`); the singleton comes in three measured, non-confused
   terms — empty word at zero cost (Huffman, `costL_singleton_empty_word`);
   a single one-bit word, injective and of cost `wt s` for the notebook's
   native codec, with no total representation
   (`one_bit_singleton_has_no_total_tree`); and the total witness
   `duplicatedLeaf`, non-injective (`duplicatedLeaf_not_nodup`) and at twice
   the weight (`costL_duplicatedLeaf`).

EN sibling of `SymbolCodec.lean`, self-contained mirror in the same namespace
`CompressionLean` (it does not import the FR file) — identical statements
and proofs, translated docstrings — i18n convention #4980 pattern A.

8. **Canonical reconstruction** (milestone 5): `buildCanon` walks the inverse
   path — from a length vector per symbol back to the tree. The construction
   goes through a tree with holes (`PTree`) and **refuses** holes at the final
   conversion: `LTree` being total, an incomplete code (Kraft < 1) cannot be
   represented in it without inventing labels. The counter is the one of
   notebook 02 (`canonWords`), and the two refusals — collision
   (`buildCanon_refuses_nonKraft`) and hole (`buildCanon_refuses_incomplete`) —
   are theorems, not comments.

See #22377 (part of #18706).
-/

namespace CompressionLean

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

/-! ## Milestone 2: canonicalization by label

Notebook 02 sorts symbols by `(length, symbol)` before assigning words. A
multiset of lengths does not suffice: it does not say **which** symbol gets
which length. The objects below carry the pair, and the theorems say what the
pair guarantees. -/

/-- Maximum length over the alphabet: bound of the sweep that builds the
canonical order. -/
def maxLen {n : Nat} (len : Fin n → Nat) : Nat :=
  (List.finRange n).foldr (fun s acc => max (len s) acc) 0

/-- The symbols of length `L`, in alphabet order. -/
def ofLength {n : Nat} (len : Fin n → Nat) (L : Nat) : List (Fin n) :=
  (List.finRange n).filter (fun s => len s == L)

/-- **Canonical order**: length increasing, then symbol index increasing for
length ties. This is the explicit total order without which two symbols of
the same length could be exchanged. -/
def canonPairs {n : Nat} (len : Fin n → Nat) : List (Nat × Fin n) :=
  (List.range (maxLen len + 1)).flatMap
    (fun L => (ofLength len L).map (fun s => (L, s)))

/-- The symbols in canonical order, lengths nondecreasing. -/
def canonOrder {n : Nat} (len : Fin n → Nat) : List (Fin n) :=
  (canonPairs len).map Prod.snd

/-- The image of every element of a list is bounded by the fold that takes
the maximum of the images. -/
theorem le_foldr_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat) (x : α), x ∈ l →
      f x ≤ l.foldr (fun y acc => max (f y) acc) a
  | [], _, _, hx => by simp at hx
  | y :: t, a, x, hx => by
      show f x ≤ max (f y) (List.foldr (fun y acc => max (f y) acc) a t)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max f t a x hx) (le_max_right _ _)

/-- Every length is bounded by `maxLen`. -/
theorem len_le_maxLen {n : Nat} (len : Fin n → Nat) (s : Fin n) :
    len s ≤ maxLen len :=
  le_foldr_max len (List.finRange n) 0 s (List.mem_finRange s)

/-- A symbol is in the length class `L` if and only if its length is `L`. -/
theorem mem_ofLength {n : Nat} (len : Fin n → Nat) (L : Nat) (s : Fin n) :
    s ∈ ofLength len L ↔ len s = L := by
  unfold ofLength
  simp only [List.mem_filter, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange s, h⟩⟩

/-- **The length follows the symbol.** In the canonical order, the length
carried by an entry is that of its symbol: this is the contract a multiset
of lengths does not establish. -/
theorem canonPairs_fst {n : Nat} {len : Fin n → Nat} {L : Nat} {s : Fin n}
    (h : (L, s) ∈ canonPairs len) : len s = L := by
  unfold canonPairs at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨L', _, s', hs', heq⟩ := h
  cases heq
  exact (mem_ofLength len L s).mp hs'

/-- No symbol of the alphabet is missing from the canonical order. -/
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

/-! ## Milestone 3: labelled cost and weighted cost

The labelled cost reads each symbol's weight from the walk (`pairs`): each
leaf pays its symbol's weight times its word's length. The link with the
weighted cost of fold 5 is an **equality after forgetting**
(`costL_eq_costW`), never a bijection of symbols: it compares the labelled
tree with the weighted tree it forgets. Huffman's optimality is then obtained
**by forgetting** (`costL_ge_huffman`): the `huffman` trie on the labels'
weights beats every labelled tree, without re-proving a single fold of the
series. The encoder's termination is structural on the message, the
decoder's is inherited from `Decode.decode`; the rejection of an absent
symbol is an explicit failure (`encodeMsg_none_of_absent`). -/

/-- Pointwise congruence for `List.map`, proved here so as not to depend
on a Mathlib name. -/
theorem map_congr_pointwise {α β : Type} {f g : α → β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      have hx : f x = g x := h x (by simp)
      have hrest : List.map f t = List.map g t := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, hx, hrest]

/-- The sum of a sum of functions splits into two sums. -/
theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Prepending a bit before every word of a walk charges exactly one unit of
length per leaf: the per-word-length share of the cost passes through
unchanged, the per-leaf share adds each label's weight. -/
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

/-- **Labelled cost**: each leaf pays its symbol's weight times its word's
length — read from `pairs`, hence on the symbol / word association the
tree actually carries. -/
def costL {n : Nat} (wt : Fin n → Nat) (t : LTree n) : Nat :=
  ((pairs t).map (fun p => wt p.2 * p.1.length)).sum

/-- A node charges its two subtrees plus, for each, one unit of length per
symbol: going one level down lengthens every word of the branch. -/
theorem costL_node {n : Nat} (wt : Fin n → Nat) (l r : LTree n) :
    costL wt (.node l r)
      = costL wt l + ((labels l).map wt).sum + costL wt r + ((labels r).map wt).sum := by
  simp only [costL, pairs, labels, List.map_append, List.sum_append]
  rw [sum_cost_prefix wt true (pairs l), sum_cost_prefix wt false (pairs r)]
  omega

/-- **The labelled cost is the weighted cost of the forgotten tree.** An
exact equality, not a bound: fold 5 (`Optimalite.lean`) defines `costW` by
the merges, the labelled codec reads it by the words — same number, two
readings. -/
theorem costL_eq_costW {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    costL wt t = costW (toWTree wt t) := by
  induction t with
  | leaf s => simp [costL, pairs, toWTree, costW]
  | node l r ihl ihr =>
      rw [costL_node, ihl, ihr]
      simp only [toWTree, costW]
      rw [weight_toWTree, weight_toWTree]

/-- The weighted leaves of the forgotten tree are the labels' weights, in
walk order. -/
theorem leafWeights_toWTree {n : Nat} (t : LTree n) (wt : Fin n → Nat) :
    List.Perm (leafWeights (toWTree wt t)) ((labels t).map wt) := by
  induction t with
  | leaf s => simp [toWTree, leafWeights, labels, pairs]
  | node l r ihl ihr =>
      simp only [labels, pairs, map_snd_prefix, toWTree, leafWeights,
                 List.map_append]
      exact List.Perm.append ihl ihr

/-- **Optimality by forgetting**: the `huffman` trie on the labels' weights
costs no more than any labelled tree carrying those labels. The proof is
one call to `huffman_optimal` after forgetting — this module adds NO
optimality argument of its own. And the inequality compares **costs**, not
codes: it does not say the Huffman trie realizes the same bijection of
symbols. -/
theorem costL_ge_huffman {n : Nat} (wt : Fin n → Nat) (t : LTree n) :
    costW (huffman ((labels t).map wt)) ≤ costL wt t := by
  rw [costL_eq_costW]
  exact huffman_optimal ((labels t).map wt).length ((labels t).map wt)
    (Nat.le_refl _) (toWTree wt t) (leafWeights_toWTree t wt)

/-- **The rejection of an absent label is explicit**: encoding a message
that contains a symbol with no path in the tree fails with `none` — never a
default word, never a truncated message. -/
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

/-! ## Milestone 4: empty and singleton alphabets

The two edge cases that the Python notebook settles by convention are settled
here by theorem. On the empty alphabet the question does not arise: no tree
exists. On the singleton, THREE terms are measured and not confused: the
injective prefix code (root leaf, empty word, zero cost — the one of `huffman`
and of `leaf_root_contract`); the REAL singleton of notebook 02 — a single
one-bit word, injective, of cost `wt s`, and incomplete (Kraft 1/2): it has no
total representation, which is what `one_bit_singleton_has_no_total_tree`
states; and the total witness `duplicatedLeaf`, which duplicates the label to
fill the tree — non-injective, doubled cost. -/

/-- **Empty alphabet: no labelled tree exists.** A leaf would require a
symbol of `Fin 0` (an empty type) and a node inherits the impossibility
from its left child. The question of a code on an empty alphabet is empty
of content. -/
theorem no_LTree_zero : ∀ t : LTree 0, False
  | .leaf s => s.elim0
  | .node l _ => no_LTree_zero l

/-- **Huffman's singleton convention**: the injective prefix code of a
one-symbol alphabet is the leaf root — empty word, zero cost. This is the
`ws = [w]` case of the optimality proof (the trie is the leaf, zero cost),
and the contract that `Decode.decode` rejects (`leaf_root_contract`). -/
theorem costL_singleton_empty_word (wt : Fin 1 → Nat) :
    costL wt (.leaf 0) = 0 := by
  simp [costL, pairs]

/-- The walk of a tree is never empty: every leaf yields one entry, every node
yields at least two. -/
theorem pairs_not_nil {n : Nat} : ∀ t : LTree n, pairs t ≠ []
  | .leaf _ => by simp [pairs]
  | .node l r => by
      intro h
      simp only [pairs] at h
      cases hl : pairs l with
      | nil => exact absurd hl (pairs_not_nil l)
      | cons x xs =>
          rw [hl] at h
          simp at h

/-- **The notebook's one-bit singleton has no total tree.** The native codec
(`huffman` on one symbol) returns a dictionary with a single one-bit word —
injective, of cost `wt s`, incomplete (Kraft 1/2). `LTree` being total, that
code cannot be represented in it: a tree on one symbol is either the root leaf
(empty word), or a node whose every subtree carries at least one word — hence
at least two entries, never a single one-bit one. The cost and injectivity
confrontation with the native codec lives in the companion Python test; the
`duplicatedLeaf` tree below is the closest TOTAL witness, not that codec. -/
theorem one_bit_singleton_has_no_total_tree (b : Bool) (t : LTree 1) :
    pairs t ≠ [([b], 0)] := by
  cases t with
  | leaf s =>
      fin_cases s
      cases b <;> simp [pairs]
  | node l r =>
      have hl : (pairs l).length ≠ 0 :=
        fun hp => pairs_not_nil l (List.length_eq_zero_iff.mp hp)
      have hr : (pairs r).length ≠ 0 :=
        fun hp => pairs_not_nil r (List.length_eq_zero_iff.mp hp)
      intro h
      have hlen : 2 ≤ (pairs (.node l r)).length := by
        simp only [pairs, List.map_append, List.length_append, List.length_map]
        omega
      rw [h] at hlen
      simp at hlen

/-- **Total-tree witness with a duplicated label**: the symbol on both
children. This is NOT the codec of notebook 02 — that one returns a single
one-bit word and has no total representation
(`one_bit_singleton_has_no_total_tree`). This witness is the closest total
tree: it fills both children at the price of duplication. -/
def duplicatedLeaf : LTree 1 := .node (.leaf 0) (.leaf 0)

/-- The witness tree with a duplicated label is not an injective code: the same
symbol has two words there. That is the witness's defect, not the native
codec's (which is injective). -/
theorem duplicatedLeaf_not_nodup : ¬ Nodup duplicatedLeaf := fun h =>
  absurd (h [true] [false] 0
    (by simp [duplicatedLeaf, pairs]) (by simp [duplicatedLeaf, pairs]))
    (by simp)

/-- And its labelled cost pays every bit: twice the symbol's weight — against
exactly `wt s` for the notebook's native codec (a single one-bit word), and
zero for the root leaf. All three values are measured, not smoothed over. -/
theorem costL_duplicatedLeaf (wt : Fin 1 → Nat) :
    costL wt duplicatedLeaf = 2 * wt 0 := by
  rw [duplicatedLeaf, costL_node, costL_singleton_empty_word]
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
#print axioms pairs_not_nil
#print axioms one_bit_singleton_has_no_total_tree
#print axioms duplicatedLeaf_not_nodup
#print axioms costL_duplicatedLeaf

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

/-! ## Milestone 2: executions and anchors -/

/-- The four-symbol canonical code of notebook 02: symbol 0 on one bit,
1 on two, 2 and 3 on three. The tree `demoTree` above is exactly this
code. -/
def demoLengths : Fin 4 → Nat := ![1, 2, 3, 3]

/-- Same lengths, but symbol 0 is longer than 1: the canonical order must
separate them by length, not by index. -/
def demoLengthsSwapped : Fin 4 → Nat := ![2, 1, 3, 3]

#eval canonOrder demoLengths
-- [0, 1, 2, 3]

/- The order sorts by length, not by index: symbol 1, being shorter, comes
before 0. Length ties (2 and 3) stay in alphabet order. -/
#eval canonOrder demoLengthsSwapped
-- [1, 0, 2, 3]

#eval (canonPairs demoLengthsSwapped).map Prod.fst
-- [1, 2, 3, 3]

/-- **Canonical round-trip**: the full message reads back after encoding by
the canonical tree. -/
theorem demoTree_roundtrip :
    decodeL demoTree [true, false, true, false, false, true, false, false, false]
      = some [0, 1, 2, 3] :=
  decodeL_encode (by intro h; exact CodeTree.noConfusion h) [0, 1, 2, 3]
    [true, false, true, false, false, true, false, false, false] (by rfl)

/-- **Negative control: a multiset of lengths does not fix the codec.**
`swapTree` has the same shape as `demoTree` — same words at the same
positions, hence the same length list and the same Kraft — but symbols 1
and 2 are exchanged, and the encoded message changes. A prefix code is not
an integrity mechanism: it does not detect this permutation. -/
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

/-! ## Milestone 5: canonical tree reconstruction

The previous milestones start from a tree and read its lengths. This one walks
the other way: given a **length vector per symbol**, it rebuilds the canonical
code of notebook 02.

One representational limit governs the construction: `LTree` is **total**
(every leaf carries a symbol), so it can only represent a **complete** code —
Kraft exactly 1. An incomplete vector cannot be written in it without
inventing fake labels. The reconstruction therefore goes through a tree with
holes, and the final conversion **refuses** holes instead of filling them. -/

/-- Insertion tree: a leaf is either a symbol or a still-unoccupied hole. -/
inductive PTree (n : Nat) where
  /-- Leaf: a symbol, or a hole. -/
  | tip : Option (Fin n) → PTree n
  /-- Internal node. -/
  | node : PTree n → PTree n → PTree n
  deriving DecidableEq, Repr

/-- Insertion of a word into the tree with holes. Every collision is an
**explicit** failure: an already taken word (`tip (some _)`) as well as a word
that prefixes a node (`node`, empty word) yield `none` — never a silent
overwrite. The `true` bit descends to the left, the convention of `pairs`. -/
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

/-- Final conversion: a hole is a **refusal**. This is where an incomplete code
fails, rather than further down under an invented leaf. -/
def toLTree {n : Nat} : PTree n → Option (LTree n)
  | .tip none => none
  | .tip (some s) => some (.leaf s)
  | .node l r => (toLTree l).bind fun l' => (toLTree r).map fun r' => .node l' r'

/-- The `width` bits of `mot`, most significant first; a width larger than the
binary size of the number pads with zeros on the left. This is the convention
of notebook 02 (`format(mot, "0{length}b")`). -/
def bitsOfNat : (width : Nat) → Nat → List Bool
  | 0, _ => []
  | width + 1, mot => bitsOfNat width (mot >>> 1) ++ [mot % 2 == 1]

/-- The canonical counter of notebook 02, applied in the `canonOrder` order:
each symbol shifts the counter by `length - previousLength`, takes the low
window as its word, then increments. -/
def canonWordsAux {n : Nat} (len : Fin n → Nat) :
    Nat → Nat → List (Fin n) → List (List Bool)
  | _, _, [] => []
  | mot, prevLen, s :: rest =>
      let m := mot <<< (len s - prevLen)
      bitsOfNat (len s) m :: canonWordsAux len (m + 1) (len s) rest

/-- The canonical words of a length vector, in the symbol order of
`canonOrder`. -/
def canonWords {n : Nat} (len : Fin n → Nat) : List (List Bool) :=
  canonWordsAux len 0 0 (canonOrder len)

/-- **Canonical reconstruction**: given a length vector per symbol, returns the
tree of the canonical code, or `none` as soon as an insertion collides or a
hole remains — that is, as soon as the vector is not complete. -/
def buildCanon {n : Nat} (len : Fin n → Nat) : Option (LTree n) :=
  let step (acc : Option (PTree n)) (p : Fin n × List Bool) : Option (PTree n) :=
    acc.bind fun t => pinsert t p.2 p.1
  (((canonOrder len).zip (canonWords len)).foldl step (some (.tip none))).bind
    toLTree

/-- The tree the reconstruction must return for `demoLengths`: the canonical
code of the notebook, written by hand so that the proof has a target. `true`
descends to the left, so the notebook's word "0" (false) is the **right**
child. -/
def demoCanonTree : LTree 4 :=
  .node (.node (.node (.leaf 3) (.leaf 2)) (.leaf 1)) (.leaf 0)

/-- **The reconstruction recovers the notebook's code**: for lengths 1-2-3-3,
symbol 0 gets "0", 1 gets "10", 2 gets "110" and 3 gets "111". Proved by full
evaluation of the counter and the insertions — it is the whole tree that is
pinned, not only its lengths. -/
theorem buildCanon_demo : buildCanon demoLengths = some demoCanonTree := by
  decide

/-- **Minimal positive control**: two symbols of length 1 (Kraft = 1) rebuild
into a node with two leaves, in the order of the counter. -/
theorem buildCanon_two : buildCanon ![1, 1] = some (.node (.leaf 1) (.leaf 0)) := by
  decide

/-- **The singleton falls back on the Huffman convention**: length 0, empty
word, root leaf — the same one as `costL_singleton_empty_word`. The notebook's
native codec, on the other hand, returns a one-bit word: it has no total tree
(`one_bit_singleton_has_no_total_tree`), so the reconstruction can only return
the root leaf or refuse. -/
theorem buildCanon_singleton : buildCanon ![0] = some (.leaf 0) := by
  decide

/-- **Refusal by collision**: three symbols of length 1 claim 3/2 > 1; the
third word lands on an already placed word and the reconstruction returns
`none`. -/
theorem buildCanon_refuses_nonKraft : buildCanon ![1, 1, 1] = none := by
  decide

/-- **Refusal by hole**: `![1, 2, 3]` has Kraft 7/8 — no word collides, but a
leaf is missing, and `LTree` cannot represent it. The reconstruction refuses
rather than fabricating a label. -/
theorem buildCanon_refuses_incomplete : buildCanon ![1, 2, 3] = none := by
  decide

/-- Consistent with `no_LTree_zero`: on the empty alphabet there is nothing to
reconstruct and the reconstruction refuses. -/
theorem buildCanon_zero_alphabet :
    buildCanon (fun _ : Fin 0 => 0) = none := by
  decide

/-- **Lengths are preserved**: read back from the reconstructed tree, the
lengths are those of the vector, symbol by symbol. The proof covers the
concrete instance — the general case "every complete vector" is not claimed
here. -/
theorem demoCanon_lengths :
    ((pairs demoCanonTree).map fun p => (p.2, p.1.length))
      = [(3, 3), (2, 3), (1, 2), (0, 1)] := by
  decide

/-- **Round-trip after reconstruction**: the message encoded by the
reconstructed tree reads back, with the milestone-1 engine (`decodeL_encode`)
and not by evaluation; the message covers all four leaves. -/
theorem demoCanon_roundtrip :
    decodeL demoCanonTree [true, true, true, true, true, false, true, false, false]
      = some [3, 2, 1, 0] :=
  decodeL_encode (by intro h; exact CodeTree.noConfusion h) [3, 2, 1, 0]
    [true, true, true, true, true, false, true, false, false] (by rfl)

/-! ### Reconstruction anchors -/

/- The words of the canonical counter for lengths 1-2-3-3: this is exactly the
table of notebook 02 (`code_canonique`), written in bits. -/
#eval canonWords demoLengths

/- The reconstructed tree, then its words read back by the milestone-1 walk. -/
#eval buildCanon demoLengths
#eval wordsOf demoCanonTree

/- The three refusals, at run time: collision, hole, empty alphabet. -/
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
