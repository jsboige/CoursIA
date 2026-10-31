import Mathlib

/-!
# PrefixCodes — prefix codes and Kraft's inequality (fold 1/2, EPIC #18706)

Lean formalization of the theoretical backbone of the **Compression** series:
a binary prefix code is the set of leaves of a finite binary tree, and the
**Kraft sum** of its words — `Σ w, 2 ^ (- |w|)` — never exceeds `1`
(Kraft's inequality). This is the exact constraint balanced by the
Shannon–Fano code (fold 1, `Compression-01-ShannonFano-Prefixe-Python.ipynb`)
and the canonical Huffman code (fold 2, `Compression-02-HuffmanCanonique`),
and the reason a prefix code cannot shorten all of its words at once: every
bit saved somewhere must be paid for elsewhere.

Formalization slice of the Lean twin of EPIC **#18706** (decision D4:
dedicated lake `Compression_lean`, mathlib only). Distilled content:

1. **Code trees** (`CodeTree`): a binary code is viewed as a finite tree —
   each leaf is a codeword (`leafWords`), each edge a bit (`true` = left,
   `false` = right). This is the same structure as the recursive Shannon–Fano
   split of the Python notebook: cutting the symbol list into two halves of
   ~ equal probability is building `node l r`.
2. **The leaves form a prefix code** (`leafWords_prefixFree`): two distinct
   leaf words are never prefixes of one another — prefix decoding is never
   ambiguous. Structural proof: two leaves of the same subtree inherit the
   property by induction; two leaves of different subtrees diverge at the
   first bit.
3. **Kraft's inequality** (`kraft_le_one`): `kraftSum t ≤ 1`, over exact
   rationals. Proof: an isolated leaf weighs `1`; a `node l r` divides every
   weight by `2` (one more bit per word), hence
   `kraftSum (node l r) = kraftSum l / 2 + kraftSum r / 2 ≤ 1`. Every level
   of the tree shares the same total budget — exactly the binary
   "cake-sharing" illustrated by the bar diagram of notebook 01.
4. **Complete tree** (`full k`): the balanced tree of depth `k` carries
   `2 ^ k` leaves (`length_leafWords_full`) all of length `k`, and its Kraft
   sum equals exactly `1` (`kraft_full`): the fixed-length code of `2 ^ k`
   symbols (the "naive" code of fold 1) saturates the bound. Numerical
   anchors `#eval`: the fixed 2-bit code and the length-`(1, 2, 3, 3)` code
   (letters `a=0, b=10, c=110, d=111` of the notebook) also saturate
   exactly at `1`.

Roadmap (later folds of #18706, outside this slice): McMillan's theorem
(converse — if `Σ 2 ^ (-ℓᵢ) ≤ 1` then a prefix code with these lengths
exists), the decoding trie (every finite prefix code is the set of leaves
of a tree), and Huffman optimality.

FR sibling: `PrefixCodes.lean` (namespace `CompressionLean`), same
statements and proofs, docstrings in French — i18n convention #4980
pattern A.
-/

namespace CompressionLean_en

/-- A finite binary code tree: a leaf (empty word) or a node with two
children (`true` = left child, `false` = right child). -/
inductive CodeTree where
  /-- Leaf: the end of a codeword. -/
  | leaf : CodeTree
  /-- Internal node: the two subtrees. -/
  | node : CodeTree → CodeTree → CodeTree
  deriving Repr

/-- `leafWords t`: the list of binary words of the leaves of `t`, in
left-first depth order. Each word is the edge-path from the root to the
leaf: it is the code itself. -/
def leafWords : CodeTree → List (List Bool)
  | .leaf => [[]]
  | .node l r => (leafWords l).map (true :: ·) ++ (leafWords r).map (false :: ·)

/-- `PrefixOf w v`: `w` is a prefix of `v` (there exists a suffix `t` such
that `v = w ++ t`). Self-contained relation: it avoids depending on
Mathlib's match-based definition of `List.IsPrefix`. -/
def PrefixOf (w v : List Bool) : Prop := ∃ t, v = w ++ t

/-- A "prefix code": a list of words in which no word is a prefix of another
distinct word — greedy decoding is therefore unambiguous. -/
def IsPrefixFree (C : List (List Bool)) : Prop :=
  ∀ w ∈ C, ∀ v ∈ C, PrefixOf w v → w = v

/-! ## The prefix propagation lemma -/

/-- If `b :: w` is a prefix of `c :: v` then the bits are equal and `w` is a
prefix of `v`. This is the brick for the sub-cases of theorem 1. -/
theorem prefixOf_cons {b c : Bool} {w v : List Bool}
    (h : PrefixOf (b :: w) (c :: v)) : b = c ∧ PrefixOf w v := by
  obtain ⟨t, ht⟩ := h
  injection ht with hbc hvt
  exact ⟨hbc.symm, ⟨t, hvt⟩⟩

/-! ## Theorem 1: the leaves of a tree form a prefix code -/

/-- **The leaf words of a tree always form a prefix code.** A greedy decoder
walking the tree leaf by leaf can never hit an ambiguity: two distinct leaf
words diverge somewhere and never prefix each other. -/
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
      · -- `w = true :: w'`: the word comes from the left subtree
        obtain ⟨v', hv', hv_eq⟩ | ⟨v', hv', hv_eq⟩ := hv
        · -- `v = true :: v'`: both come from the left
          subst hw_eq; subst hv_eq
          exact congrArg (fun x => true :: x) (ihl w' hw' v' hv' (prefixOf_cons hp).2)
        · -- `v = false :: v'`: divergence at the first bit
          subst hw_eq; subst hv_eq
          exact absurd (prefixOf_cons hp).1 (by decide)
      · -- `w = false :: w'`: the word comes from the right subtree
        obtain ⟨v', hv', hv_eq⟩ | ⟨v', hv', hv_eq⟩ := hv
        · -- `v = true :: v'`: divergence at the first bit
          subst hw_eq; subst hv_eq
          exact absurd (prefixOf_cons hp).1 (by decide)
        · -- `v = false :: v'`: both come from the right
          subst hw_eq; subst hv_eq
          exact congrArg (fun x => false :: x) (ihr w' hw' v' hv' (prefixOf_cons hp).2)

/-! ## The Kraft sum -/

/-- `kraftSum t`: the Kraft sum of the tree — each codeword `w` contributes
`1 / 2 ^ |w|`. Over exact rationals, hence evaluable (`#eval`). -/
def kraftSum (t : CodeTree) : ℚ :=
  ((leafWords t).map fun w => (1 : ℚ) / 2 ^ w.length).sum

/-- Key step of the Kraft recurrence: prepending one bit to every word of a
code divides its Kraft sum by exactly `2`. -/
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

/-- Kraft sum recurrence over a node: one more bit per word divides each
side by `2`. -/
theorem kraftSum_node (l r : CodeTree) :
    kraftSum (.node l r) = kraftSum l / 2 + kraftSum r / 2 := by
  simp only [kraftSum, leafWords, List.map_append, List.sum_append]
  rw [sum_map_bit_halves, sum_map_bit_halves]
  ring

/-! ## Theorem 2: Kraft's inequality -/

/-- **Kraft's inequality**: the Kraft sum of a prefix code (viewed as a
tree) never exceeds `1`. Each leaf consumes a share of the unit budget
`2 ^ (- |w|)` and the shares never overlap. This is the constraint that
Shannon–Fano (fold 1) and Huffman (fold 2) saturate at the optimum. -/
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

/-! ## Theorem 3: the complete tree saturates the bound exactly -/

/-- `full k`: the complete binary tree of depth `k` — the fixed-length code
of `2 ^ k` symbols (the "naive" code of fold 1 of the Python notebook). -/
def full : ℕ → CodeTree
  | 0 => .leaf
  | (k + 1) => .node (full k) (full k)

/-- The complete tree of depth `k` carries exactly `2 ^ k` leaves. -/
theorem length_leafWords_full (k : ℕ) : (leafWords (full k)).length = 2 ^ k := by
  induction k with
  | zero => simp [leafWords, full]
  | succ k ih =>
      simp only [full, leafWords, List.length_append, List.length_map, ih]
      rw [pow_succ]
      omega

/-- The Kraft sum of the complete tree equals **exactly** `1`: the
fixed-length code saturates Kraft's bound. -/
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

/-! ## Numerical anchors (executable) -/

/-- The fixed 2-bit code (4 symbols): `full 2`. -/
def fixed2 : CodeTree := full 2

/-- The length-`(1, 2, 3, 3)` code — letters `a=0, b=10, c=110, d=111` of
notebook 01 (Shannon–Fano on the distribution `1/2, 1/4, 1/8, 1/8`). -/
def sf4 : CodeTree := .node .leaf (.node .leaf (.node .leaf .leaf))

/-- Anchor: the fixed 2-bit code saturates Kraft exactly. -/
example : kraftSum fixed2 = 1 := kraft_full 2

/-- Anchor: the `(1, 2, 3, 3)` code saturates Kraft exactly
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

end CompressionLean_en
