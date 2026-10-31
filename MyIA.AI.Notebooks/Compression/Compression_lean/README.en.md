# compression_lean — Prefix codes and Kraft's inequality, Lean 4

Dedicated Lean 4 (Mathlib) lake of the **Compression** series — formal twin
of the Python notebooks `Compression-01-ShannonFano-Prefixe-Python.ipynb`
(fold 1, Shannon–Fano) and `Compression-02-HuffmanCanonique` (fold 2,
canonical Huffman). Decision **D4** of EPIC
[#18706](https://github.com/jsboige/CoursIA/issues/18706): dedicated lake
`Compression_lean/`, mathlib only.

## Module `PrefixCodes` (fold 1/2)

1. **Code trees** (`CodeTree`, `leafWords`) — a binary code is viewed as a
   finite tree: each leaf is a codeword, each edge a bit. This is the same
   structure as the recursive Shannon–Fano split of the Python notebook.
2. **`leafWords_prefixFree`** — the leaf words of a tree always form a
   **prefix code**: greedy decoding is never ambiguous. Structural proof by
   induction, leaves of different subtrees diverging at the first bit.
3. **`kraft_le_one`** — **Kraft's inequality** over exact rationals:
   `kraftSum t ≤ 1`. A node divides every weight by `2` (`kraftSum_node`),
   so every level of the tree shares the same unit budget — the binary
   "cake-sharing" of notebook 01.
4. **`kraft_full`** — the complete tree of depth `k` carries `2 ^ k` leaves
   (`length_leafWords_full`) and **saturates the bound exactly**:
   `kraftSum (full k) = 1`. Executable anchors `#eval`: the fixed 2-bit code
   and the `(1, 2, 3, 3)` code (`a=0, b=10, c=110, d=111`) both equal
   exactly `1`.

Roadmap (later folds of #18706): McMillan's theorem (converse), decoding
trie, Huffman optimality.

## Build

```bash
lake build   # both modules (EN + FR), 0 sorry
```

## i18n (convention #4980, pattern A)

`PrefixCodes_en.lean` (namespace `CompressionLean_en`, EN docstrings) and
`PrefixCodes.lean` (namespace `CompressionLean`, FR docstrings) are
self-contained mirrors: same statements and proofs, only the prose differs.
Check: `python scripts/lean/check_i18n_siblings.py --all`.
