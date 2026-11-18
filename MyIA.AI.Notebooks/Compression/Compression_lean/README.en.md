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
   sharing of the budget that notebook 01 sets out in § 3 (Kraft's
   inequality).
4. **`kraft_full`** — the complete tree of depth `k` carries `2 ^ k` leaves
   (`length_leafWords_full`) and **saturates the bound exactly**:
   `kraftSum (full k) = 1`. Executable anchors `#eval`: the fixed 2-bit code
   and the `(1, 2, 3, 3)` code (`a=0, b=10, c=110, d=111`) both equal
   exactly `1`.

Roadmap (later folds of #18706): ~~McMillan's theorem (converse)~~
(delivered, module `McMillan`), ~~Huffman canonical decoding trie~~
(delivered, modules `Huffman` and `Optimalite`), ~~Huffman optimality~~
(delivered, modules `Appariement`, `Echange`, `Expansion`, `Feuilles`,
`Soeurs`, `Descente`, `DeuxMinima` then `HuffmanOptimal`, closed by the
`SymbolCodec` gateway with notebook 02). The complete arc is executed by
the companion notebook's appendix.

## Module `Decode` (fold 2)

The complementary **dynamic engine** of `PrefixCodes` — what the fold 2
Python notebook ("decoding tables") does by hand:

1. **`decode1`** — one decoding step: follow the bits from the root
   (`true` = left) to the first leaf, return the consumed word and the rest
   of the stream; `none` if the stream runs out on the way.
2. **`decode1_sound` / `decode1_complete`** — the step is exact: it returns
   `some (w, rest)` if and only if the stream starts with the leaf word `w`
   followed by `rest`.
3. **`decode`** — full stream decoding (terminates via `decode1_shorter`:
   one step consumes at least one bit outside the root-leaf case; the empty
   stream decodes to the empty message).
4. **`decode_encode`** — **round-trip**: decoding the concatenation of a
   list of leaf words returns exactly that list, in order. Anchors `#eval`:
   message `a b c` of the `(1, 2, 3, 3)` code, truncated stream (`none`),
   full round-trip of `sf4` and `fixed2`.

## Module `McMillan` (fold 3)

The **converse of Kraft** — the "realisation" direction of the
Kraft–McMillan theorem, the guarantee the Python notebook
`Compression-02` relies on when it rebuilds a code from a length table:

1. **`bits`** — exact binary writing of a counter over `l` bits (MSB
   first): exact length, reading of the first `k` bits as a quotient,
   injectivity below `2 ^ l`.
2. **`mass` / `Inv`** — Kraft's constraint lifted to integers at scale
   `2 ^ L` (`Σ 2 ^ (L - ℓᵢ) ≤ 2 ^ L`), and the mass invariant of the
   construction: counter + remaining mass ≤ `2 ^ L` (`inv_fits`: the
   counter fits in its band; `inv_step`: the counter jump preserves the
   invariant).
3. **`canon`** — the **canonical code** (Schwartz–Kallick): lengths sorted
   increasingly, counter starting at `0`, and at each passage from `ℓᵢ` to
   `ℓᵢ₊₁` the jump `(c + 1) * 2 ^ (ℓᵢ₊₁ - ℓᵢ)` — stepping beyond every
   prolongation of the previous word.
4. **`canon_spec`** — the output is **prefix-free** (the core:
   `not_prefix_of_jumps` — a counter jumping beyond the band
   `[c * 2 ^ (ℓ - l), (c + 1) * 2 ^ (ℓ - l))` cannot prolong the shorter
   word) and of **exact lengths**.
5. **`mcmillan_converse`** — every band of increasingly sorted, admissible
   lengths is realised by a prefix code. Anchors `#eval`: the
   `(1, 2, 3, 3)` code yields `a=0, b=10, c=110, d=111` (Kraft saturated),
   the fixed 2-bit code fills the whole space.

## Companion notebook

`Compression-01b-Kraft-McMillan-Lean.ipynb` (kernel `lean4-wsl`) imports
the lake's **real** modules and puts them to work: `#eval` anchors of
Kraft (`sf4`, `full k`), the decoding round-trip, the `canon` / `mass`
construction, `#print axioms` of the four pillar theorems
(`mcmillan_converse`, `canon_spec` and `kraft_le_one` depend on `propext`,
`Classical.choice` and `Quot.sound`; `decode_encode` on `propext` and
`Quot.sound` only), then in appendix the complete Huffman arc: the
construction and its cost (`huffman`, `costW`, `cost_dot`), the merging law
(`subst`, `huffman_expand`), the local moves (`sisterPath`, `exchange_le`,
`both_mins_to_bottom`), the symbol gateway (`SymbolCodec`) and the
`huffman_optimal` verdict with its axioms — no `sorryAx`, no
`native_decide`. Placed inside `Compression_lean/` because the kernel
detects the ancestor `lakefile.lean`: its directory is its environment.
Run from the lake root (`papermill -k lean4-wsl`).

## Build

```bash
lake build   # every module of the lake: PrefixCodes FR + EN, Decode, McMillan, the Huffman arc (Huffman ... HuffmanOptimal) and SymbolCodec, 0 sorry
```

## i18n (convention #4980, pattern A)

`PrefixCodes.lean` (namespace `CompressionLean`, FR docstrings) and
`PrefixCodes_en.lean` (namespace `CompressionLean_en`, EN docstrings) are
self-contained mirrors: same statements and proofs, only the prose differs.
The gateway follows the same twin pattern: `SymbolCodec.lean` (FR) and
`SymbolCodec_en.lean` (EN, self-contained mirror). The other modules of the
Huffman arc remain FR-only to date.
Check: `python scripts/lean/check_i18n_siblings.py --all`.
