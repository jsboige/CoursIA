# compression_lean — Codes préfixes et inégalité de Kraft, Lean 4

Lake Lean 4 (Mathlib) dédié de la série **Compression** — jumeau formel des
carnets Python `Compression-01-ShannonFano-Prefixe-Python.ipynb` (pli 1,
Shannon–Fano) et `Compression-02-HuffmanCanonique` (pli 2, Huffman canonique).
Décision **D4** de l'EPIC [#18706](https://github.com/jsboige/CoursIA/issues/18706) :
lake dédié `Compression_lean/`, mathlib seule.

## Module `PrefixCodes` (pli 1/2)

1. **Arbres de codes** (`CodeTree`, `leafWords`) — un code binaire est vu
   comme un arbre fini : chaque feuille est un mot du code, chaque arête un
   bit. C'est la même structure que la coupe récursive de Shannon–Fano du
   carnet Python.
2. **`leafWords_prefixFree`** — les mots des feuilles d'un arbre forment
   toujours un **code préfixe** : le décodage glouton n'est jamais ambigu.
   Preuve structurelle par induction, les feuilles de sous-arbres différents
   divergeant au premier bit.
3. **`kraft_le_one`** — **inégalité de Kraft** sur les rationnels exacts :
   `kraftSum t ≤ 1`. Un nœud divise chaque poids par `2`
   (`kraftSum_node`), donc chaque étage de l'arbre partage le même budget
   unitaire — le « partage du gâteau » binaire du carnet 01.
4. **`kraft_full`** — l'arbre complet de profondeur `k` porte `2 ^ k`
   feuilles (`length_leafWords_full`) et **sature exactement** la borne :
   `kraftSum (full k) = 1`. Ancres exécutables `#eval` : le code fixe 2 bits
   et le code `(1, 2, 3, 3)` (`a=0, b=10, c=110, d=111`) valent tous deux
   exactement `1`.

Roadmap (plis suivants de #18706) : théorème de McMillan (réciproque), trie
de décodage, optimalité de Huffman.

## Build

```bash
lake build   # les deux modules (FR + EN), 0 sorry
```

## i18n (convention #4980, pattern A)

`PrefixCodes.lean` (namespace `CompressionLean`, docstrings FR) et
`PrefixCodes_en.lean` (namespace `CompressionLean_en`, docstrings EN) sont
des miroirs auto-contenus : mêmes énoncés et preuves, seule la prose diffère.
Vérification : `python scripts/lean/check_i18n_siblings.py --all`.
