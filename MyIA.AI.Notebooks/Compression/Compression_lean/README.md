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

Roadmap (plis suivants de #18706) : ~~théorème de McMillan (réciproque)~~
(livré, module `McMillan`), trie canonique de Huffman, optimalité de Huffman.

## Module `Decode` (pli 2)

La **machine dynamique** complémentaire de `PrefixCodes` — ce que le carnet
Python du pli 2 (« tables de décodage ») fait à la main :

1. **`decode1`** — un pas de décodage : suivre les bits depuis la racine
   (`true` = gauche) jusqu'à la première feuille, rendre le mot consommé et
   le reste du flux ; `none` si le flux s'épuise en chemin.
2. **`decode1_sound` / `decode1_complete`** — le pas est exact : il rend
   `some (w, rest)` si et seulement si le flux commence par le mot de
   feuille `w` suivi de `rest`.
3. **`decode`** — décodage complet du flux (termine par `decode1_shorter` :
   un pas consomme au moins un bit hors racine-feuille ; le flux vide
   décode en message vide).
4. **`decode_encode`** — **round-trip** : décoder la concaténation d'une
   liste de mots de feuilles redonne exactement cette liste, dans l'ordre.
   Ancres `#eval` : message `a b c` du code `(1, 2, 3, 3)`, flux tronqué
   (`none`), round-trip intégral de `sf4` et `fixed2`.

## Module `McMillan` (pli 3)

La **réciproque de Kraft** — le sens « réalisation » du théorème de
Kraft–McMillan, la garantie qu'utilise le carnet Python `Compression-02`
quand il reconstruit un code depuis une table de longueurs :

1. **`bits`** — écriture binaire exacte d'un compteur sur `l` bits (MSB en
   tête) : longueur exacte, lecture des `k` bits de tête comme quotient,
   injectivité sous `2 ^ l`.
2. **`mass` / `Inv`** — la contrainte de Kraft remontée en entiers à
   l'échelle `2 ^ L` (`Σ 2 ^ (L - ℓᵢ) ≤ 2 ^ L`), et l'invariant de masse de
   la construction : compteur + masse restante ≤ `2 ^ L` (`inv_fits` : le
   compteur tient dans sa bande ; `inv_step` : le saut de compteur préserve
   l'invariant).
3. **`canon`** — le **code canonique** (Schwartz-Kallick) : longueurs triées
   croissantes, compteur initial `0`, et à chaque passage de `ℓᵢ` à `ℓᵢ₊₁`
   le saut `(c + 1) * 2 ^ (ℓᵢ₊₁ - ℓᵢ)` — on passe au-delà de tous les
   prolongements du mot précédent.
4. **`canon_spec`** — la sortie est **préfixe-libre** (le cœur :
   `not_prefix_of_jumps` — un compteur qui saute au-delà de la bande
   `[c * 2 ^ (ℓ - l), (c + 1) * 2 ^ (ℓ - l))` ne peut pas prolonger le mot
   court) et de **longueurs exactes**.
5. **`mcmillan_converse`** — toute bande de longueurs triée croissante et
   admissible est réalisée par un code préfixe. Ancres `#eval` : le code
   `(1, 2, 3, 3)` redonne `a=0, b=10, c=110, d=111` (Kraft saturé), le code
   fixe 2 bits remplit tout l'espace.

## Carnet compagnon

`Compression-01b-Kraft-McMillan-Lean.ipynb` (kernel `lean4-wsl`) importe les
trois modules **réels** du lake et les fait travailler : ancres `#eval` de
Kraft (`sf4`, `full k`), round-trip de décodage, construction `canon` /
`mass`, `#print axioms` des quatre théorèmes piliers : `mcmillan_converse`,
`canon_spec` et `kraft_le_one` dépendent de `propext`, `Classical.choice` et
`Quot.sound` ; `decode_encode` de `propext` et `Quot.sound` seulement — aucun
`sorryAx`, aucun `native_decide`.
Placé dans `Compression_lean/` car le kernel détecte le `lakefile.lean`
ancêtre : son répertoire est son environnement. Exécution depuis la racine
du lake (`papermill -k lean4-wsl`).

## Build

```bash
lake build   # tous les modules du lake (PrefixCodes FR + EN, Decode, McMillan), 0 sorry
```

## i18n (convention #4980, pattern A)

`PrefixCodes.lean` (namespace `CompressionLean`, docstrings FR) et
`PrefixCodes_en.lean` (namespace `CompressionLean_en`, docstrings EN) sont
des miroirs auto-contenus : mêmes énoncés et preuves, seule la prose diffère.
Vérification : `python scripts/lean/check_i18n_siblings.py --all`.
