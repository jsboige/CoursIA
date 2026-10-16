import Lake
open Lake DSL

/-!
# Lake dédié `Compression_lean` — jumeau formel de la série Compression (EPIC #18706)

Formalisation Lean du cœur théorique des codes de compression : l'inégalité de
Kraft et le théorème de McMillan pour les codes préfixes, ancres formelles des
carnets Python `Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb`
(pli 1, Shannon–Fano) et `Compression-02-HuffmanCanonique` (pli 2, Huffman
canonique). Décision D4 de l'EPIC #18706 : lake dédié, mathlib seule.

Convention des lakes frères (`learning_theory_lean`, `search_lean`) : le lake
est le livrable formel, `lake build` est la preuve d'exécution ; les carnets
Python de la série restent le vecteur pédagogique.
-/

package «compression_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

/-- Modules racine du lake : `PrefixCodes` — codes préfixes et inégalité de
Kraft (pli 1/2 de #18706) : arbres de codes binaires, mots des feuilles, code
préfixe, somme de Kraft ≤ 1, arbre complet de profondeur k (2^k feuilles,
Kraft = 1 exactement), ancres numériques des carnets Python frères (sibling
EN : `PrefixCodes_en`) ; `Decode` — décodage préfixe et table de décodage
(pli 2 de #18706) : un pas de décodage le long de l'arbre, correction et
complétude du pas, décodage complet du flux, théorème de round-trip ;
`McMillan` — réciproque de Kraft, sens réalisation (pli 3 de #18706) :
code canonique construit depuis une bande de longueurs admissible,
préfixe-liberté et longueurs exactes via l'invariant de masse à l'échelle
`2 ^ L` ; `Huffman` — le trie canonique depuis les fréquences (pli 4 de
#18706) : arbres pondérés, construction de Huffman par fusion des deux
minima d'une forêt triée, profondeurs, Kraft à l'échelle entière, et le
théorème capital — le code canonique des profondeurs du trie existe et est
préfixe-libre (invocation du pli 3), le code de l'arbre l'est aussi
(invocation du pli 1) ; `Optimalite` — le coût d'un code préfixe (pli 5 de
#18706) : poids des feuilles en parcours, deux lectures du coût (externe à
profondeur de départ `k`, interne par nœuds fusionnés) unies par le théorème
`costAt_eq`, ancre du carnet 02 — le trie de Huffman `[1,1,2,4]` coûte 14
contre 16 au code fixe ; `Echange` — le lemme d'échange (pli 5b de
#18706) : symétrie du coût entre branches d'un nœud (`cost_node_comm`), forme
élémentaire du lemme d'échange (`exchange_le`) — faire monter un poids fort
contre un poids faible ne augmente jamais le coût, écart exact `b - a` — et la
descente du carnet 02 : 21 -> 15 -> 14 par deux échanges jusqu'au trie de
Huffman. -/
@[default_target]
lean_lib «PrefixCodes» where
  -- Module plat (fichiers racine, aucune arborescence `PrefixCodes/`) :
  -- pas de `.submodules`, cf la note `MathUniverse` de `learning_theory_lean`.
  globs := #[`PrefixCodes, `PrefixCodes_en, `Decode, `McMillan, `Huffman, `Optimalite, `Echange]
