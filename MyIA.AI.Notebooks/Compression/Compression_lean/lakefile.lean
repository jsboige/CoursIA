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
Huffman ; `Appariement` — le coût comme somme pondérée et l'échange général
(pli 5c de #18706) : produit pondéré des parcours (`dotp`), théorème central
`cost_dot` — la charge par fusions est la facture feuille à feuille `Σ wᵢ·dᵢ` —
et l'inégalité de réarrangement sur deux feuilles quelconques (`rearrange_two`),
d'écart exact le produit des écarts ; `Expansion` — le pas inductif de
l'optimalité (pli 5d de #18706) : développer la feuille de masse `a + b` en
ses deux constituants (`subst`) facture exactement la masse fusionnée
(`costW_subst` : `costW (subst t a b) = costW t + (a + b)`), sans bouger le
poids ni le reste de l'arbre — l'ingrédient montant de l'induction sur le
nombre de symboles ; `Feuilles` — profondeurs et substitution d'un poids
(pli 5e de #18706) : profondeur de la première feuille d'un poids donné
(`depthOf`), hauteur (`maxDepth`), remplacement du poids d'une feuille
(`swapW`) avec ses invariants (poids, multi-ensemble des feuilles) et sa
facture — l'écart de poids fois la profondeur de la cible
(`costW_swapW_eq`), dont le corollaire monotone alléger ne coûte jamais
plus ; `Soeurs` — paires profondes et échange de deux feuilles (pli 5f de
#18706) : adressage positionnel (`subtreeAt`, `replaceAt`) et sa facture
(`costW_replaceAt_eq` — l'écart fois la profondeur du chemin), existence
d'une paire de feuilles sœurs exactement à la profondeur maximale
(`sisterPath_spec`), et l'échange de deux poids en un parcours
(`exchangeW`, facture `costW_exchangeW_eq`, corollaire strict
`costW_exchangeW_lt` — le réarrangement du pli 5c lu sur l'arbre), ancres
de la descente 21 -> 15 -> 14 du carnet 02 ; `Descente` — amener un minimum
dans la paire profonde (pli 5g de #18706) : l'échange positionnel de deux
feuilles (`exchPos`, deux `replaceAt` aux chemins exacts, jamais par poids)
et sa facture (`costW_exchPos_eq` — chaque position paie l'écart à SA
profondeur, corollaire monotone `costW_exchPos_le` — produit des écarts),
l'infrastructure positionnelle (prolongement des chemins `subtreeAt_congr`,
remplacement qui ne touche aucune position divergente, multi-ensemble des
feuilles conservé, tout chemin plafonné par la hauteur), et le théorème
`min_to_bottom` : tout poids minimal peut être amené dans la paire de sœurs
à la profondeur maximale sans augmenter le coût — la première moitié du lemme
des sœurs du théorème d'optimalité, ancre 21 -> 19 du carnet 02 ; `DeuxMinima`
— les deux minima dans la paire profonde (pli 5h de #18706) : le comptage
positionnel (`count_two_positions` — deux positions distinctes d'un même
poids forcent sa multiplicité, et réciproquement `exists_leafPos_ne` désigne
une seconde occurrence divergente), et le théorème `both_mins_to_bottom` :
les DEUX plus petits poids vivent ensemble dans la paire de sœurs à la
profondeur maximale, sans augmenter le coût — la seconde moitié du lemme des
sœurs, ancre 21 -> 19 -> 16 du carnet 02 (le trie compte deux 1) ;
`HuffmanOptimal` — le théorème d'optimalité complet (pli 5i de #18706) :
la contraction positionnelle (`replaceAtW` : refermer la paire de sœurs en
une feuille de masse mariée rembourse exactement sa masse), la lecture en
facture de la construction (`costW_build_charge` — le coût d'un `build` est
la somme des coûts internes plus la charge des fusions, laquelle ne lit que
la bande des poids), l'unicité du tri (`sortedLe_perm_eq`), la commutation
`huffman_expand` (marier d'abord coûte le trie réduit plus la masse), et le
théorème capital `huffman_optimal` : le trie de Huffman coûte moins que tout
arbre des mêmes feuilles — ancre 14 du carnet 02, désormais un minimum
prouvé. -/
@[default_target]
lean_lib «PrefixCodes» where
  -- Module plat (fichiers racine, aucune arborescence `PrefixCodes/`) :
  -- pas de `.submodules`, cf la note `MathUniverse` de `learning_theory_lean`.
  globs := #[`PrefixCodes, `PrefixCodes_en, `Decode, `McMillan, `Huffman, `Optimalite, `Echange, `Appariement, `Expansion, `Feuilles, `Soeurs, `Descente, `DeuxMinima, `HuffmanOptimal]
