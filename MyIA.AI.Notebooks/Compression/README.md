# Compression — sous-série pédagogique

La compression de données **sans perte**, du premier principe (le code préfixe)
jusqu'aux codecs réels et au compromis description/données (MDL). La série se
déploie au format **Origami** : un pli à la fois, chaque pli s'ouvrant à la
livraison du précédent ([EPIC #18706](https://github.com/jsboige/CoursIA/issues/18706)).

Chaque carnet porte le suffixe de son noyau (`-Python`, `-Lean`) — le jumeau
Lean des définitions est prévu par les plis suivants.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un code préfixe optimal sur un alphabet de symboles à fréquences connues (algorithme de Huffman)
2. **Vérifier** la condition de Kraft sur un code arbitraire et reconnaître les codes qui violent la borne
3. **Comparer** les arbres Shannon-Fano et Huffman sur un même corpus pour comprendre l'origine du gain
4. **Calculer** la longueur moyenne d'un code et la confronter à la borne entropique de Shannon sur une source discrète
5. **Encoder et décoder** un message avec un code préfixe arbitraire, et détecter les codes ambigus
6. **Canoniser et décoder par table** : réduire l'en-tête d'un code Huffman à ses seules longueurs (Schwartz-Kallick), puis décoder par table indexée à $2^L$ entrées plutôt que par parcours d'arbre

## Carnets

| Carnet | Niveau | Contenu |
|---|---|---|
| [Compression-01 — Codes préfixes : de Shannon-Fano à Huffman](Compression-01-ShannonFano-Prefixe-Python.ipynb) | Découverte | codes préfixes, inégalité de Kraft, Shannon-Fano contre Huffman, l'entropie comme borne |
| [Compression-02 — Huffman canonique : des longueurs aux tables de décodage](Compression-02-HuffmanCanonique-Python.ipynb) | Découverte | forme canonique de Schwartz-Kallick (l'en-tête réduit aux longueurs), table de décodage $2^L$ et son coût mémoire, aller-retour octet-exact sur un extrait réel, débits mesurés contre chiffres cités |

Compression-02 en une phrase : le récepteur n'a jamais besoin de l'arbre ni
des mots — les longueurs suffisent, et une table de $2^L$ entrées transforme
chaque symbole décodé en une lecture indexée. Le carnet le démontre sur 128 Kio
du *Horla* (aller-retour exact, 58,2 % de l'original, longueur moyenne 4,655
bits/octet contre une entropie de 4,620) et confronte ses débits Python aux
chiffres publiés des Huffman de production (Huff0, Oodle).

## Position dans le dépôt

La série est une voisine de
[Complexity](../Complexity/README.md) : Complexity traite du coût de
*calculer* une fonction, Compression du coût de *représenter* une information.
Les deux questions se rejoignent dans le compromis temps de calcul contre
taille de sortie — les renvois croisés se posent au fil des plis.

## Jumeau formel Lean

Le lake [`Compression_lean/`](Compression_lean/) formalise le cœur théorique
des carnets, un module par pli de l'EPIC :

| Module | Contenu |
|---|---|
| [`PrefixCodes.lean`](Compression_lean/PrefixCodes.lean) | codes préfixes sur arbres binaires, inégalité de Kraft (pli 1) |
| [`Decode.lean`](Compression_lean/Decode.lean) | décodage préfixe pas à pas et round-trip (pli 2) |
| [`McMillan.lean`](Compression_lean/McMillan.lean) | réciproque de Kraft : le code canonique réalise toute bande de longueurs admissible (pli 3) |
| [`Huffman.lean`](Compression_lean/Huffman.lean) | le trie de Huffman depuis les fréquences : forêt triée, fusion des deux minima, Kraft sur les profondeurs, code canonique préfixe-libre (pli 4) |
| [`Optimalite.lean`](Compression_lean/Optimalite.lean) | le coût d'un code préfixe : deux lectures du même nombre (poids × profondeurs, poids des fusions) unies par `costAt_eq`, ancre 14 vs 16 du carnet 02 (pli 5) |
| [`Echange.lean`](Compression_lean/Echange.lean) | le lemme d'échange élémentaire : faire monter un poids fort ne augmente jamais le coût (`exchange_le`, écart exact `b - a`), descente 21 → 15 → 14 du carnet 02 (pli 5b) |
| [`Appariement.lean`](Compression_lean/Appariement.lean) | le coût comme somme pondérée `costW t = Σ wᵢ·dᵢ` (`cost_dot`) et l'échange général par inégalité de réarrangement sur deux feuilles quelconques (pli 5c) |
| [`Expansion.lean`](Compression_lean/Expansion.lean) | le pas inductif de l'optimalité : développer la feuille de masse `a + b` en ses deux constituants facture exactement la masse fusionnée (`costW_subst`), ancre 12 + 2 = 14 du carnet 02 (pli 5d) |
| [`Feuilles.lean`](Compression_lean/Feuilles.lean) | les outils positionnels du théorème d'optimalité : profondeur d'une feuille (`depthOf`), hauteur (`maxDepth`), substitution d'un poids (`swapW`) et sa facture — l'écart de poids fois la profondeur (`costW_swapW_eq`), ancre 21 − 3·(4−1) = 12 du carnet 02 (pli 5e) |
| [`Soeurs.lean`](Compression_lean/Soeurs.lean) | l'adressage positionnel (`subtreeAt`, `replaceAt`) et sa facture, l'existence d'une paire de feuilles sœurs exactement à la profondeur maximale (`sisterPath_spec`), et l'échange de deux poids en un parcours (`exchangeW`) strictement améliorant (`costW_exchangeW_lt`) — la descente 21 → 15 → 14 du carnet 02 (pli 5f) |
| [`Descente.lean`](Compression_lean/Descente.lean) | l'échange positionnel de deux feuilles (`exchPos`, par chemins exacts — jamais par poids) et sa facture, l'infrastructure des chemins (prolongement, divergence, plafond de hauteur, multi-ensemble des feuilles conservé), et le théorème `min_to_bottom` : tout poids minimal descend dans la paire de sœurs à la profondeur maximale sans augmenter le coût — ancre 21 → 19 du carnet 02 (pli 5g) |
| [`DeuxMinima.lean`](Compression_lean/DeuxMinima.lean) | le comptage positionnel (`count_two_positions` : deux positions d'un même poids forcent sa multiplicité, `exists_leafPos_ne` : la réciproque désigne une seconde occurrence divergente) et le théorème `both_mins_to_bottom` : les deux plus petits poids vivent ensemble dans la paire profonde sans augmenter le coût, multiplicités comprises — ancre 21 → 19 → 16 du carnet 02 (pli 5h) |

`lake build` (depuis `Compression_lean/`) est la preuve d'exécution du lake ;
les carnets Python restent le vecteur pédagogique.

## Environnement

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du
dépôt ([common-commands](../../docs/reference/common-commands.md)).
