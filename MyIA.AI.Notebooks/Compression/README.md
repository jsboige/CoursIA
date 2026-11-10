# Compression — sous-série pédagogique

La compression de données **sans perte**, du premier principe (le code préfixe)
jusqu'aux codecs réels et au compromis description/données (MDL). La série se
déploie au format **Origami** : un pli à la fois, chaque pli s'ouvrant à la
livraison du précédent ([EPIC #18706](https://github.com/jsboige/CoursIA/issues/18706)).
Le pli 7 change d'objet : la compression des **modèles** entraînés
(quantification, élagage, distillation), qui est, elle, une compression avec
pertes contrôlées.

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
7. **Parser et référencer** : remplacer la répétition par un couple (décalage, longueur) dans une fenêtre glissante (LZ77), séparer le parse en flux (littéraux, longueurs, décalages) et mesurer la double couche LZ + entropie
8. **Coder des bits fractionnaires** : briser le plafond du bit entier de Huffman avec ANS — l'état rANS accumule $-\log_2 p$ bits par symbole, tANS fige la machine dans des tables de $2^L$ états, et le cas très déséquilibré (99 %/1 %) montre un facteur onze sur la longueur moyenne
9. **Quantifier, élaguer et distiller** un modèle entraîné — et lire le prix en exactitude : comparer FP32/FP16/INT8, choisir entre per-tensor et per-channel, mesurer la falaise du pruning one-shot, puis montrer ce que la distillation transfère que l'étiquette seule ne dit pas
10. **Arbitrer** entre le coût du modèle et celui des données (principe MDL) : chiffrer la description d'un modèle quantifié, localiser la précision optimale `b*` et vérifier qu'elle croît avec la taille du bloc ; reconnaître ensuite que la complexité de Kolmogorov n'est pas calculable et que trois compresseurs n'en fournissent que des bornes supérieures

## Carnets

| Carnet | Niveau | Contenu |
|---|---|---|
| [Compression-01 — Codes préfixes : de Shannon-Fano à Huffman](Compression-01-ShannonFano-Prefixe-Python.ipynb) | Découverte | codes préfixes, inégalité de Kraft, Shannon-Fano contre Huffman, l'entropie comme borne |
| [Compression-02 — Huffman canonique : des longueurs aux tables de décodage](Compression-02-HuffmanCanonique-Python.ipynb) | Découverte | forme canonique de Schwartz-Kallick (l'en-tête réduit aux longueurs), table de décodage $2^L$ et son coût mémoire, aller-retour octet-exact sur un extrait réel, débits mesurés contre chiffres cités |
| [Compression-03 — LZ77 : compresser par références dans une fenêtre glissante](Compression-03-LZ77-Python.ipynb) | Licence | parse LZ77 en littéraux et couples (décalage, longueur), copie chevauchante, structure `LZData` à trois flux sur le modèle zstd, coût d'un triplet et double couche LZ + entropie, débit de la recherche naïve contre un tableau de suffixes |
| [Compression-04 — ANS : coder des bits fractionnaires par l'état (rANS, tANS)](Compression-04-ANS-Python.ipynb) | Licence | plafond Huffman sur source déséquilibrée, pas rANS et état porteur d'entropie, streaming par blocs avec retour prouvé à M, tables tANS par pavage dyadique et appariement tourné, validation exhaustive des transitions, banc de taux et débits contre Huffman et zlib |
| [Compression-04b — Codecs SOTA : le front de Pareto vitesse × taux](Compression-04b-CodecsSOTA-Pareto-Python.ipynb) | Recherche | sondage honnête des codecs réellement présents (`zlib`, `bz2`, `lzma`, `zstd`, `brotli`, `lz4`) et des absents (`openzl`, codecs de la distribution 7-Zip), banc à deux axes sur trois corpus avec aller-retour octet-exact par empreinte, front de Pareto **calculé** et lu séparément sur la vitesse d'encodage et de décodage, quatre régimes croisant taux et vitesse, balayage des niveaux zstd montrant qu'un même codec traverse plusieurs régimes, témoin négatif sur l'incompressible |
| [Compression-05 — Compression des modèles : quantifier, élaguer, distiller](Compression-05-MLCompression-Python.ipynb) | Licence | vue d'ensemble des trois familles appliquées à un réseau entraîné — quantification FP16/INT8, élagage par magnitude, distillation maître-élève — sur un terrain synthétique CPU ; cellules adaptées des `3.9-*` de la série ML, mesures avant/après sur une même référence et pont vers le compression-progress (ICT-17b) |
| [Compression-06 — MDL : décrire le modèle autant que les données](Compression-06-MDL-Kolmogorov-Python.ipynb) | Licence | principe MDL en deux parties, précision optimale `b*` d'un modèle quantifié sur 16 Kio du *Horla*, coût du modèle amorti par `n` mesuré contre la loi en `0,5 log2(n)`, complexité de Kolmogorov non calculable et trois bornes supérieures mesurées |

Compression-02 en une phrase : le récepteur n'a jamais besoin de l'arbre ni
des mots — les longueurs suffisent, et une table de $2^L$ entrées transforme
chaque symbole décodé en une lecture indexée. Le carnet le démontre sur 128 Kio
du *Horla* (aller-retour exact, 58,2 % de l'original, longueur moyenne 4,655
bits/octet contre une entropie de 4,620) et confronte ses débits Python aux
chiffres publiés des Huffman de production (Huff0, Oodle).

Compression-03 en une phrase : la deuxième occurrence d'une suite d'octets ne se
code pas, elle se référence par un couple (décalage, longueur) dans la fenêtre des
octets déjà produits — et la copie qui se chevauche elle-même déroule les runs
gratuitement. Le carnet parse 16 Kio du *Horla* en trois flux séparés (le modèle
de zstd), chiffre la double couche LZ + entropie contre Huffman seul et contre
zlib, puis mesure le débit de la recherche exhaustive face à un tableau de
suffixes.

Compression-04 en une phrase : là où chaque mot de code de Huffman paie un bit
entier, ANS accumule les bits fractionnaires dans un seul état — rANS fait de
chaque symbole une multiplication réversible d'un entier (le round-trip se
prouve par le retour exact à l'état initial, par blocs pour borner la mémoire),
tANS fige la machine dans des tables de $2^L$ états construites par pavage
dyadique. Le carnet valide chaque codeur par round-trips aléatoires et une
énumération exhaustive des transitions, puis mesure : sur 16 Kio du *Horla*
tous les codeurs entropiques collent à l'entropie (écart de 2 à 5 centièmes),
mais sur une source à 99 %/1 % tANS rend 0,09 bit/symbole là où Huffman rend
1,0000.

Compression-04b en une phrase : un codec n'est pas un score, c'est un point
dans le plan taux × vitesse, et le vainqueur change selon l'axe de vitesse
qu'on regarde. Le carnet sonde les codecs réellement installés, mesure neuf
d'entre eux sur trois corpus avec un aller-retour octet-exact vérifié par
empreinte, puis **calcule** le front de Pareto : sur 128 Kio du *Horla*, `bz2
-9` reste le meilleur taux (2,5970 bits/octet, 2,02 bits sous l'entropie
d'ordre 0) et bat sur ce corpus `brotli -11`, `lzma -6` et `zstd -19` en taux
comme en vitesse d'encodage ; le front de décodage, lui, change de membres.
Il établit aussi ce que le carnet 04 ne pouvait pas refermer : les codecs de
production descendent **sous** l'entropie des octets parce qu'ils ne
transmettent pas ces octets — et il montre qu'une grille de régimes se décide
par son seuil, raison pour laquelle le front est calculé et non désigné.

Compression-05 en une phrase : un réseau entraîné est un fichier de poids à
4 octets qui se comprime de trois façons complémentaires — **quantifier**
(÷2 en FP16, ÷4 en INT8, sans perte mesurable sur le terrain du carnet),
**élaguer** (zéroer les petits poids, que le codage monétise : la sparsité est
de la redondance), **distiller** (un petit réseau imite les sorties adoucies
d'un grand). Le carnet mesure chaque famille avant/après sur une même
référence CPU, puis relie la boucle au compression-progress de Schmidhuber :
apprendre est déjà compresser.

Compression-06 en une phrase : la description d'une donnée se paie en deux fois —
le modèle, puis les données sous ce modèle — et le bon modèle minimise la somme,
pas l'un des deux termes. Le carnet mesure la précision optimale sur 16 Kio du
*Horla* (`b* = 11` bits, 9 483,1 octets pour 16 384), montre qu'elle croît avec la
taille du bloc sans suivre exactement la pente en `0,5 log2(n)`, puis établit le
résultat le plus inconfortable de la série : 12 000 décimales de pi et 12 000
chiffres tirés au hasard se compressent à 18 octets près, alors que la première a
une description de vingt lignes. Un compresseur mesure l'entropie de l'alphabet et
les répétitions locales, pas la complexité algorithmique.

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
| [`HuffmanOptimal.lean`](Compression_lean/HuffmanOptimal.lean) | le théorème d'optimalité complet : contraction de la paire de sœurs en une feuille mariée (`replaceAtW`), lecture en facture de la construction (`costW_build_charge` : coût interne + charge des fusions), unicité du tri (`sortedLe_perm_eq`), commutation `huffman_expand` (marier d'abord coûte le trie réduit plus la masse), et le théorème capital `huffman_optimal` : le trie de Huffman coûte moins que tout arbre des mêmes feuilles — l'ancre 14 du carnet 02 devient un minimum prouvé (pli 5i) |

`lake build` (depuis `Compression_lean/`) est la preuve d'exécution du lake ;
les carnets Python restent le vecteur pédagogique.

## Environnement

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du
dépôt ([common-commands](../../docs/reference/common-commands.md)).
