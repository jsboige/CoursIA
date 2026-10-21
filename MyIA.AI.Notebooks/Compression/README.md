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
7. **Parser et référencer** : remplacer la répétition par un couple (décalage, longueur) dans une fenêtre glissante (LZ77), séparer le parse en flux (littéraux, longueurs, décalages) et mesurer la double couche LZ + entropie
8. **Coder des bits fractionnaires** : briser le plafond du bit entier de Huffman avec ANS — l'état rANS accumule $-\log_2 p$ bits par symbole, tANS fige la machine dans des tables de $2^L$ états, et le cas très déséquilibré (99 %/1 %) montre un facteur onze sur la longueur moyenne

## Carnets

| Carnet | Niveau | Contenu |
|---|---|---|
| [Compression-01 — Codes préfixes : de Shannon-Fano à Huffman](Compression-01-ShannonFano-Prefixe-Python.ipynb) | Découverte | codes préfixes, inégalité de Kraft, Shannon-Fano contre Huffman, l'entropie comme borne |
| [Compression-02 — Huffman canonique : des longueurs aux tables de décodage](Compression-02-HuffmanCanonique-Python.ipynb) | Découverte | forme canonique de Schwartz-Kallick (l'en-tête réduit aux longueurs), table de décodage $2^L$ et son coût mémoire, aller-retour octet-exact sur un extrait réel, débits mesurés contre chiffres cités |
| [Compression-03 — LZ77 : compresser par références dans une fenêtre glissante](Compression-03-LZ77-Python.ipynb) | Licence | parse LZ77 en littéraux et couples (décalage, longueur), copie chevauchante, structure `LZData` à trois flux sur le modèle zstd, coût d'un triplet et double couche LZ + entropie, débit de la recherche naïve contre un tableau de suffixes |
| [Compression-04 — ANS : coder des bits fractionnaires par l'état (rANS, tANS)](Compression-04-ANS-Python.ipynb) | Licence | plafond Huffman sur source déséquilibrée, pas rANS et état porteur d'entropie, streaming par blocs avec retour prouvé à M, tables tANS par pavage dyadique et appariement tourné, validation exhaustive des transitions, banc de taux et débits contre Huffman et zlib |

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
tous les codeurs entropiques collent à l'entropie (écart de 2 à 4 centièmes),
mais sur une source à 99 %/1 % tANS rend 0,09 bit/symbole là où Huffman rend
1,0000.

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

`lake build` (depuis `Compression_lean/`) est la preuve d'exécution du lake ;
les carnets Python restent le vecteur pédagogique.

## Environnement

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du
dépôt ([common-commands](../../docs/reference/common-commands.md)).
