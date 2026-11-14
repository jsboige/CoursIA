# Compression — représenter une information à moindre coût

[↑ Parcours de notebooks](../README.md) · [Complexity : coût du calcul](../Complexity/README.md)

Comment transmettre un message avec moins de bits tout en permettant sa reconstruction ? La série part des codes préfixes, où les symboles fréquents reçoivent les mots les plus courts, puis exploite les répétitions, le codage entropique et les compromis des codecs réels. Elle aborde ensuite la compression avec pertes contrôlées des modèles appris et le principe de longueur de description minimale : il faut payer le modèle aussi bien que les données qu'il décrit.

Le point d'entrée est accessible avec les bases de Python et les probabilités discrètes. L'entropie et les codes préfixes sont introduits dans le carnet 01 ; le parcours apporte progressivement les outils nécessaires aux suivants. Le carnet 05 demande en plus les bases des réseaux de neurones et de PyTorch. Le compagnon Lean s'adresse aux lecteurs souhaitant étudier les preuves formelles.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal et ses approfondissements.

- **Vous découvrez** : suivez les numéros nus, du code préfixe au coût total d'une description. Le palier 05 ouvre une application aux modèles appris ; 06 se lit aussi directement après 01–02.
- **Vous creusez un palier** : 01b développe la preuve en Lean ; 04b compare les codecs disponibles selon leur taux et leur vitesse ; 07 confie à un modèle local le triage des segments d'un répertoire.
- **Vous cherchez des prolongements** : « Pour aller plus loin » relie les expériences aux garanties formelles, à la complexité du calcul et à l'apprentissage par compression.

Au fil du parcours, vous apprendrez à construire et décoder un code, à justifier ses bornes, à vérifier un aller-retour exact, puis à comparer des représentations en comptant ce qu'elles coûtent réellement : en-tête, tables, données et modèle. Pour la compression avec pertes, la qualité prédictive entre aussi dans la comparaison.

## Parcours principal — Découverte et Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Codes préfixes : Shannon–Fano et Huffman](Compression-01-ShannonFano-Prefixe-Python.ipynb) | Construire un arbre de code, vérifier la condition de Kraft et confronter sa longueur moyenne à l'entropie. | Découverte ; Python et probabilités discrètes. | [01b — preuves Lean](#autour-de-01--codes-et-preuves-recherche). |
| 02 | [Huffman canonique — Python](Compression-02-HuffmanCanonique-Python.ipynb) · [C#](Compression-02-HuffmanCanonique-CSharp.ipynb) | Reconstruire les mots de code à partir de leurs longueurs ; échanger du temps de décodage contre une table en mémoire. | Découverte ; après 01. | Coût de l'en-tête, de la table et du décodage dans le carnet. |
| 03 | [LZ77](Compression-03-LZ77-Python.ipynb) | Remplacer une répétition par une référence dans une fenêtre glissante, gérer les copies chevauchantes et combiner références et codage entropique. | Licence ; codes préfixes et entropie. | Comparer recherche exhaustive et tableau de suffixes. |
| 04 | [ANS : codage par l'état](Compression-04-ANS-Python.ipynb) | Comprendre comment rANS et tANS accumulent des contributions fractionnaires de bits ; vérifier l'inversion des transitions. | Licence ; après 01–02, arithmétique entière. | [04b — codecs et fronts de Pareto](#autour-de-04--choisir-un-codec-recherche). |
| 05 | [Compression des modèles appris](Compression-05-MLCompression-Python.ipynb) | Quantifier les poids, les élaguer ou distiller un réseau ; mesurer taille et précision sur la même tâche. | Licence ; Python, PyTorch et apprentissage supervisé. | Distinguer poids nuls, stockage creux et taille du fichier. |
| 06 | [MDL et complexité de Kolmogorov](Compression-06-MDL-Kolmogorov-Python.ipynb) | Minimiser la somme du coût du modèle et des données ; distinguer cette description calculable de la complexité algorithmique idéale. | Licence ; après 01–02 et leur modèle statistique. | Effet de la taille du bloc et limites des compresseurs. |

### Parité des implémentations

| Notebook | Python | C# | Parité | Moteur et vérifications |
|---|---|---|---|---|
| 02 — Huffman canonique | [Notebook Python](Compression-02-HuffmanCanonique-Python.ipynb) | [Notebook C#](Compression-02-HuffmanCanonique-CSharp.ipynb) | Sémantique ; SOTA-OK, algorithme from-scratch des deux côtés | BCL .NET 9 côté C# ; même extrait binaire du Horla, arbre de Huffman, canonisation, table directe, aller-retour octet/hash. |

Les ex æquo de fréquence peuvent donner des arbres différents selon le départage ; la comparaison porte sur les fréquences, les longueurs et le coût optimal, pas sur une forme d’arbre imposée.

### Pourquoi les représentations changent — Licence

Huffman optimise un code symbole par symbole. Le carnet 02 montre que ses **longueurs** suffisent à reconstruire un code canonique : transmettre l'arbre entier devient inutile. Une table permet ensuite le décodage par accès indexé, au prix de mémoire. LZ77 change l'objet transmis : une répétition devient un couple décalage–longueur. Le code entropique s'applique alors aux éléments de cette représentation, ce qui explique qu'un codec puisse descendre sous l'entropie des octets calculée sans tenir compte de leur contexte.

ANS répond à une autre limite : un code préfixe binaire non trivial paie au moins un bit pour chaque symbole, même si l'un d'eux est presque certain. Sur la source à probabilités 99 % et 1 % du carnet 04, la sortie de tANS est d'environ 0,09 bit par symbole, contre 1 pour Huffman. L'état du codeur porte l'information accumulée ; les vérifications d'aller-retour contrôlent que ce gain préserve le message.

Le palier 05 change de contrat : le réseau comprimé doit conserver une qualité utile, sans devoir restituer exactement ses poids initiaux. Quantifier réduit leur précision ; élaguer introduit des zéros ; distiller apprend un autre réseau à partir des sorties du premier. Le palier 06 revient au coût de représentation : augmenter la précision du modèle peut raccourcir les données tout en allongeant excessivement le modèle. L'optimum porte sur leur somme.

### LZ77 en Python et C#

| Python | C# | Moteur et vérifications |
|---|---|---|
| [LZ77 Python](Compression-03-LZ77-Python.ipynb) | [LZ77 C#](Compression-03-LZ77-CSharp.ipynb) | Algorithmes pédagogiques, fenêtres et copies chevauchantes ; aller-retour octet/hash, tableau de suffixes et comparaison avec zlib ou ZLibStream. |

Le compagnon C# utilise .NET Interactive `.net-csharp`, .NET 9 et la BCL. Les limites du parse borné, les champs sérialisés et le coût du cadre y sont explicites ; les bornes d'entropie restent distinctes des flux réellement encodés.

## Approfondissements — Recherche

### Autour de 01 — codes et preuves (Recherche)

[01b — Kraft–McMillan et Huffman en Lean](Compression_lean/Compression-01b-Kraft-McMillan-Lean.ipynb) accompagne les codes préfixes et le décodage de 01–02. Il expose les définitions, les théorèmes et leurs hypothèses, jusqu'à l'optimalité de Huffman. Il suppose la lecture d'arbres binaires, des raisonnements par induction et un noyau Lean préparé avec le projet [Compression_lean](Compression_lean/README.md).

### Autour de 04 — choisir un codec (Recherche)

[04b — Codecs et front de Pareto](Compression-04b-CodecsSOTA-Pareto-Python.ipynb) compare les bibliothèques présentes sur des textes, des données structurées et des octets aléatoires. Après 03–04, on apprend à lire un front de Pareto : un codec est dominé si un autre est à la fois plus rapide et plus économe sur le banc choisi. Le front d'encodage peut différer de celui de décodage. Les niveaux d'un même codec déplacent aussi ce compromis.

Les débits dépendent de la machine, des versions et des corpus. Le carnet vérifie la restitution par empreinte et distingue les bibliothèques mesurées des outils seulement cités. Les données aléatoires servent de contrôle : changer de codec ne crée pas une régularité absente de la source.

### Autour de 05 — le triage par un modèle local (Recherche)

[07 — Triage par le LLM et opérations réelles](Compression-07-Triage-LLM-Operations-Reelles-Python.ipynb) prolonge le pli jouet du 05b jusque dans un système de compression par segments. Les opérations y sont réelles et inversables : les codecs de la bibliothèque standard d'un côté, des découpages de fichiers de l'autre — colonnes d'un CSV, clés d'un JSON, lignes, blocs. Le modèle local voit la vue de chaque segment, c'est-à-dire sa taille, son entropie et un aperçu, et choisit une opération par appel d'outil ; la boucle le rappelle tant qu'il reste des segments produits par un découpage, et lui renvoie la raison quand une opération ne s'applique pas au contenu. La décompression ne fait aucun appel : elle rejoue la recette certifiée à l'envers, et le banc vérifie le round-trip octet pour octet.

Le banc compare ce triage au traitement indifférencié d'un bloc, d'abord avec le même codec, puis avec le meilleur codec global choisi après coup — une borne favorable au traitement naïf, puisqu'elle lui offre un choix que personne ne fait sans essayer tous les codecs sur tout le contenu. Le gain vient du découpage, non d'une compression inventée par le modèle : une colonne de catégories séparée de ses montants se comprime mieux que le tableau entremêlé. La recette elle-même, c'est-à-dire les décisions sérialisées, est comptée dans le total : une recette gratuite n'existe pas.

## Installation — Découverte et pratique

Utiliser un noyau Python 3.10 ou ultérieur dans un environnement virtuel, avec NumPy et Matplotlib. Le compagnon C# du carnet 02 utilise le noyau .NET Interactive `.net-csharp` et .NET 9 ; il ne demande aucun paquet NuGet. Le carnet 05 utilise aussi PyTorch et Pandas. Le carnet 04b sonde les codecs installés : `zlib`, `bz2` et `lzma` viennent de Python ; `zstandard`, `brotli` et `lz4` sont des compléments selon les comparaisons souhaitées. Le carnet 07 suppose en plus l'endpoint OpenAI-compatible de la pile vLLM locale et le modèle `swift` ; il s'arrête explicitement s'ils sont absents. Les instructions générales sont dans les [commandes de référence](../../docs/reference/common-commands.md).

Commencer par [01](Compression-01-ShannonFano-Prefixe-Python.ipynb), puis modifier la distribution de symboles et observer l'arbre obtenu. Les expériences Python du parcours utilisent le CPU. Pour 01b, suivre la toolchain déclarée dans [Compression_lean](Compression_lean/README.md), construire le projet avec `lake build` depuis ce dossier et utiliser le noyau Lean `lean4-wsl` indiqué par le carnet.

## Pour aller plus loin — Recherche

### Formalisations Lean

Le projet [Compression_lean](Compression_lean/) outille le [compagnon 01b](Compression_lean/Compression-01b-Kraft-McMillan-Lean.ipynb). Les résultats se lisent en suivant leur dépendance conceptuelle :

- [PrefixCodes](Compression_lean/PrefixCodes.lean), [Decode](Compression_lean/Decode.lean) et [McMillan](Compression_lean/McMillan.lean) relient condition de Kraft, existence d'un code et restitution après encodage.
- [Huffman](Compression_lean/Huffman.lean) construit l'arbre ; [Optimalite](Compression_lean/Optimalite.lean) relie son coût aux charges des fusions. [Echange](Compression_lean/Echange.lean) et [Appariement](Compression_lean/Appariement.lean) expliquent pourquoi placer les poids importants plus près de la racine ne peut augmenter le coût.
- [SymbolCodec](Compression_lean/SymbolCodec.lean) relie le code étiqueté par symboles au modèle d'arbre pondéré utilisé dans la preuve d'optimalité.
- [Expansion](Compression_lean/Expansion.lean), [Feuilles](Compression_lean/Feuilles.lean) et [Soeurs](Compression_lean/Soeurs.lean) préparent la transformation des arbres. [Descente](Compression_lean/Descente.lean) et [DeuxMinima](Compression_lean/DeuxMinima.lean) amènent les deux poids minimaux dans une paire de feuilles sœurs, en conservant leurs multiplicités. [HuffmanOptimal](Compression_lean/HuffmanOptimal.lean) conclut par `huffman_optimal` : l'arbre construit minimise le coût parmi les arbres portant les mêmes feuilles.

### Mesurer la compression et comprendre ses limites

Les taux de 02–04 doivent se lire avec le périmètre annoncé : plusieurs comparaisons isolent les flux sans compter tout l'en-tête d'un format de fichier. Dans 05, annuler un poids ne réduit pas à lui seul un stockage dense ; le mode de représentation compte autant que le taux de zéros. Le résultat sur le réseau synthétique ne préjuge pas du comportement d'un grand modèle.

Dans 06, la comparaison des décimales de π et de chiffres aléatoires illustre la limite des régularités reconnues par les codecs choisis. Une courte description algorithmique peut leur échapper. La complexité de Kolmogorov est non calculable : un compresseur fournit une description possible, pas sa valeur exacte.

### Liens avec les autres parcours

[Complexity](../Complexity/README.md) étudie le coût de **calculer** ; les tables de Huffman et les recherches de références LZ77 montrent ici comment ce coût s'échange contre une représentation plus courte. Le [compression-progress d'ICT-17b](../IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress-Python.ipynb) prolonge le palier 05 en examinant l'apprentissage comme progrès de compression : la question devient celle de l'évolution du modèle, au-delà de sa seule taille finale.

## Ressources — tous niveaux

Les carnets présentent les références auprès des constructions : Shannon, Fano, Huffman et Kraft en [01](Compression-01-ShannonFano-Prefixe-Python.ipynb), Schwartz–Kallick en [02](Compression-02-HuffmanCanonique-Python.ipynb), Ziv–Lempel en [03](Compression-03-LZ77-Python.ipynb), Duda et ANS en [04](Compression-04-ANS-Python.ipynb), puis MDL et Kolmogorov en [06](Compression-06-MDL-Kolmogorov-Python.ipynb). Les ressources des codecs comparés figurent dans [04b](Compression-04b-CodecsSOTA-Pareto-Python.ipynb).

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md)


## Twins de notebooks

Le carnet [01 — codes préfixes en C#](Compression-01-ShannonFano-Prefixe-CSharp.ipynb) accompagne [sa version Python](Compression-01-ShannonFano-Prefixe-Python.ipynb). Les deux implémentent Shannon-Fano et Huffman à partir des primitives du langage ; le jumeau C# utilise uniquement la BCL, avec une génération gamma pour ses tirages Dirichlet et un SVG autonome pour le nuage. Les exercices restent ouverts dans les deux parcours.
