# Séquences — comparer deux séquences sans les énumérer, et savoir si l'on a le droit de le faire

[↑ Bio & Médecine](../README.md)

Comment dire que deux séquences se correspondent ? La réponse tient dans un choix : parmi toutes les façons de les mettre colonne par colonne, prendre celle qui donne le meilleur score. Ce pli commence par ce choix, et par l'algorithme qui le calcule sans parcourir les alignements un à un.

Le premier carnet écrit à la main l'alignement **global** — deux séquences comparées d'un bout à l'autre — et l'alignement **local** — la meilleure paire de sous-chaînes — avec des brèches dont le coût dépend de leur longueur. Il ne se contente pas de faire tourner les récurrences : il les confronte à deux voies qui ne partagent pas leur code. L'énumération de tous les alignements donne la définition de l'optimum, sur des séquences courtes ; la bibliothèque Biopython donne le juge, sur quatre protéines publiques. Trois contre-témoins montrent que ces juges savent échouer.

Le pli s'étendra à la recherche de motif : un motif planté dans un fond aléatoire, une matrice de poids positionnelle comme modèle, l'inférence du motif par `Probas/Infer/`. C'est la suite naturelle de l'alignement local — chercher un motif, c'est aligner un motif contre une séquence — et le sujet que les promotions précédentes ont le plus travaillé, comme le relève l'Epic de la série.

Les carnets s'adressent à un étudiant de licence qui connaît Python, les probabilités élémentaires et la programmation dynamique dans son principe. Aucune connaissance préalable de la biologie moléculaire n'est supposée : la matrice de substitution est construite depuis un modèle de mutation déclaré avant d'être utilisée, et les quatre protéines réelles ne servent qu'à la fin.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par l'alignement global et local du premier carnet. Vous verrez pourquoi énumérer tous les alignements est hors de portée, comment une récurrence à trois états rend le même maximum, et ce qu'une matrice de scores représente vraiment — un logarithme de rapport de probabilités, pas une table de nombres choisie au hasard.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque mesure établit, ce que chaque contrôle ne peut pas voir, et ce que le carnet laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme la feuille suivante — la recherche de motif — et les questions qu'elle ouvre, dont la statistique d'un score local, que ce carnet n'aborde pas.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Séquences-01 — Alignement par programmation dynamique](Sequences-01-Alignement-Programmation-Dynamique-Python.ipynb) | Les deux récurrences à brèches affines, écrites à partir de zéro, et leur contrôle par énumération : `900` paires de séquences à deux lettres, `127 180` alignements énumérés, écart maximal `0.0`, aucun chemin invalide ; le même accord en local sur `196` paires. La construction d'une matrice de substitution depuis un modèle de mutation déclaré : le score moyen d'une paire vraie vaut son information mutuelle à `0,07 %` près à faible distance, et la matrice reconstruite par comptage converge vers la matrice calculée. La simulation à vérité connue, sur cinq jeux par distance : identité mesurée conforme à `1-τ` à moins de deux écarts-types, et récupération des sites homologues qui décroît de `0,996` à `0,592`. Le contrôle par `Bio.Align.PairwiseAligner` : conventions de brèches mesurées, scores identiques sur les deux insulines (`437`) et les deux globines (`288`). Trois contre-témoins : glouton sous l'optimum sur `97` paires sur `100`, récurrence fautive relevée deux fois, contrôle de vérité qui échoue à grande distance. | Licence : Python, probabilités élémentaires, programmation dynamique. Outils : numpy, matplotlib, biopython. | Les trois exercices, puis la feuille de recherche de motif. |

La feuille suivante — la recherche de motif par matrice de poids positionnelle — viendra s'ajouter ici.

## Approfondissements — Licence

### Autour de 01 : deux contrôles, deux natures

Le carnet ne répète pas deux fois le même contrôle, et il dit ce que chacun ne peut pas voir.

**Une définition qu'on énumère.** Le score optimal est par définition le maximum des scores de tous les alignements. Sur un alphabet de deux lettres, toutes les séquences de un à quatre caractères se listent — `30` séquences, `900` paires — et tous les chemins s'énumèrent. La récurrence et l'énumération rendent le même maximum sur les `900` paires, à l'arrondi, et le chemin rendu est toujours un alignement valide, de score égal. En local, le contrôle énumère tous les couples de sous-chaînes ; l'accord est le même sur `196` paires.

**Le contrôle se contrôle lui-même.** Un énumérateur incomplet passerait pour un juge parfait, puisqu'il trouverait un maximum plus petit que la récurrence et que la récurrence paraîtrait alors trop haute. Le carnet compare donc le nombre de chemins produits à la formule fermée du nombre de Delannoy, sur quatre grilles : `3`, `5`, `25` et `321`. L'énumérateur est complet.

**Ce que l'énumération ne voit pas.** Elle partage avec la récurrence la convention des brèches affines : si les deux se trompaient du même prix, l'accord ne dirait rien. C'est pourquoi le carnet mesure la convention de la bibliothèque avant tout — pour une brèche de longueur $k$, `-7`, `-8`, `-9`, `-10` pour $k$ de `1` à `4`, soit $g_o + (k-1)g_e$ — puis construit la récurrence fautive, qui oublie la prolongation, et qui est relevée par l'énumération (`210` paires sur `900`) comme par la bibliothèque (`427` contre `437`).

### Autour de 01 : ce que la matrice de scores gouverne

**Elle se construit.** Sous le modèle déclaré — un site garde sa lettre avec la probabilité $1-\tau$, en prend une autre uniformément sinon, fond uniforme — la matrice n'a que deux valeurs, et le score moyen d'une paire vraie se calcule : c'est l'information mutuelle. La mesure sur `200 000` paires suit la formule à `0,07 %` près à faible distance, à `2,6 %` quand l'information tombe à `0,02` nat. Reconstruire la matrice en comptant les couples observés — la recette des matrices réelles — redonne la matrice calculée, de `1,29` nat d'écart maximal à `2 000` couples à `0,23` nat à `200 000`, les cases rares étant vides aux petits échantillons.

**Elle ne se réduit pas à un paramètre.** La meilleure distance au sens des moindres carrés vaut `0,584`, avec une erreur résiduelle de `1,52` pour un écart-type de `2,19` sur les `400` entrées de BLOSUM62 : le modèle à deux valeurs explique une partie de la structure et pas la structure. La figure du carnet montre les blocs de la matrice réelle à côté des deux teintes du modèle.

**Ce qui gouverne la récupération n'est pas l'ajustement.** Sur les données simulées à distance $0{,}3$, la matrice ajustée à cette distance récupère `0,940` des sites homologues ; une matrice ajustée à `0,5` en récupère `0,966`, et la matrice identité `0,966`. À pénalités de brèche fixes, le prix d'une substitution contre celui d'une ouverture décroît avec la distance — `2,83` à `0,05`, `1,82` à la distance des données, `0,75` à `0,8` — et c'est ce rapport qui décide. Le carnet écrit ce résultat tel qu'il le mesure, contre l'attente naïve.

### Autour de 01 : la vérité, quand on la connaît

La simulation écrit la liste des couples de sites homologues, ce qui permet de mesurer la récupération. Sur cinq jeux par distance : `0,996`, `0,940`, `0,871` et `0,592` en moyenne, avec une dispersion qui grandit jusqu'à couvrir `0,280` à `0,853` à grande distance. La simulation tient ses propres statistiques — part de sites identiques conforme à $1-\tau$ à moins de deux écarts-types binomiaux, part de sites conservés conforme à $1-p/2$ — ce qui rend le contrôle crédible.

La récupération ne mesure pourtant que les colonnes appariées : deux sites homologues remis dans la même colonne comptent, même si le voisinage est faux. Un bloc décalé d'un cran affiche une récupération partielle, et c'est ce qui arrive aux grandes distances.

### Ce que le carnet n'établit pas

Le modèle de substitution n'a **pas de chimie** : toutes les substitutions y coûtent le même prix. Les matrices utilisées en pratique distinguent les familles d'acides aminés ; le carnet mesure l'écart, il ne le comble pas.

Les séquences simulées évoluent **site par site, indépendamment**, et les moyennes portent sur cinq jeux de `150` sites par distance : c'est peu, et le carnet donne les écarts-types plutôt que de les taire. Les conclusions valent pour ce modèle, à ces longueurs, à cette probabilité d'indel.

Le score d'un alignement local **n'est pas une probabilité**. La statistique des scores — décider si un score est plus grand que ce que donnent deux séquences sans parenté — n'est pas abordée. Les heuristiques de recherche dans une base de millions de séquences non plus : la récurrence est exacte, et son coût interdit de l'appliquer telle quelle à grande échelle.

Enfin, le juge de la section 6 est une **bibliothèque** : il établit que deux implémentations indépendantes rendent le même nombre sur les cas essayés, pas que la convention des brèches affines soit le bon modèle biologique, ni que le maximum d'un score additif soit l'alignement vrai.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3`, sans GPU. Il appelle le réseau une fois, pour charger quatre séquences protéiques publiques depuis les *E-utilities* de la NCBI ; aucune séquence n'est recopiée dans le dépôt.

```bash
python -m pip install jupyterlab ipykernel numpy matplotlib biopython
jupyter lab MyIA.AI.Notebooks/BioMedecine/Sequences/Sequences-01-Alignement-Programmation-Dynamique-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** La recherche de motif : un motif planté dans un fond aléatoire, la matrice de poids positionnelle comme modèle, l'inférence avec `Probas/Infer/`, et le motif retrouvé comme contrôle. Puis les modèles de profil, qui remplacent la matrice de substitution par une matrice par position, et les heuristiques de graines, qui rendent la recherche en base possible.

**Questions ouvertes.** La statistique d'un score local, et la part d'un score qui doit à la longueur des séquences plutôt qu'à leur ressemblance. Les matrices construites sur des alignements observés, et ce qu'un modèle de mutation uniforme ne peut pas en dire. L'alignement de plusieurs séquences à la fois, qui n'est pas une répétition de l'alignement par paires. Et ce que l'alignement optimal dit de l'histoire des séquences, qui est une question de biologie et non de score.

**Ponts.** [NLP](../../NLP/05-HMM-Viterbi.ipynb) porte l'algorithme de Viterbi : la même programmation dynamique sur un chemin, dans un modèle où les états sont cachés. [Probas/Infer](../../Probas/Infer/README.md) porte l'inférence probabiliste, dont la feuille sur le motif planté a besoin. La série [Search](../../Search/README.md) traite la programmation dynamique pour elle-même, et les stratégies qui évitent de tout parcourir. Les sous-séries [Structures](../Structures/README.md) et [Dynamiques](../Dynamiques/README.md) posent, pour la molécule et pour les populations, les mêmes questions de modèle et de contrôle.

## Ressources — tous niveaux

- Modèle et mesures : matrice de substitution construite depuis un modèle de mutation déclaré, brèches affines, récurrences écrites à partir de zéro. Les séquences simulées sont engendrées par le carnet ; les quatre protéines réelles sont chargées à l'exécution depuis la NCBI, dont la page des politiques déclare ne poser aucune restriction sur l'usage ou la distribution de ses données moléculaires.
- Bibliothèque de référence : Biopython (Cock et al., 2009), utilisée pour sa matrice BLOSUM62 et son aligneur `PairwiseAligner`. La copie archivée et les conditions de diffusion sont données dans les références du carnet.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
