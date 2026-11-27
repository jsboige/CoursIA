# Séquences — comparer deux séquences sans les énumérer, puis y chercher un motif sans le connaître

[↑ Bio & Médecine](../README.md)

Comment dire que deux séquences se correspondent ? La réponse tient dans un choix : parmi toutes les façons de les mettre colonne par colonne, prendre celle qui donne le meilleur score. Ce pli commence par ce choix, et par l'algorithme qui le calcule sans parcourir les alignements un à un.

Le premier carnet écrit à la main l'alignement **global** — deux séquences comparées d'un bout à l'autre — et l'alignement **local** — la meilleure paire de sous-chaînes — avec des brèches dont le coût dépend de leur longueur. Il ne se contente pas de faire tourner les récurrences : il les confronte à deux voies qui ne partagent pas leur code. L'énumération de tous les alignements donne la définition de l'optimum, sur des séquences courtes ; la bibliothèque Biopython donne le juge, sur quatre protéines publiques. Trois contre-témoins montrent que ces juges savent échouer.

Le second carnet prend la suite naturelle de l'alignement local : chercher un motif, c'est aligner un motif contre une séquence — sans savoir où. Le motif devient une **matrice de poids positionnelle**, construite à la main depuis des sites alignés ; son seuil se lit sur la distribution de fond ; le calcul passe par `Bio.motifs` de Biopython ; deux contre-témoins vérifient que la chaîne sait échouer. Vient ensuite la question qui coûte : et si les sites n'étaient pas alignés ? L'estimation par l'algorithme de Bailey–Elkan, dans une version simplifiée, est mesurée sur plusieurs départs, et le carnet écrit le résultat tel qu'il sort — deux départs sur cinq retrouvent le site, et un contre-témoin ne teste pas ce qu'il annonçait. C'est le sujet que les promotions précédentes ont le plus travaillé.

Les carnets s'adressent à un étudiant de licence qui connaît Python, les probabilités élémentaires et la programmation dynamique dans son principe. Aucune connaissance préalable de la biologie moléculaire n'est supposée : la matrice de substitution est construite depuis un modèle de mutation déclaré avant d'être utilisée, et les quatre protéines réelles ne servent qu'à la fin du premier carnet.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par l'alignement global et local du premier carnet. Vous verrez pourquoi énumérer tous les alignements est hors de portée, comment une récurrence à trois états rend le même maximum, et ce qu'une matrice de scores représente vraiment — un logarithme de rapport de probabilités, pas une table de nombres choisie au hasard. Poursuivez par la recherche de motif du second : un motif qui n'est pas un mot, un seuil qui se mesure, et la part des sites qui échappe à ce seuil.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque mesure établit, ce que chaque contrôle ne peut pas voir, et ce que les carnets laissent ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme ce que les deux carnets laissent ouvert — l'estimation du motif par un moteur d'inférence probabiliste, les modèles de profil, les heuristiques de graines, et la statistique d'un score local, qu'aucun des deux n'aborde.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Séquences-01 — Alignement par programmation dynamique](Sequences-01-Alignement-Programmation-Dynamique-Python.ipynb) | Les deux récurrences à brèches affines, écrites à partir de zéro, et leur contrôle par énumération : `900` paires de séquences à deux lettres, `127 180` alignements énumérés, écart maximal `0.0`, aucun chemin invalide ; le même accord en local sur `196` paires. La construction d'une matrice de substitution depuis un modèle de mutation déclaré : le score moyen d'une paire vraie vaut son information mutuelle à `0,07 %` près à faible distance, et la matrice reconstruite par comptage converge vers la matrice calculée. La simulation à vérité connue, sur cinq jeux par distance : identité mesurée conforme à `1-τ` à moins de deux écarts-types, et récupération des sites homologues qui décroît de `0,996` à `0,592`. Le contrôle par `Bio.Align.PairwiseAligner` : conventions de brèches mesurées, scores identiques sur les deux insulines (`437`) et les deux globines (`288`). Trois contre-témoins : glouton sous l'optimum sur `97` paires sur `100`, récurrence fautive relevée deux fois, contrôle de vérité qui échoue à grande distance. | Licence : Python, probabilités élémentaires, programmation dynamique. Outils : numpy, matplotlib, biopython. | Les trois exercices, puis la feuille de recherche de motif. |
| 02 | [Séquences-02 — Recherche de motif par matrice de poids positionnelle](Sequences-02-Recherche-Motif-Poids-Positionnel-Python.ipynb) | La matrice de poids positionnelle construite à la main depuis des sites alignés — pseudocount, log-odds contre un fond non uniforme — puis le score de chaque fenêtre glissante, sur un motif dont le contenu informatif vaut `10,97` bits en douze positions. Le seuil lu sur la distribution du meilleur score par séquence, sur `4 000` séquences de fond à $\alpha = 10^{-2}$ : `11,66` bits, quarante dépassements attendus. La mesure sur `200` séquences à site planté et `40` leurres : rappel `0,440`, précision `0,989`, aucun faux positif sur les leurres — plus de la moitié des sites échappe au seuil, et c'est le résultat. Le contrôle par `Bio.motifs` de Biopython : facteur de conversion `1,000000`, écart matriciel `4,44e-16`, écart de scores `9,5e-07`, `48` positions sur `48`. Trois lectures du même motif sur les mêmes données : consensus littéral `0,005`, consensus IUPAC `0,255`, matrice `0,440`. Deux contre-témoins qui ramènent les détections à l'ordre de $\alpha$ : colonnes permutées `0/200`, séquences brassées `2/200`. Enfin l'estimation du motif à positions inconnues par une version simplifiée de l'algorithme de Bailey–Elkan, sur cinq départs et deux budgets d'itérations : `0/5` retrouvent le site à vingt-cinq itérations, `2/5` à cent cinquante — une graine exacte, une décalée d'une position, trois piégées, chacune sur un optimum qui n'est pas le motif — et le départ poly-G se réinterprète dès sa première itération. | Licence : Python, probabilités élémentaires, programmation dynamique, plus le principe de l'estimation par maximum de vraisemblance pour la dernière section. Outils : numpy, matplotlib, biopython. | Les trois exercices : le pseudocount, la calibration fenêtre par fenêtre, le brin complémentaire. |

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

### Autour de 02 : un contrôle par un autre chemin, et deux destructions

**Le même calcul, par un autre code.** Le second carnet ne recalcule pas Biopython pour se rassurer : il refait, avec `Bio.motifs`, le trajet qui va des comptages pseudocountés à la matrice puis aux scores. Le facteur de conversion entre les deux conventions d'unité vaut `1,000000` — les deux travaillent en base 2 —, la matrice coïncide case par case à `4,44e-16` près, les scores de fenêtre à `9,5e-07`, sur `48` positions comparées sur `48`. L'écart sur les scores ne vient pas de la matrice : additionnées à la main, les cases exposées par Biopython redonnent les scores du carnet à `3,6e-15` près, et le millionième vient de l'appel qui les additionne dans la bibliothèque, pas d'une différence de convention.

**Un contrôle qui ne sait pas échouer ne prouve rien.** Une chaîne de mesure qui ne peut que réussir ne mesure rien : si la matrice ou le seuil était inerte, les chiffres seraient les mêmes. Le carnet détruit donc **une seule** des deux sources à la fois. Permuter les colonnes de la matrice — les comptages sont conservés, seul l'appariement position-contrainte est détruit — fait tomber les détections à `0` sur `200`, avec un seuil recalculé de `11,12`. Brasser chaque séquence — le motif disparaît, la composition globale est conservée — en laisse `2` sur `200`, exactement ce que la calibration prédit, $\alpha \times 200$ — et la matrice permutée, elle, en laisse `0`, ce qu'un hasard de moyenne `2` produit une fois sur sept. Le détail qui compte : la permutation ruine la détection alors qu'elle préserve la composition du motif, ce qui indique que l'information utile est l'appariement, et non un biais de composition global. Ce dernier point n'était pas acquis d'avance.

### Autour de 02 : trois modèles pour le même motif

Le même jeu de données, la même définition du rappel, trois modèles de complexité croissante : `0,005` pour le consensus littéral — le mot le plus probable, cherché exactement —, `0,255` pour le consensus IUPAC qui remplace par `N` les positions où la base majoritaire reste sous `0,6`, et `0,440` pour la matrice complète. Aucun des trois ne déclare de faux positif sur les `40` leurres ; l'écart porte donc entièrement sur ce qui est retrouvé.

L'échelle s'explique par la structure du motif : quatre positions sur douze sont peu contraintes (base majoritaire sous `0,6`, de `0,45` à `0,55`). Le mot exact perd l'occurrence entière dès qu'une seule de ces positions diffère — ce qui arrive près de dix-neuf fois sur vingt ; le consensus IUPAC en récupère une partie en abandonnant ce qu'elles disent ; la matrice, elle, pondère chaque position par ce qu'elle apporte, et une contribution faible cesse de faire perdre un site. C'est la lecture juste de la matrice : un cumul de preuves, jamais une ressemblance à un mot.

### Autour de 02 : le seuil est une décision

Le seuil ne se lit pas dans une table : il se calcule sur un modèle de fond. Le carnet mesure la distribution du **meilleur score par séquence** sur `4 000` séquences sans site, et prend le quantile qui laisse `1 %` à droite : `11,66` bits, pour quarante dépassements attendus sur les quatre mille. Prendre le maximum par séquence, et non fenêtre par fenêtre, absorbe les tests multiples internes à une séquence — deux cents bases, près de deux cents fenêtres — et déplace la question de « cette fenêtre est-elle extrême ? » à « la meilleure fenêtre de cette séquence l'est-elle ? ».

Ce choix a un prix, mesuré : appliqué à un jeu de `200` séquences, il déclare positives $\alpha \times 200$, soit deux séquences sans site sur deux cents. Le contre-témoin sur séquences brassées rend exactement `2`. Sur les `89` séquences déclarées positives du jeu à site, `88` le sont à la position plantée, à deux bases près : la précision vaut donc `88/89`, et le rappel `0,440`. Autrement dit, le seuil ne garantit pas l'absence de faux positif ; il en borne le taux à l'échelle du jeu, et la calibration fenêtre par fenêtre — l'exercice 2 — en déplace à la fois la valeur et le sens : elle contrôle un taux par fenêtre, non un taux par séquence.

### Autour de 02 : converger n'est pas avoir fini

L'estimation à positions inconnues est un maximum **local** : l'étape M est une moyenne pondérée, et une moyenne pondérée ne peut que raffiner l'hypothèse qu'on lui donne. Le carnet le mesure sur cinq départs aléatoires et **deux budgets d'itérations** — et c'est le budget qui fait basculer le résultat. À vingt-cinq itérations, aucun départ ne retrouve le site : le meilleur rappel vaut `0,005`, soit un site sur deux cents. À cent cinquante, deux départs sur cinq y parviennent : la graine `99` retrouve le consensus planté exactement, avec un rappel de `0,470` ; la graine `1` le retrouve décalé d'une position, avec un rappel de `0,310`. Les trois autres tombent chacune sur un optimum qui n'est pas le motif, sur des consensus enrichis en A et T. La graine qui réussit est stable — `3,0e-13` d'écart maximal sur la matrice entre cent cinquante et trois cents itérations —, ce qui établit la convergence et non la justesse.

Deux leçons, toutes deux contre l'intuition. **La métrique peut fabriquer un échec** : la graine `1` n'a qu'une position juste sur douze en lecture brute, mais onze sur douze au meilleur décalage — un désalignement d'un cran, pas une absence de motif. Mesurer par `argmax` sans tolérance aurait conclu « échec » là où le motif est là. **Et un contre-témoin peut ne pas tester ce qu'il annonce** : le départ poly-G, censé être le plus défavorable possible, est réinterprété dès sa première itération. Les probabilités nulles y sont bornées à $10^{-12}$, si bien que l'étape E classe d'abord les fenêtres par leur contenu en G ; la matrice devient enrichie en G à `0,48` contre `0,20` dans le fond, et le départ « impossible » est devenu un départ ordinaire. Il aboutit au même consensus que la graine `0`, un A/T sans rapport avec le motif, avec un rappel nul, avec ou sans seuil — un consensus lu par `argmax` ne prouve pas que les deux matrices coïncident, et ce rappel ne dit rien de l'hypothèse testée. Le résultat se rapporte comme ce qu'il est : une mesure sur l'instrument, pas sur la méthode.

### Ce que les carnets n'établissent pas

Le modèle de substitution n'a **pas de chimie** : toutes les substitutions y coûtent le même prix. Les matrices utilisées en pratique distinguent les familles d'acides aminés ; le carnet mesure l'écart, il ne le comble pas.

Les séquences simulées évoluent **site par site, indépendamment**, et les moyennes portent sur cinq jeux de `150` sites par distance : c'est peu, et le carnet donne les écarts-types plutôt que de les taire. Les conclusions valent pour ce modèle, à ces longueurs, à cette probabilité d'indel.

Le score d'un alignement local **n'est pas une probabilité**. La statistique des scores — décider si un score est plus grand que ce que donnent deux séquences sans parenté — n'est pas abordée. Les heuristiques de recherche dans une base de millions de séquences non plus : la récurrence est exacte, et son coût interdit de l'appliquer telle quelle à grande échelle.

Enfin, le juge de la section 6 est une **bibliothèque** : il établit que deux implémentations indépendantes rendent le même nombre sur les cas essayés, pas que la convention des brèches affines soit le bon modèle biologique, ni que le maximum d'un score additif soit l'alignement vrai.

Le second carnet, lui, travaille sur un **fond i.i.d.** de composition fixe, sur **un seul brin**, et sur un motif dont la longueur est connue d'avance. Son EM suppose un site par séquence, à position inconnue, et son étape E ignore le fond : une fenêtre riche en bases que la matrice courante favorise pèse lourd, même quand ces bases sont courantes dans le fond. Les deux points l'écartent du modèle de Bailey et Elkan (1994), dont le mélange compte le fond comme seconde composante et modélise zéro, une ou plusieurs occurrences par séquence. Enfin, ce qu'il mesure est « le site est-il retrouvé ? », non « le motif est-il estimé ? » : la graine `1` retrouve les sites avec un motif décalé d'une position.

## Installation — pratique, tous niveaux

Les deux carnets tournent sur le noyau `python3`, sans GPU. Seul le premier appelle le réseau, une fois, pour charger quatre séquences protéiques publiques depuis les *E-utilities* de la NCBI ; le second est entièrement local, et ses graines sont affichées. Aucune séquence n'est recopiée dans le dépôt.

```bash
python -m pip install jupyterlab ipykernel numpy matplotlib biopython
jupyter lab MyIA.AI.Notebooks/BioMedecine/Sequences/
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** La recherche de motif est livrée par le second carnet ; reste ouvert son prolongement par un moteur d'inférence probabiliste, avec `Probas/Infer/`. Puis les modèles de profil, qui remplacent la matrice de substitution par une matrice par position, et les heuristiques de graines, qui rendent la recherche en base possible.

**Questions ouvertes.** La statistique d'un score local, et la part d'un score qui doit à la longueur des séquences plutôt qu'à leur ressemblance. Les matrices construites sur des alignements observés, et ce qu'un modèle de mutation uniforme ne peut pas en dire. L'alignement de plusieurs séquences à la fois, qui n'est pas une répétition de l'alignement par paires. Et ce que l'alignement optimal dit de l'histoire des séquences, qui est une question de biologie et non de score.

**Ponts.** [NLP](../../NLP/05-HMM-Viterbi.ipynb) porte l'algorithme de Viterbi : la même programmation dynamique sur un chemin, dans un modèle où les états sont cachés. [Probas/Infer](../../Probas/Infer/README.md) porte l'inférence probabiliste, qui donnerait au motif planté un second moteur d'estimation. La série [Search](../../Search/README.md) traite la programmation dynamique pour elle-même, et les stratégies qui évitent de tout parcourir. Les sous-séries [Structures](../Structures/README.md) et [Dynamiques](../Dynamiques/README.md) posent, pour la molécule et pour les populations, les mêmes questions de modèle et de contrôle.

## Ressources — tous niveaux

- Modèle et mesures : matrice de substitution construite depuis un modèle de mutation déclaré, brèches affines, récurrences écrites à partir de zéro. Les séquences simulées sont engendrées par le carnet ; les quatre protéines réelles sont chargées à l'exécution depuis la NCBI, dont la page des politiques déclare ne poser aucune restriction sur l'usage ou la distribution de ses données moléculaires.
- Bibliothèque de référence : Biopython (Cock et al., 2009), utilisée dans le premier carnet pour sa matrice BLOSUM62 et son aligneur `PairwiseAligner`, et dans le second pour `Bio.motifs` et `PositionSpecificScoringMatrix`. La copie archivée et les conditions de diffusion sont données dans les références du premier carnet.
- Littérature de la recherche de motif : quatre textes sont cités en fin de second carnet. Trois sont déposés au gisement bibliographique partagé, deux ont été lus sur leurs deux premières pages, le quatrième n'a pas été obtenu. Ce que le carnet retient du texte de Bailey et Elkan (1994), de celui de Schneider et Stephens (1990), et ce qu'il ne doit à aucun des quatre y sont écrits référence par référence.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
