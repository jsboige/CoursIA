# InformationTheory — l'information comme objet calculable

[↑ Hub Information et calcul](../README.md) · [Tous les notebooks](../../README.md) · [Compression : contracter sans perdre](../Compression/README.md)

Combien d'information transporte une source, combien un canal bruité peut-il en transmettre, et comment approche-t-on cette borne en pratique ? La série fait des questions de Shannon des **objets calculables** : d'abord la mesure (entropie, information mutuelle, capacité d'un canal), puis la correction (distance de Hamming, décodage par syndrome), enfin le réseau, où un seul émetteur vers un seul récepteur ne suffit plus. Tous les calculs s'exécutent sur CPU avec numpy, sans GPU.

L'entrée est accessible avec Python et les probabilités discrètes : l'entropie se construit dès le carnet 01, et chaque carnet suivant introduit les outils qu'il emploie. La série est en cours de constitution : les carnets publiés couvrent trois paliers — mesure (01), correction (03), réseaux (08) — et la numération laisse les places des carnets suivants.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) permet de choisir sa profondeur de lecture.

- **Vous découvrez** : suivez les numéros nus. Le 01 fait d'« c'est informatif » un nombre ; le 03 montre ce que la distance d'un code achète ; le 08 étend la mesure aux situations où il y a plusieurs émetteurs, plusieurs récepteurs ou des sources corrélées.
- **Vous creusez un palier** : les exercices vivent dans les carnets eux-mêmes — le régime asymptotique du théorème du codage de canal, la borne de Hamming, le pentagone du canal à accès multiple — et chacun porte un contrôle par le calcul.
- **Vous cherchez des prolongements** : « Pour aller plus loin » relie la série à la compression (l'entropie y est la même grandeur), à la complexité et aux garanties formelles du codage.

À l'issue du parcours, vous saurez calculer l'entropie et la capacité d'une source ou d'un canal, vérifier sur des mots réels le budget de détection et de correction d'un code, et raisonner sur les régions de capacité d'un canal à accès multiple.

## Parcours principal — Découverte et Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Entropie et information mutuelle](InformationTheory-01-Entropie-Et-Information-Mutuelle.ipynb) | Calculer l'entropie de Shannon, l'entropie conditionnelle, l'information mutuelle, la divergence de Kullback-Leibler, l'inégalité de traitement de l'information et la capacité d'un canal bruité, sur des exemples exécutables. | Découverte ; Python et probabilités discrètes. | Les trois exercices du carnet : le théorème du codage de canal en régime asymptotique, l'entropie de taux d'une source avec mémoire, l'entropie différentielle. |
| 03 | [Code de Hamming et décodage par syndrome](InformationTheory-03-Code-de-Hamming-Et-Decodage-Par-Syndrome.ipynb) | Construire en numpy pur la distance de Hamming, la distance minimale et ce qu'elle achète en détection et correction, le code de parité, le code de Hamming (7,4) avec décodage par syndrome, et la borne de Hamming qui le rend parfait. | Licence ; après 01, numpy. | Dans le carnet, le budget d'une distance minimale 3 sur un code de 16 mots, et le pavage exact 16 × 8 = 128 = 2⁷. |
| 08 | [Théorie de l'information des réseaux](InformationTheory-08-Theorie-De-L-Information-Des-Reseaux.ipynb) | Calculer les bornes de capacité de quatre situations au-delà du canal unique : le canal à accès multiple, le canal de diffusion dégradé, le codage de Slepian-Wolf pour des sources corrélées, le codage réseau et la coupe minimale. | Recherche ; après 01, numpy. | Dans le carnet, le pentagone du MAC binaire, le contrôle de puissance qui atteint la capacité somme du MAC gaussien, et l'XOR du réseau papillon. |

### Le fil qui relie les paliers

Le 01 pose la mesure : l'entropie est le nombre de bits qu'une source produit réellement, l'information mutuelle ce qu'une observation apprend, la capacité la borne supérieure du débit fiable d'un canal. Le 03 répond à la question qu'elle laisse ouverte — comment approcher cette borne ? Un code allonge le message pour qu'une poignée d'erreurs du canal devienne détectable, voire corrigible : une distance minimale de 3 détecte 2 erreurs et en corrige 1, et la borne de Hamming montre que le (7,4) ne gaspille aucune place. Le 08 multiplie les objets : avec plusieurs émetteurs, plusieurs récepteurs ou des sources corrélées, la capacité n'est plus un nombre mais une *région* — et le codage réseau montre qu'un relais qui combine les flux obtient ce que le routage ne peut pas.

## Approfondissements — Recherche

Les approfondissements de ce parcours vivent dans les carnets eux-mêmes : chaque palier s'achève sur des exercices dont les énoncements portent la question suivante.

- **01** ouvre trois fronts : pourquoi la capacité est une borne de régime asymptotique, pourquoi les corrélations font baisser l'entropie par symbole (entropie de taux), et pourquoi l'entropie différentielle peut être négative.
- **03** prépare les codes réels : les codes cycliques, Reed-Solomon et BCH (ceux des disques, des QR et de la 5G), puis les LDPC et turbo qui approchent la capacité de Shannon — la direction que la série annonce pour ses carnets suivants.
- **08** s'achève sur deux exercices sur les régions MAC (atteignabilité d'un point du pentagone, choix du coefficient de contrôle de puissance) et annonce un carnet sur la sécurité au sens de l'information (canal wiretap, accord de clé secrète).

## Installation — Découverte et pratique

Utiliser un noyau Python 3.10 ou ultérieur dans un environnement virtuel, avec NumPy. Les trois carnets n'emploient que numpy et la bibliothèque standard ; les expériences tournent sur CPU, sans clé d'API. Les instructions générales sont dans les [commandes de référence](../../../docs/reference/common-commands.md).

Commencer par [01](InformationTheory-01-Entropie-Et-Information-Mutuelle.ipynb), puis recalculer l'entropie d'une distribution de son choix. Le [08](InformationTheory-08-Theorie-De-L-Information-Des-Reseaux.ipynb) est autonome : il redéfinit les fonctions qu'il emprunte au 01 pour s'exécuter seul.

## Pour aller plus loin — Recherche

- [Compression](../Compression/README.md) partage la même mesure : les codes préfixes s'y construisent contre l'entropie que le 01 calcule, et le critère MDL y paie le modèle en plus des données.
- [Complexity](../Complexity/README.md) mesure le coût de **calculer** les objets que cette série mesure — la complexité de Kolmogorov y apparaît comme miroir de la compression.
- [Information quantique](../../Physique/InformationQuantique/README.md) transporte l'entropie et le codage aux états quantiques.

## Ressources — tous niveaux

Les carnets citent les références au fil des constructions : Shannon, *A Mathematical Theory of Communication* (1948) et Cover–Thomas, *Elements of Information Theory* (2ᵉ éd., 2006) en [01](InformationTheory-01-Entropie-Et-Information-Mutuelle.ipynb) ; El Gamal et Kim, *Lecture Notes on Network Information Theory*, copie archivée au gisement, citée page à page en [08](InformationTheory-08-Theorie-De-L-Information-Des-Reseaux.ipynb).

[Retour au hub](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
