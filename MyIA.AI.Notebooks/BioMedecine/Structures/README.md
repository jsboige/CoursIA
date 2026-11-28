# Structures — la liaison hydrogène comme rotation, le repliement comme paysage d'énergie

[↑ Bio & Médecine](../README.md)

Une liaison hydrogène referme le squelette d'une protéine ; encore faut-il savoir de quel objet géométrique on parle. Ce pli commence par le plus petit d'entre eux : une chaîne peptidique construite atome par atome, à partir de longueurs et d'angles déclarés, dont on mesure la vis. Ce premier carnet ne replie encore aucune protéine. Il établit le vocabulaire et les instruments qui rendent un repliement calculé vérifiable — sans eux, une conformation trouvée par un algorithme ne se distingue pas d'une chaîne quelconque.

Le second carnet passe au pli lui-même, sur le plus petit modèle qui se calcule en entier : une chaîne de deux espèces de résidus posée sur un réseau carré, dont l'énergie compte les contacts entre résidus hydrophobes. Là où le premier décrit une conformation, le second cherche la meilleure parmi toutes, et dit où une marche aléatoire passe son temps.

Le point de départ est un fait de Penner : dans une protéine, les liaisons hydrogène qui referment le squelette peuvent chacune se lire comme un élément du groupe des rotations de l'espace, et la statistique de ces éléments sur les structures déposées prend la forme d'une distribution sur $SO(3)$ dont le mode est le tour de l'hélice $\alpha$ idéale. Le carnet reprend la géométrie et le critère, pas la statistique : aucune structure expérimentale n'est lue.

Le second carnet part d'un texte de Gromov, *Crystals, Proteins, Stability and Isoperimetry* (2010), qui formule le repliement de deux façons : comme la recherche du minimum d'une énergie sur un espace de configuration, et comme une marche aléatoire biaisée par cette énergie. Le carnet joue cette double formulation sur le plus petit modèle qui se calcule en entier : une chaîne de trois à seize résidus sur un réseau carré, chacun hydrophobe ou polaire, dont l'énergie est l'opposé du nombre de contacts entre résidus hydrophobes. Il énumère l'espace des conformations, démontre deux bornes sur le nombre de contacts, décrit le paysage d'une séquence, résout exactement la loi de long terme de la marche, et balaye toutes les séquences de trois tailles. Là encore, aucune protéine réelle n'est lue : le texte apporte la formulation, le carnet les calculs.

Le troisième carnet change de molécule et de géométrie. Il prend l'ARN circulaire — la forme sous laquelle se répliquent les viroïdes, les plus petits réplicateurs connus — et y transporte la récurrence de comptage de Nussinov : une structure est un appariement de bases qui ne se croisent pas, A–U et G–C, séparé par une boucle minimale, et l'on cherche le nombre maximal de paires. Le cercle retire aux extrémités leur rôle : aucune base n'a de côté libre, et la boucle minimale s'applique aussi à la paire qui enjambe l'origine. Le carnet démontre ce que cette différence fait à l'optimum, le mesure par deux voies indépendantes — énumération exhaustive et programme linéaire en nombres entiers —, et établit qu'un nombre de structures ne désigne pas une structure : à neuf bases, aucune des 510 séquences A/U n'admet de repliement unique. Aucune séquence de viroïde n'est lue : le texte de Pallas, Di Serio et Suzuki fournit le cadre biologique, le carnet les calculs.

Les carnets s'adressent à un étudiant de licence avancée qui connaît Python et l'algèbre linéaire élémentaire ; le second suppose en plus une marche aléatoire sur un graphe et sa loi stationnaire, qu'il utilise sans les redéfinir ; le troisième n'exige que la récurrence de comptage, qu'il démontre avant de s'en servir. Aucune connaissance préalable de la biophysique des protéines n'est supposée : le squelette, les angles dièdres et la liaison hydrogène sont introduits avant d'être mesurés dans le premier carnet ; le second n'en a pas besoin, son modèle est plus grossier.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Structures-01. Le carnet construit une chaîne, mesure une vis, retrouve l'hélice $\alpha$, puis montre trois cas où le critère se trompe ou ne peut pas conclure. Poursuivez par Structures-02, qui passe du squelette au pli : il énumère les conformations d'une chaîne sur un réseau, compte les minima de son énergie, et calcule la loi de long terme de la marche qui cherche le pli. Terminez par Structures-03, qui transporte la même recherche de paires sur un ARN circulaire et montre ce que le cercle change à l'optimum.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque section mesure et ce qu'elle laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les feuilles du pli — repliement d'ARN par comptage de paires, puis par énergie minimale — et les questions qu'elles ouvrent.

## Parcours principal — Licence avancée

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Structures-01 — Liaisons hydrogène et géométrie du squelette protéique](Structures-01-Liaisons-Hydrogene-Squelette-Proteique-Python.ipynb) | La construction d'une chaîne peptidique à paramètres déclarés, et son aller-retour à `5,7e-14°` près sur les dièdres. La régularité translationnelle d'une hélice à angles constants : `3,824779340040` Å d'un $C_\alpha$ au suivant, `+50,9154815749°` de torsion, sur toute la chaîne. Un critère de liaison hydrogène à quatre conditions, qui retient la liaison $i+4 \to i$ au point de référence et refuse l'affectation inverse. La carte des couples $(\varphi,\psi)$ : `154` cases sur `5184`, en deux régions miroir de `77` cases, où l'hélice tourne de `3,5099` à `4,1289` résidus par tour. La rotation du repère peptidique, dont l'axe est celui de l'hélice et dont l'angle vaut la vis, à `1,00000000` de cosinus. | Licence avancée : Python, algèbre linéaire, géométrie dans l'espace. Outils : numpy, scipy, matplotlib. | Les trois exercices, puis la feuille suivante, Structures-02. |
| 02 | [Structures-02 — Repliement sur réseau : espace des conformations, énergie et bornes](Structures-02-Repliement-Reseau-Energie-Isoperimetrie-Python.ipynb) | Le dénombrement exact d'un espace de conformations, `4067` à $N = 10$ et `30 073` à $N = 12$, par deux algorithmes indépendants ; le nombre de plis, `2034` et `15 037`, deux fois plus petit que le premier, à une unité près. Deux bornes sur le nombre de contacts, isopérimétrique et de parité, démontrées puis éprouvées sur les `1024` séquences de $N = 10$, sans un dépassement. Le paysage d'une séquence : `92` minima locaux stricts, dont `90` hors du pli natif. La loi stationnaire de la marche biaisée, qui n'est pas la loi de Gibbs : `0,2256` de distance en variation totale, et `3,12 %` de sa masse dans le pli natif. Un temps moyen de retour au pli de `32,0` pas, contre `246` pas de première atteinte médiane. La part des séquences à pli unique : `6` sur `1024` à $N = 10$. | Licence avancée : Python, marche aléatoire sur un graphe. Outils : numpy, scipy, matplotlib. | Les trois exercices, puis la feuille 03, sur l'ARN circulaire. |
| 03 | [Structures-03 — ARN circulaire et repliement en paires](Structures-03-ARN-Circulaire-Repliement-Paires-Python.ipynb) | Le comptage de Nussinov transporté sur un cercle : une structure est un appariement non croisé, A–U et G–C, séparé par une boucle minimale de trois positions, et l'objectif est le nombre maximal de paires. Ce que refermer retire : `AGGGGU` passe de `1` à `0` paire, `GGGGAAUUCC` de `2` à `1`, `AUAUAUAUAU` de `3` à `1`. Trois conséquences démontrées puis mesurées sur `3 840` rotations : l'optimum circulaire ne dépend pas de la coupe, il ne dépasse jamais l'optimum linéaire, et il n'est pas le maximum des coupes — les deux coïncident dans `52,22 %` des cas à douze bases et `75,33 %` à cinquante. Deux contrôles indépendants : énumération exhaustive, sans écart sur toutes les séquences A/U de `4` à `12` bases et sur `300` cas par taille à quatre lettres ; programme linéaire en nombres entiers, sans écart non plus sur `60` cas par longueur, mais seulement avec une contrainte de degré par base — sans elle il empile deux paires sur une position, dans `60` cas sur `60` à vingt bases. Un nombre ne désigne pas une structure : à `8` bases, `64` séquences sur `256` n'ont qu'un repliement optimal ; à `9`, aucune des `510` séquences A/U n'en a un, par un argument de parité sur un cycle impair. | Licence avancée : Python, programmation dynamique, optimisation en nombres entiers. Outils : numpy, scipy (`scipy.optimize.milp`), matplotlib. | Les trois exercices, puis la feuille de repliement d'ARN par minimisation d'énergie. |

La feuille suivante — le repliement d'ARN par minimisation d'une énergie — viendra s'ajouter ici.

## Approfondissements — Licence avancée

### Autour de 01 : quatre contrôles, quatre natures

Le carnet ne répète pas quatre fois le même contrôle. Chacun juge une chose différente, et c'est cette variété qui fait sa valeur pédagogique.

**Un aller-retour.** Les coordonnées sont construites à partir de couples $(\varphi,\psi)$ tirés au hasard, puis les dièdres sont relus sur ces coordonnées. L'écart maximal vaut `5,7e-14°` sur $\varphi$, `8,5e-14°` sur $\psi$ et `5,7e-14°` sur $\omega$. Les deux voies partagent le code de construction : un accord n'est donc pas une surprise, mais un désaccord révélerait une erreur de placement qui resterait sinon invisible. La planéité du groupe peptidique est tenue à `6,8e-16` Å en moyenne et `2,6e-15` Å au maximum.

**Une régularité translationnelle.** Une chaîne à angles constants doit être un objet rigide qui se répète. Le carnet le vérifie sans formule : la distance entre $C_\alpha$ voisins vaut `3,824779340040` Å, l'angle de vis `90,8927803075°`, la torsion `+50,9154815749°`, et les étendues le long de la chaîne restent sous `4,0e-15` Å et `2,1e-13°`. Le même triplet est retrouvé à douze décimales au début et au milieu de la chaîne.

**Une formule analytique.** Pour une hélice idéale, l'angle de vis, le pas et le rayon se calculent à partir des seuls paramètres déclarés. Au point de référence, la mesure donne `+99,907878°`, `1,530383` Å et `2,289443` Å ; la formule donne les mêmes valeurs, à `0,0` degré, `1,6e-15` Å et `4,4e-16` Å près.

**Une identité de transformation.** La rotation qui amène le repère peptidique d'un résidu sur le suivant doit être la vis elle-même. Son angle vaut `99,9079°` pour un pas, son déterminant `1,000000000000`, et le cosinus entre son axe et l'axe de la vis `1,00000000`. Sur quatre pas, elle vaut `39,6315°`, ce qui est exactement `4κ` ramené dans $[0,180]$.

### Autour de 01 : les contre-témoins, et ce qu'ils attrapent

Un contrôle qui ne sait pas échouer ne prouve rien. Le carnet construit trois cas d'échec — et un quatrième, plus dérangeant, où le critère réussit alors qu'il ne devrait pas.

- **Le miroir.** Le critère retient la liaison de l'hélice gauche aussi bien que celle de l'hélice droite : $H\cdots O$ à `1,978` Å, $N\cdots O$ à `2,975` Å. Il est **achiral**. Les deux hélices se distinguent ailleurs : la torsion du repère vaut `-50,9155°` et le pas de vis `-99,9079°`, quand l'angle de rotation reste `39,6315°`. C'est ce contre-témoin qui établit que le modèle employé ne peut pas dire pourquoi l'hélice $\alpha$ est droite.
- **La conformation étendue.** À $(\varphi,\psi) = (-180°,-180°)$, la chaîne s'allonge à `32,8047` Å sur neuf pas, soit `3,6450` Å par résidu, et aucune liaison $i\pm4$ n'est retenue — les distances valent `16,803` Å et `12,343` Å. Une conformation qui n'est pas une hélice ne fabrique donc pas de liaison hydrogène par accident.
- **La liaison peptidique tordue.** Avec $\omega = 160°$, la planéité du groupe se dégrade à `0,1600` Å, et le critère retient pourtant une liaison avec $H\cdots O$ à `0,4239` Å, $N\cdots O$ à `1,3744` Å et un angle de `143,6°`. Un hydrogène à quatre dixièmes d'ångström d'un oxygène est un empilement stérique, pas une liaison : le critère ne fixe que des bornes supérieures de distance et des bornes inférieures d'angle, et c'est la planéité seule qui arrête ce cas.
- **La carte, à deux lectures.** Les quatre conditions retiennent `154` cases sur `5184`, soit `2,97 %` ; les deux conditions de distance seules en retiennent `178`, soit `3,43 %`. Les conditions d'angle retirent donc `24` cases que les distances acceptaient. La carte n'est pas un point mais deux régions miroir de `77` cases, de barycentres $(-56{,}23°, -57{,}73°)$ et $(56{,}23°, 57{,}73°)$.

### Autour de 01 : le bassin, et ce qu'il contient

Chaque case retenue est une hélice régulière : le carnet recalcule ses paramètres, et le bassin couvre `3,5099` à `4,1289` résidus par tour, un pas axial de `1,0315` à `1,6532` Å, un rayon de `2,2102` à `2,6706` Å, un angle de vis de `89,7692°` à `98,4728°` et une torsion de `28,8020°` à `56,6658°`, d'un seul signe. Le point de référence $(-57°,-47°)$ n'est pas une case de la grille : sa case la plus proche est $(-55°,-45°)$, retenue, et il occupe le rang `8` sur `77` en résidus par tour.

### Autour de 02 : deux bornes, et celle qui mord

Les deux bornes disent des choses différentes. L'isopérimétrique, $N + 1 - 2\sqrt{N}$ pour une chaîne tout hydrophobe, vient du contour de la réunion des carrés unité centrés sur les sites : deux carrés de sites voisins, liaisons de la chaîne comprises, partagent un côté, et chaque colonne comme chaque rangée occupée apporte au moins deux côtés au contour, ce qui borne celui-ci par $4\sqrt{N}$. La parité vient du damier : deux sites voisins sont de couleurs opposées, donc un contact unit toujours un résidu de rang pair et un résidu de rang impair. Le carnet démontre les deux, puis calcule le maximum exact de chaque séquence de $N = 10$ : aucune ne dépasse la plus petite des siennes.

La plus contraignante change avec le nombre de résidus hydrophobes. Jusqu'à $k = 3$, toutes les séquences atteignent la borne de parité. À $k = 4$, la parité est atteinte par `154` séquences sur `210` et l'isopérimétrie par `52` ; à $k = 5$, l'ordre s'inverse : `34` et `154` sur `252`. À partir de $k = 6$, plus aucune n'atteint la parité, alors que `39` atteignent encore le plancher de la borne isopérimétrique. Quand les hydrophobes sont rares, c'est le damier qui limite ; quand ils sont nombreux, c'est la géométrie.

Le contre-témoin est la séquence alternée : sa borne de parité est nulle, aucun contact n'est possible, et c'est bien ce que donne l'énumération.

### Autour de 02 : la loi de la marche n'est pas celle qu'on attend

On attend d'une marche biaisée par une énergie qu'elle passe dans chaque état un temps proportionnel à $\exp(-E)$ : c'est la loi de Gibbs. Ce n'est pas ce que donne la marche à temps discret du carnet. À chaque pas, le poids de chaque voisin est divisé par la somme des poids de tous les voisins, et un état entouré de bons états en profite : la loi stationnaire est $\pi(x) \propto \exp(-E(x)) \sum_{z \sim x} \exp(-E(z))$. Le carnet l'établit en deux lignes, la vérifie par la résolution du système $\pi P = \pi$, dont le résidu est de l'ordre de $10^{-16}$, et mesure l'écart : `0,2256` en variation totale.

Le contre-témoin est l'énergie nulle. Là où la loi de Gibbs est la loi uniforme, la marche reste proportionnelle au degré de chaque état : `0,1050` de variation totale entre les deux. L'écart à la loi de Gibbs a donc une cause identifiée, la normalisation parmi les voisins, et non un défaut de calcul.

Deux temps sont à ne pas confondre. Le temps moyen de retour au pli natif vaut `32,0` pas, par la formule de Kac : il se compte depuis le pli lui-même. Le temps de première atteinte, depuis un état tiré au hasard hors du pli, vaut `246` pas en médiane sur `200` marches, et au moins `442` pas pour le quart le plus lent : le second vaut presque huit fois le premier. Une marche qui vient de trouver le pli y revient vite ; une marche partie d'ailleurs met des centaines de pas à le trouver.

### Autour de 02 : la part des séquences qui n'ont qu'un pli

Gromov demande quelle part des chaînes se replient, et laisse la question ouverte. Le carnet la pose sur son modèle : une séquence a un pli unique quand les conformations de son minimum forment un seul pli. Elles sont `7` sur `256` à $N = 8$, `6` sur `1024` à $N = 10$, `87` sur `4096` à $N = 12$, soit `2,7 %`, `0,6 %` et `2,1 %` : la part n'est pas décroissante d'une taille à l'autre, et trois tailles ne disent rien sur une décroissance exponentielle. Aucune ne compte moins de quatre résidus hydrophobes : il en faut assez pour qu'un arrangement soit seul à réaliser le maximum. À $N = 10$, la première qui compte autant de $H$ que de $P$, dans l'ordre du balayage, est `HHPHPPHPPH`, la séquence étudiée en détail. Comme contrôle, chaque séquence a été comparée à sa lecture renversée : zéro écart aux trois tailles.

### Autour de 03 : le cercle retire les extrémités

Refermer une molécule n'ajoute pas de paires libres : chaque corde gagne une seconde boucle, celle qui passe par l'origine, et la contrainte de longueur minimale s'y applique aussi. Deux témoins se lisent à la main.

Sur `AGGGGU`, une seule paire est autorisée en ligne, $(0,5)$ : quatre positions la séparent, donc $5 > 3$. Sur le cercle, $6 - 5 = 1$ : la boucle de l'autre côté ne contient aucune position libre, la paire est refusée, et l'optimum tombe de `1` à `0`. Sur `AUAUAUAU`, quatre paires sont autorisées en ligne — $(0,5)$, $(0,7)$, $(1,6)$ et $(2,7)$ ; sur un cercle de huit positions, la condition des deux côtés impose $3 < d < 5$, or les distances valent `5` et `7` : aucune ne passe. L'optimum linéaire vaut `2`, le circulaire `0`.

Le carnet démontre ensuite ce que ces cas annoncent : une structure circulaire non croisée est exactement une structure non croisée sur les paires autorisées au sens du cercle. Trois conséquences en découlent, mesurées séparément sur cinq longueurs et trente molécules par longueur. L'optimum circulaire est le même à toute coupe — `0` optimum variable sur `3 840` rotations ; il ne dépasse jamais l'optimum linéaire de la coupe courante — `0` violation sur ces mêmes rotations ; et il n'est pas le maximum des optimums linéaires, puisque la part des coupes où les deux coïncident vaut `0,5222` à douze bases et `0,7533` à cinquante, sans jamais atteindre `1`. Le cercle n'ajoute donc pas de liberté : il en retire, et il la retire uniformément.

### Autour de 03 : deux contrôles, et la contrainte qu'on oublie

Énumérer toutes les structures d'une molécule donne l'optimum sans récurrence : c'est lent, mais c'est une définition. Le carnet s'en sert comme d'un juge, sur deux alphabets. À deux lettres, toutes les séquences de quatre à douze bases passent, dans les deux géométries, sans un écart ; et la taille de l'énumération dit pourquoi elle s'arrête — `1`, `2`, `4`, `8`, `16`, `31`, `62`, `119`, `238` structures au plus, qui doublent à chaque base jusqu'à huit, puis ralentissent à mesure que l'interdiction de croisement mord. À quatre lettres, `150` molécules par taille et par géométrie, soit `300` cas : aucun écart non plus, avec `894`, `2 160`, `4 801` et `12 252` structures énumérées au total sur les `300` cas de huit, dix, douze et quatorze bases.

Le second contrôle est un programme linéaire en nombres entiers résolu par `scipy.optimize.milp` : une variable par paire autorisée, leur somme pour objectif, et deux familles de contraintes qui interdisent le croisement. La seconde famille est celle qu'on oublie — sans une contrainte de degré par base, rien n'empêche deux paires de partir de la même position. Le carnet le mesure au lieu de l'affirmer : sur `AAAUUU`, le noyau trouve `1` paire et le programme relâché `2` ; à vingt bases, le relâché dépasse l'optimum dans `60` cas sur `60`, de six paires au plus. Avec la contrainte, `0` écart sur `60` cas à chacune des longueurs `14`, `16`, `18`, `20` et `24`, pour un programme qui passe de `15` variables et `52` contraintes à `57` et `752`.

### Autour de 03 : un nombre ne désigne pas une structure

Un optimum est un nombre ; une structure est un ensemble de paires. Le carnet sépare les deux, et trouve un cas où le nombre ne désigne rien.

À neuf bases, sur l'alphabet A/U, l'argument est géométrique et tient en trois lignes. Les paires autorisées sont les neuf cordes de distance circulaire `4` : la condition des deux côtés impose $3 < d < 6$, et seule $d = 4$ subsiste. Ces neuf cordes forment un cycle de neuf sommets, chacune joignant $i$ à $i+4$. Une paire A–U n'existe que là où la lettre change ; or un cycle impair n'admet pas un nombre impair de changements, donc il y en a un nombre pair, et au moins deux. Deux cordes d'un tel cycle partagent toujours une extrémité ou se croisent : l'optimum vaut au plus `1`, et deux structures optimales distinctes ne peuvent pas coexister. La mesure suit : sur les `512` séquences de neuf bases, `510` ont un optimum non nul et **aucune** n'a de repliement unique.

À huit bases, le compte est exact et tombe juste. Les seules cordes autorisées sont les quatre diamètres, et une structure optimale est un choix de diamètres deux à deux non croisés : deux diamètres se croisent toujours, donc l'optimum vaut `1` dès qu'un diamètre A–U existe, et la structure est unique exactement dans ce cas. Chaque diamètre est A–U avec probabilité $1/2$, d'où $4 \times (1/2)^4 = 1/4$, soit `64` séquences sur `256` — le nombre mesuré. Le compte des séquences à une seule paire autorisée est d'ailleurs le même `64`.

Le nombre de structures optimales, lui, ne suit aucune règle simple : `2,133` en moyenne à huit bases, `4,518` à neuf, `2,632` à dix, `5,830` à douze. La part des séquences à optimum non nul qui n'admettent qu'un seul repliement optimal ne bouge presque plus : `0,267` à huit bases, `0` à neuf, `0,391` à dix, `0,393` à douze.

### Ce que le carnet n'établit pas

Le modèle est **achiral** : il accepte une hélice et son image. C'est une propriété du critère, montrée par contre-témoin, pas un défaut d'implémentation.

Tous les paramètres géométriques sont **déclarés** — longueurs, angles de valence, et le couple de référence lui-même. Le dernier exercice mesure la sensibilité du bassin à l'angle $N-C_\alpha-C$ ; les autres n'ont pas été balayés, et une déviation réelle de quelques degrés déplacerait les frontières du bassin sans le faire disparaître.

Le critère admet des empilements stériques, et aucune structure expérimentale n'est lue : le carnet mesure ce qu'un modèle prédit, pas ce que les protéines font.

Les exercices du premier carnet ouvrent trois pistes : la sensibilité de la carte au pas de la grille, l'inventaire chiral d'un couple d'angles, et l'effet d'un angle $N-C_\alpha-C$ déclaré à `111°` plutôt qu'à `109,47°`.

Le second carnet n'extrapole rien non plus. Ses chaînes comptent de $3$ à $16$ résidus, et l'espace entier n'est énuméré que jusqu'à $N = 12$ : ce qu'il mesure n'est dit que pour ces tailles. Son énergie est additive, alors que le texte de Gromov dit d'une protéine réelle que son énergie n'est pas une somme de termes de paire : les deux bornes valent pour cette énergie, et pour elle seule. Et sa marche est à temps discret, ce qui est la cause de l'écart à la loi de Gibbs.

Ses exercices ouvrent trois autres pistes : la borne isopérimétrique boîte par boîte, le paysage sans les déplacements d'extrémité, et la part du pli natif quand la température tend vers zéro.

Le troisième carnet ne lit aucune séquence de viroïde : la revue fournit le cadre biologique, le carnet les calculs, et ses molécules sont tirées au hasard. Son modèle n'a pas d'énergie — il maximise un nombre de paires à longueur de boucle fixée —, et le balayage de cette longueur montre que le choix n'est pas neutre : à deux cents bases, passer de $\ell = 0$ à $\ell = 3$ retire près de dix-huit paires en moyenne. La décroissance du coût par position ajoutée est constatée, pas démontrée ; la forme en U de l'optimum selon la composition est constatée elle aussi, et l'explication proposée — densité de partenaires — reste une hypothèse. Le plafond de composition $\min(n_A,n_U) + \min(n_G,n_C)$ majore de loin : l'écart moyen vaut `5,335` paires à cinquante bases, `32,550` à trois cents, et il croît avec la longueur. Les moyennes portent sur cinquante molécules, sans dispersion donnée, et l'optimum circulaire n'est pas calculé sur une énergie de boucle : c'est précisément ce que la feuille suivante ajoute.

Ses exercices ouvrent trois pistes de plus : le gain de la paire G–U, que le modèle autorise sans le peser, l'invariance de l'optimum circulaire sous rotation vérifiée par énumération exhaustive, et l'effet d'une substitution de base sur l'optimum.

## Installation — pratique, tous niveaux

Les trois carnets tournent sur le noyau `python3`, sans GPU. Ils sont déterministes : le tirage des dièdres du contrôle de Structures-01, les trois trajectoires simulées de Structures-02 et les séquences tirées de Structures-03 sont semés, chaque exécution rejoue les mêmes nombres.

```bash
python -m pip install jupyterlab ipykernel numpy scipy matplotlib
jupyter lab MyIA.AI.Notebooks/BioMedecine/Structures/Structures-01-Liaisons-Hydrogene-Squelette-Proteique-Python.ipynb
jupyter lab MyIA.AI.Notebooks/BioMedecine/Structures/Structures-02-Repliement-Reseau-Energie-Isoperimetrie-Python.ipynb
jupyter lab MyIA.AI.Notebooks/BioMedecine/Structures/Structures-03-ARN-Circulaire-Repliement-Paires-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** Le repliement d'ARN par minimisation d'énergie, après le comptage de paires de Structures-03 : deux façons de poser le même problème, dont la première sert de contrôle à la seconde sur de petites séquences. Et l'apprentissage sur des graphes de protéines, où la géométrie mesurée dans Structures-01 devient une description d'entrée.

**Questions ouvertes.** Pourquoi l'hélice $\alpha$ est droite, ce que ce modèle achiral ne peut pas dire. Ce que devient la carte quand on ajoute au critère une borne inférieure de distance et un contrôle de collision, comme le cas de la liaison peptidique tordue le suggère. Quelle statistique de ces rotations apparaît sur des structures déposées, question qui demande une base expérimentale et DSSP, et que le carnet ne traite pas. Pourquoi les protéines se replient vite, alors que Structures-02 compte `92` minima locaux pour une chaîne de dix résidus ; quelle part des séquences a un pli unique, et si cette part décroît exponentiellement, ce que trois tailles ne disent pas ; et ce que devient ce paysage sur un réseau à trois dimensions.

**Ponts.** [Physique/Numerique](../../Physique/Numerique/README.md) mesure ce qu'un schéma fait à une équation de conservation ; dans Structures-01, c'est la régularité d'un objet discret qui sert de juge. Les solveurs de contraintes de [Search](../../Search/README.md) et de [SymbolicAI](../../SymbolicAI/README.md) sont les outils de la feuille de repliement d'ARN, où l'optimum d'une énergie devient un problème combinatoire. Structures-02 s'arrête là où l'espace cesse d'être énumérable : chercher sans tout parcourir est le sujet de la série Search, dont le recuit simulé est la marche biaisée de sa section 4, à température décroissante. La sous-série [Dynamiques](../Dynamiques/README.md) pose, pour les populations, la question symétrique de sa loi de long terme.

## Ressources — tous niveaux

- Modèle et mesures : squelette peptidique à paramètres déclarés, critère de liaison hydrogène emprunté à DSSP tel que Penner le reprend, carte des couples $(\varphi,\psi)$. Aucune donnée externe ; toutes les chaînes sont construites à paramètres connus.
- Repliement sur réseau : le texte de Gromov, *Crystals, Proteins, Stability and Isoperimetry* (2010), et son entretien avec Jaimungal sur la chaîne *Theories of Everything*. Les passages utilisés et la copie archivée sont donnés dans Structures-02 ; l'espace des conformations, lui, est énuméré par le carnet.
- ARN circulaire : la revue de Pallas, Di Serio et Suzuki, *The simplest RNA replicons, viroids* (2023), qui présente les viroïdes comme des ARN circulaires non codants de 250 à 400 nucléotides, les plus petits réplicateurs connus. Les passages utilisés et la copie archivée sont donnés dans Structures-03 ; aucune séquence de viroïde n'est lue par le carnet.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
