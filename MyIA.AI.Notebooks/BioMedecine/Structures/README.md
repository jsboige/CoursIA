# Structures — la liaison hydrogène comme rotation, et la carte des hélices

[↑ Bio & Médecine](../README.md)

Une liaison hydrogène referme le squelette d'une protéine ; encore faut-il savoir de quel objet géométrique on parle. Ce pli commence par le plus petit d'entre eux : une chaîne peptidique construite atome par atome, à partir de longueurs et d'angles déclarés, dont on mesure la vis. Il ne replie encore aucune protéine. Il établit le vocabulaire et les instruments qui rendent un repliement calculé vérifiable — sans eux, une conformation trouvée par un algorithme ne se distingue pas d'une chaîne quelconque.

Le point de départ est un fait de Penner : dans une protéine, les liaisons hydrogène qui referment le squelette peuvent chacune se lire comme un élément du groupe des rotations de l'espace, et la statistique de ces éléments sur les structures déposées prend la forme d'une distribution sur $SO(3)$ dont le mode est le tour de l'hélice $\alpha$ idéale. Le carnet reprend la géométrie et le critère, pas la statistique : aucune structure expérimentale n'est lue.

Le carnet s'adresse à un étudiant de licence avancée qui connaît Python et l'algèbre linéaire élémentaire. Aucune connaissance préalable de la biophysique des protéines n'est supposée : le squelette, les angles dièdres et la liaison hydrogène sont introduits avant d'être mesurés.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Structures-01. Le carnet construit une chaîne, mesure une vis, retrouve l'hélice $\alpha$, puis montre trois cas où le critère se trompe ou ne peut pas conclure.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque section mesure et ce qu'elle laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les feuilles suivantes du pli — repliement d'ARN par Nussinov puis par énergie minimale, modèle HP de protéines sur réseau — et les questions qu'elles ouvrent.

## Parcours principal — Licence avancée

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Structures-01 — Liaisons hydrogène et géométrie du squelette protéique](Structures-01-Liaisons-Hydrogene-Squelette-Proteique-Python.ipynb) | La construction d'une chaîne peptidique à paramètres déclarés, et son aller-retour à `5,7e-14°` près sur les dièdres. La régularité translationnelle d'une hélice à angles constants : `3,824779340040` Å d'un $C_\alpha$ au suivant, `+50,9154815749°` de torsion, sur toute la chaîne. Un critère de liaison hydrogène à quatre conditions, qui retient la liaison $i+4 \to i$ au point de référence et refuse l'affectation inverse. La carte des couples $(\varphi,\psi)$ : `154` cases sur `5184`, en deux régions miroir de `77` cases, où l'hélice tourne de `3,5099` à `4,1289` résidus par tour. La rotation du repère peptidique, dont l'axe est celui de l'hélice et dont l'angle vaut la vis, à `1,00000000` de cosinus. | Licence avancée : Python, algèbre linéaire, géométrie dans l'espace. Outils : numpy, scipy, matplotlib. | Les trois exercices, puis les feuilles de repliement (voir « Pour aller plus loin »). |

Un seul carnet pour l'instant. Les feuilles suivantes — le repliement d'ARN par Nussinov puis par énergie minimale, le modèle HP de protéines sur réseau — viendront s'ajouter ici.

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

### Ce que le carnet n'établit pas

Le modèle est **achiral** : il accepte une hélice et son image. C'est une propriété du critère, montrée par contre-témoin, pas un défaut d'implémentation.

Tous les paramètres géométriques sont **déclarés** — longueurs, angles de valence, et le couple de référence lui-même. Le dernier exercice mesure la sensibilité du bassin à l'angle $N-C_\alpha-C$ ; les autres n'ont pas été balayés, et une déviation réelle de quelques degrés déplacerait les frontières du bassin sans le faire disparaître.

Le critère admet des empilements stériques, et aucune structure expérimentale n'est lue : le carnet mesure ce qu'un modèle prédit, pas ce que les protéines font.

Les exercices ouvrent trois pistes : la sensibilité de la carte au pas de la grille, l'inventaire chiral d'un couple d'angles, et l'effet d'un angle $N-C_\alpha-C$ déclaré à `111°` plutôt qu'à `109,47°`.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3`, sans GPU. Il est déterministe : le tirage des dièdres du contrôle est semé, chaque exécution rejoue les mêmes nombres.

```bash
python -m pip install jupyterlab ipykernel numpy scipy matplotlib
jupyter lab MyIA.AI.Notebooks/BioMedecine/Structures/Structures-01-Liaisons-Hydrogene-Squelette-Proteique-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** Le repliement d'ARN par l'algorithme de Nussinov, puis par minimisation d'énergie : deux façons de poser le même problème, dont la première sert de contrôle à la seconde sur de petites séquences. Le modèle HP de protéines sur réseau, dont l'optimum s'obtient par énumération exhaustive sur les petites instances, ce qui donne un juge exact à une heuristique. Et l'apprentissage sur des graphes de protéines, où la géométrie mesurée ici devient une description d'entrée.

**Questions ouvertes.** Pourquoi l'hélice $\alpha$ est droite, ce que ce modèle achiral ne peut pas dire. Ce que devient la carte quand on ajoute au critère une borne inférieure de distance et un contrôle de collision, comme le cas de la liaison peptidique tordue le suggère. Quelle statistique de ces rotations apparaît sur des structures déposées, question qui demande une base expérimentale et DSSP, et que le carnet ne traite pas.

**Ponts.** [Physique/Numerique](../../Physique/Numerique/README.md) mesure ce qu'un schéma fait à une équation de conservation ; ici, c'est la régularité d'un objet discret qui sert de juge. Les solveurs de contraintes de [Search](../../Search/README.md) et de [SymbolicAI](../../SymbolicAI/README.md) sont les outils des feuilles de repliement, où l'optimum d'une énergie devient un problème combinatoire.

## Ressources — tous niveaux

- Modèle et mesures : squelette peptidique à paramètres déclarés, critère de liaison hydrogène emprunté à DSSP tel que Penner le reprend, carte des couples $(\varphi,\psi)$. Aucune donnée externe ; toutes les chaînes sont construites à paramètres connus.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
