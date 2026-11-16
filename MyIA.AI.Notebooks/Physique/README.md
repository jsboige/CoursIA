---
pagetitle: "Physique — des modèles aux calculs vérifiables"
---

# Physique — des modèles aux calculs vérifiables

[↑ Parcours de notebooks](../README.md)

Comment savoir si un calcul physique représente bien le phénomène annoncé ? Cette famille part de lois de conservation, de symétries et d'intégrales de Feynman pour construire des calculs dont on peut examiner les hypothèses, les références et les limites. Une solution analytique, une identité symbolique, une simulation et la reproduction d'un résultat publié apportent des contrôles différents : apprendre à les distinguer fait partie du cours.

Le parcours s'adresse aux étudiants en physique, mathématiques appliquées et informatique scientifique, ainsi qu'aux enseignants cherchant des expériences calculables. Python et les bases du calcul différentiel permettent d'aborder la branche numérique ; les autres portes indiquent leurs prérequis propres. Vous apprendrez à passer d'une équation à une discrétisation, à relier symétrie et conservation, à comparer des voies de calcul indépendantes et à formuler précisément ce qu'un résultat établit.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue entrée dans le sujet, approfondissements et recherche.

- **Vous découvrez** : choisissez une question dans la table ci-dessous. Numérique offre une première expérience concrète avec une équation, un choc et des schémas à comparer.
- **Vous approfondissez** : suivez les paliers de Jauge ou d'Intégrales et leurs exercices, ou entrez par Information quantique si l'algèbre linéaire des matrices de densité vous est familière. Les liens entre conservation, discrétisation et contrôles numériques sont développés ensuite.
- **Vous explorez des fondements** : Constructeur et Chaînes interrogent la formulation des lois et le statut de leurs conséquences. Leur lecture demande de séparer modèle illustratif, résultat démontré et conjecture.

Il n'y a pas de séquence unique imposée entre ces branches. Les numéros des carnets décrivent une progression à l'intérieur de chaque sous-série ; les README locaux portent les inventaires et les approfondissements.

## Parcours principal — choisir une question physique

| Question | Sous-série et premier carnet | Ce qu'on y apprend | Prérequis et public | Pour approfondir |
|---|---|---|---|---|
| Comment une loi de conservation produit-elle un choc ? | [Numérique](Numerique/README.md) → [Burgers et volumes finis](Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb) | Caractéristiques, solutions faibles, vitesse de choc, flux Godunov/Rusanov et erreur de discrétisation. | Licence : Python, dérivées partielles et intégration. | Modifier le flux et examiner l'entropie discrète. |
| Que permet de déduire une symétrie ? | [Jauge](Jauge/README.md) → [Théorème de Noether](Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) | Conservation, covariance locale U(1)/SU(2), variables de lien, plaquettes et boucles de Wilson. | Licence avancée puis Master : mécanique lagrangienne, nombres complexes et matrices. | Passer du calcul symbolique au Monte Carlo sur réseau. |
| Comment calculer et contrôler une intégrale de Feynman ? | [Intégrales](Integrales/README.md) → [Triangle scalaire](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) | Représentations paramétriques, quadratures, valeurs spéciales, divergence ultraviolette et structure elliptique. | Licence avancée puis Master : intégration et fonctions spéciales ; la première amplitude est construite dans le carnet. | Relier le sunrise à ses périodes elliptiques. |
| Peut-on formuler une loi comme une tâche impossible ? | [Constructeur](Constructeur/README.md) → [Lois comme tâches](Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb) | Tâches, constructeurs, conservation, non-clonage et témoin de non-classicité dans un modèle jouet. | Lecture conceptuelle avancée : algèbre linéaire et notions quantiques pour les calculs. | Discuter ce que l'exemple de médiateur permet d'inférer. |
| Comment examiner un programme physique fondé sur un axiome informationnel ? | [Chaînes](Chaines/README.md) → [Intrication et constante de structure fine](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) | Reproduire une énumération, examiner une valeur candidate et distinguer résultats mesurés, cités et ouverts. | Recherche : algèbre linéaire, notions d'intrication et lecture critique d'une prépublication. | Vérifier les étapes de la dérivation et leurs hypothèses. |
| Comment tester l'intrication d'un état mixte par le calcul ? | [Information quantique](InformationQuantique/README.md) → [Werner, PPT, distillation, canaux à rupture d'intrication](InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) | États mixtes et purification, critère PPT, seuils de distillabilité des états de Werner et canaux à rupture d'intrication, chaque seuil cité étant recalculé sur des matrices explicites. | Master : algèbre linéaire (valeurs propres, produit tensoriel) et notions de matrice de densité. | Ajouter une dimension aux états de Werner et chercher où le critère PPT cesse d'être suffisant. |

## Comprendre les liens entre les branches — Licence et Master

### Conservation : de l'identité continue au calcul discret

[Jauge-01](Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) étudie un oscillateur isotrope dans le plan. L'invariance par rotation conduit à la conservation du moment angulaire ; une anisotropie fournit un contre-exemple qui montre le rôle de cette hypothèse. Le calcul symbolique et la trajectoire numérique répondent à deux questions complémentaires : quelle identité suit du modèle, et avec quelle précision l'intégrateur la respecte-t-il ?

[Numérique-01](Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb) part de l'équation de Burgers sous forme conservative. Lorsque les caractéristiques se croisent, la solution classique laisse place à une solution faible avec un choc. La condition de Rankine–Hugoniot fixe sa vitesse : pour les états gauche `uL = 1` et droit `uR = 0`, elle vaut `0,5`. Les flux Godunov et Rusanov sont alors comparés à cette référence.

À résolution finie, un choc numérique est étalé : cette diffusion ne suffit pas à déclarer le schéma incorrect. On examine la position du choc, l'erreur L1, le pas de temps sous condition CFL et le comportement lorsque le maillage est raffiné. Le carnet distingue les propriétés démontrées des contrôles empiriques du code. Une expérience consiste à changer le flux ou la résolution et à prévoir ce que chaque mesure devrait révéler.

### Jauge locale : préserver la structure en changeant de représentation

Dans [Jauge-02](Jauge/Jauge-02-Invariance-Jauge-U1-SU2-Python.ipynb), une phase qui dépend de la position fait apparaître un terme supplémentaire dans la dérivée ordinaire. Le champ de jauge permet de construire une dérivée covariante : la transformation locale du champ et celle de sa dérivée restent compatibles. Le passage à SU(2) introduit des matrices qui ne commutent pas et un terme d'auto-interaction. Les contrôles du carnet confrontent les identités attendues à des exemples numériques et à un contre-témoin abélien.

[Jauge-03](Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb) remplace les champs continus par des transports sur les arêtes d'un réseau. Les produits autour d'une plaquette donnent des observables invariantes de jauge ; les boucles de Wilson rendent la comparaison avec une loi d'aire accessible au calcul. Le banc étudié est celui de **U(1) compact**. En deux dimensions, une référence exacte permet de contrôler la simulation : à `β = 0,6`, la tension affichée vaut environ `1,2499`, contre `1,2474` pour la référence.

Cette proximité sert à examiner le Monte Carlo et son protocole. Elle ne démontre ni un résultat de confinement pour une théorie non abélienne continue, ni la localisation précise d'une transition de phase. L'extension en quatre dimensions permet d'observer un changement de comportement ; il faut distinguer cette observation d'une détermination quantitative de la limite continue.

### Intégrales : comparer les voies de calcul avant d'interpréter les nombres

[Intégrales-01](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) construit le triangle scalaire et compare plusieurs voies de quadrature. Pour la famille isocèle, une expression en fonctions de Clausen fournit un contrôle supplémentaire. Une valeur spéciale, `J(1,1,2) = 2G` où `G` est la constante de Catalan, fournit un point de contrôle. L'accord numérique de plusieurs méthodes est utile, mais leur indépendance et la provenance de la référence doivent être examinées.

Le [sunrise à masses égales en deux dimensions](Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb) partage l'ancrage `I(0) = J(1,1,1) ≈ 2,343907…`. Faire varier l'invariant cinématique révèle cependant une structure supplémentaire. [Intégrales-04](Integrales/Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb) fait apparaître une courbe elliptique, calcule ses périodes et les compare à des intégrales elliptiques complètes. Le rapport des périodes varie avec la cinématique ; une valeur spéciale ne décrit donc pas toute la famille. Les expressions plus générales de la littérature sont distinguées des calculs effectivement reproduits.

La [bulle d'Intégrales-03](Integrales/Integrales-03-Bulle-Premiere-Divergence-Python.ipynb) ouvre une autre difficulté : l'intégrale diverge dans l'ultraviolet. La mesure angulaire fixe la normalisation ; on sépare le terme divergent, la partie finie et la dépendance à l'échelle de soustraction. Dans la convention du carnet, coefficient logarithmique et constante finie valent `π²`. Changer de prescription peut modifier une partie finie : annoncer le nombre sans la convention ferait perdre son sens physique.

Les contre-tests sont aussi instructifs que les accords. Le carnet sur la bulle distingue un artefact de quadrature localisé d'un véritable terme décroissant avec la coupure. Celui sur le sunrise teste puis rejette des hypothèses de forme fermée ou asymptotique ; il diagnostique aussi un facteur deux dans une représentation hyperbolique. Les exercices invitent à modifier un paramètre, anticiper une limite et confronter plusieurs représentations du même objet.

### Principes physiques : préciser la portée d'un exemple

[Constructeur-01](Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb) reformule certaines lois en termes de tâches possibles ou impossibles. Conservation et non-clonage deviennent des contraintes sur les transformations réalisables. Le modèle de médiateur quantique illustre une production d'intrication, mesurée par une négativité de `0,5`, là où le témoin classique du carnet donne zéro. Il s'agit d'un exemple calculable de non-classicité, pas d'une expérience de gravité.

[Chaînes-01](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) étudie une proposition informationnelle récente de Wissner-Gross. Il reproduit une énumération et examine la valeur candidate obtenue pour la constante de structure fine. Retrouver le calcul de la source permet d'en contrôler l'exécution ; cela ne valide pas l'axiome physique de départ ni les conjectures qui relient les objets combinatoires aux particules. La distinction **Mesuré / Cité / Ouvert** accompagne cette lecture d'une prépublication non relue.

## Activités transversales — approfondir un contrôle

| Travail proposé | Carnets d'appui | Question à traiter dans le compte rendu |
|---|---|---|
| Rompre une hypothèse | Jauge-01 : isotropie puis anisotropie. | Quelle conservation disparaît et quel contrôle permet de l'observer ? |
| Raffiner une discrétisation | Numérique-01 : maillage et flux de Burgers. | L'erreur diminue-t-elle comme attendu et quelle propriété reste à démontrer ? |
| Construire une référence indépendante | Intégrales-01/02 : quadrature, valeur spéciale et limite. | Les deux calculs pourraient-ils partager la même erreur de normalisation ? |
| Séparer signal et artefact | Intégrales-03 : coupure et quadrature. | Comment distinguer une erreur numérique d'un terme physique ou d'une convention ? |
| Délimiter une conclusion | Constructeur-01 ou Chaînes-01. | Qu'est-ce qui est calculé ici, supposé par le modèle ou seulement repris d'une source ? |

Les exercices des carnets servent de point de départ à ces comparaisons. Conserver les hypothèses, paramètres, références et sorties dans le compte rendu permet à un autre lecteur de comprendre ce qui a été testé.

## Installation — pratique, tous niveaux

Les carnets présents utilisent Python et disposent de sorties consultables. NumPy et Matplotlib suffisent au premier parcours de Burgers ; les autres branches utilisent aussi SciPy, SymPy ou mpmath. Ces dépendances doivent être installées dans l'environnement du noyau Jupyter.

Depuis la racine du dépôt :

```bash
python -m venv .venv-physique
source .venv-physique/bin/activate
python -m pip install jupyterlab ipykernel numpy scipy sympy matplotlib mpmath
python -m ipykernel install --user --name coursia-physique --display-name "Python — Physique"
jupyter lab MyIA.AI.Notebooks/Physique/Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb
```

Sous Windows, activer l'environnement avec `.\.venv-physique\Scripts\Activate.ps1`. Sélectionner le noyau « Python — Physique », puis exécuter les cellules dans l'ordre. Les [commandes communes](../../docs/reference/common-commands.md) complètent l'aide à l'environnement.

Les calculs de haute précision et les simulations Monte Carlo peuvent demander plus de temps que les exemples symboliques. Pour reproduire une expérience, conserver la précision numérique, les graines, les paramètres du réseau ou du maillage et les réglages d'échantillonnage. Les références analytiques doivent être retrouvées à la tolérance du protocole ; les sorties stochastiques ne sont pas promises identiques bit à bit.

## Pour aller plus loin — Recherche

### Du contrôle numérique à la preuve

Une égalité simplifiée par SymPy, une borne démontrée dans le texte et une erreur mesurée sur quelques maillages ont des portées différentes. On peut approfondir chaque carnet en dressant la liste des hypothèses, des étapes démontrées et des propriétés seulement testées. Le raffinement du maillage, la variation de précision et les contre-exemples peuvent réfuter une implémentation ou révéler un oubli ; ils ne remplacent pas une preuve générale de convergence.

Les références des sous-séries conduisent à Noether et aux théories de jauge, aux méthodes de volumes finis, aux intégrales de Feynman et à leurs fonctions spéciales. Dans Intégrales, la structure elliptique ouvre vers les méthodes analytiques du sunrise ; dans Jauge, le passage réseau-continu demande de traiter les limites de volume, de pas et d'échantillonnage séparément.

### Fonctions de Green et probabilités

Le carnet [Marches — retour de Pólya et intégrales de Watson](../Probas/Applications/Marches-01-Retour-Polya-Watson-Python.ipynb), dans [Probas/Applications](../Probas/Applications/README.md), offre un pont précis vers les fonctions de Green et les intégrales associées aux marches sur réseau. Comparer les objets, leurs singularités et leurs représentations aide à reconnaître une structure mathématique commune sans confondre les modèles physiques et probabilistes.

### Lire les propositions de fondements avec leurs hypothèses

Les branches [Constructeur](Constructeur/README.md) et [Chaînes](Chaines/README.md) permettent un travail de lecture critique : reconstruire une implication, identifier ses hypothèses et chercher un contre-témoin. Les bibliographies locales distinguent les textes fondateurs, les résultats repris et les questions encore ouvertes. Un accord avec une constante connue doit être examiné avec la construction qui l'a produit et les choix qu'elle laisse libres.

## Ressources — tous niveaux

- [Numérique](Numerique/README.md) : équations de conservation, problème de Riemann, schémas et exercices.
- [Jauge](Jauge/README.md) : Noether, symétries locales et références pour le calcul sur réseau.
- [Intégrales](Integrales/README.md) : normalisations, fonctions spéciales et bibliographie des amplitudes étudiées.
- [Constructeur](Constructeur/README.md) : textes sur les tâches possibles et impossibles en physique.
- [Chaînes](Chaines/README.md) : source étudiée, reproduction et statut des propositions.
- [Information quantique](InformationQuantique/README.md) : états mixtes, intrication, témoins et canaux, calculés sur des matrices.

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md) · [Licence](../../LICENSE)
