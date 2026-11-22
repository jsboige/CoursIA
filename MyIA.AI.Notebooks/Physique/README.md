---
pagetitle: "Physique — des modèles aux calculs vérifiables"
---

[↑ Parcours de notebooks](../README.md)

Comment savoir si un calcul physique représente bien le phénomène annoncé ? Cette famille part de lois de conservation, de symétries, d'intégrales de Feynman et d'états quantiques pour construire des calculs dont on peut examiner les hypothèses, les références et les limites. Une solution analytique, une identité symbolique, une simulation et la reproduction d'un résultat publié apportent des contrôles différents : apprendre à les distinguer fait partie du cours.

Le parcours s'adresse aux étudiants en physique, mathématiques appliquées et informatique scientifique, ainsi qu'aux enseignants qui cherchent des expériences calculables. Python et les bases du calcul différentiel suffisent pour la branche numérique ; les autres portes indiquent leurs prérequis propres. Vous apprendrez à passer d'une équation à une discrétisation, à relier symétrie et conservation, à comparer des voies de calcul indépendantes et à dire précisément ce qu'un résultat établit.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue entrée dans le sujet, approfondissements et recherche.

- **Vous découvrez** : choisissez une question dans la table du parcours principal. Numérique offre une première expérience concrète : une équation, un choc et des schémas à comparer.
- **Vous approfondissez** : la section « Sous-séries » dit ce que contient chaque dossier, et « Approfondissements » relie les branches entre elles. Jauge et Intégrales se suivent dans l'ordre de leurs numéros ; Information quantique s'ouvre à qui connaît l'algèbre linéaire.
- **Vous explorez des fondements** : Constructeur et Chaînes interrogent la formulation des lois et le statut de leurs conséquences. Leur lecture demande de séparer modèle illustratif, résultat démontré et conjecture.

Aucune séquence n'est imposée entre les branches. Les numéros des carnets décrivent une progression à l'intérieur de chaque sous-série ; les README locaux portent les tables complètes et les exercices.

## Parcours principal — choisir une question, de la Licence à la Recherche

| Question | Sous-série et premier carnet | Ce qu'on y apprend | Prérequis et public | Pour approfondir |
|---|---|---|---|---|
| Comment une loi de conservation produit-elle un choc ? | [Numérique](Numerique/README.md) → [Burgers et volumes finis](Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb) | Caractéristiques, solutions faibles, vitesse de choc, flux de Godunov et de Rusanov, ordre de convergence mesuré. | Licence : Python, dérivées partielles et intégration. | [Numérique-02](Numerique/Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb) : mesurer un solveur C dont les équations sont prouvées ailleurs. |
| Que permet de déduire une symétrie ? | [Jauge](Jauge/README.md) → [Théorème de Noether](Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) | Conservation, covariance locale U(1) et SU(2), variables de lien, plaquettes et boucles de Wilson. | Licence avancée puis Master : mécanique lagrangienne, nombres complexes et matrices. | Du calcul symbolique au Monte Carlo sur réseau, puis aux spineurs de [Jauge-04](Jauge/Jauge-04-Points-Spineurs-Twisteurs-Python.ipynb). |
| Comment calculer et contrôler une intégrale de Feynman ? | [Intégrales](Integrales/README.md) → [Triangle scalaire](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) | Représentations paramétriques, quadratures de haute précision, valeurs spéciales, divergence ultraviolette et structure elliptique. | Licence avancée puis Master : intégrales multiples ; la première amplitude est construite dans le carnet. | Relier le sunrise à sa courbe elliptique et à ses périodes. |
| Comment tester l'intrication d'un état mixte par le calcul ? | [Information quantique](InformationQuantique/README.md) → [Werner, PPT, distillabilité](InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) | États mixtes et purification, critère PPT, seuils de distillabilité des états de Werner, canaux à rupture d'intrication. Chaque seuil cité est recalculé sur des matrices explicites. | Licence avancée et Master : algèbre linéaire, numpy. | [InfoQuant-02](InformationQuantique/InfoQuant-02-Trois-Copies-Werner-Distillabilite-Python.ipynb) : la question trois-copies du trou de distillabilité, face à un préprint 2026. |
| Peut-on formuler une loi comme une tâche impossible ? | [Constructeur](Constructeur/README.md) → [Les lois comme tâches](Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb) | Tâches, constructeurs, conservation, non-clonage et témoin de non-classicité dans un modèle jouet. | Licence : Python de base ; notions de qubit pour la dernière partie. | Discuter ce que l'exemple de médiateur permet d'inférer. |
| Comment examiner un programme physique fondé sur un axiome informationnel ? | [Chaînes](Chaines/README.md) → [Intrication et constante de structure fine](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) | Rejouer une énumération, examiner une valeur candidate et distinguer résultats mesurés, cités et ouverts. | Recherche : algèbre linéaire, notions d'intrication, lecture critique d'une prépublication. | Suivre la source chapitre par chapitre, jusqu'à ses résultats ouverts. |

## Sous-séries — ce que contient chaque dossier

### Numérique — Licence

[Numérique](Numerique/README.md) mesure ce qu'un solveur fait réellement. [Numérique-01](Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb) traite l'équation de Burgers : formation du choc, condition de Rankine-Hugoniot, schémas de Godunov et de Rusanov comparés à la solution exacte, ordre de convergence mesuré par régression. [Numérique-02](Numerique/Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb) compile un fichier C d'un dépôt amont, pris à une empreinte épinglée, et en mesure la conservation, la vitesse de propagation et l'ordre. Chaque carnet sépare par écrit ce qui est mesuré, ce qui est rapporté et ce qui demanderait une preuve.

### Jauge — Licence avancée et Master

[Jauge](Jauge/README.md) suit un arc : une symétrie continue donne une quantité conservée ([Jauge-01](Jauge/Jauge-01-Theoreme-Noether-Python.ipynb)), rendue locale elle impose un champ de jauge ([Jauge-02](Jauge/Jauge-02-Invariance-Jauge-U1-SU2-Python.ipynb)), et posé sur un réseau ce champ devient calculable ([Jauge-03](Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb)). [Jauge-04](Jauge/Jauge-04-Points-Spineurs-Twisteurs-Python.ipynb) ouvre un contrepoint géométrique : SU(2) comme double revêtement des rotations, et la relation d'incidence des twisteurs. Chaque identité est établie symboliquement, contrôlée numériquement contre un seuil annoncé, puis confrontée à un contre-témoin construit pour échouer.

### Intégrales — Licence avancée et Master

[Intégrales](Integrales/README.md) calcule des intégrales à boucles en haute précision : le [triangle scalaire](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb), le [sunrise à masses égales](Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb), la [bulle](Integrales/Integrales-03-Bulle-Premiere-Divergence-Python.ipynb), première intégrale qui diverge, puis la [courbe elliptique du sunrise](Integrales/Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb). La sous-série pratique trois règles : valider un outil contre une valeur connue avant de s'en servir, ne chercher une constante que dans un ensemble déclaré à l'avance, exiger d'un contrôle qu'il sache échouer.

### Information quantique — Licence avancée et Master

[Information quantique](InformationQuantique/README.md) s'ouvre avec [InfoQuant-01](InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb). Le carnet construit les objets de l'intrication des états mixtes avec numpy seul : purification, décomposition de Schmidt, états de Werner, transposition partielle, témoins de distillabilité, matrice de Choi d'un canal. Chaque seuil est retrouvé numériquement avant d'être comparé à sa source, et les questions ouvertes rencontrées en chemin sont nommées. [InfoQuant-02](InformationQuantique/InfoQuant-02-Trois-Copies-Werner-Distillabilite-Python.ipynb) prend l'une d'elles — des Werner NPT que rien ne distille à une copie — et la confronte à trois copies : le critère y devient une forme matricielle calculable, dont le carnet vérifie le minimiseur exact d'un préprint 2026 et mesure la frontière que des milliers de tirages ne franchissent pas.

### Constructeur — Licence

[Constructeur](Constructeur/README.md) est la sous-série conceptuelle. [Constructeur-01](Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb) présente la théorie du constructeur, qui énonce les lois comme des tâches possibles ou impossibles : la conservation de l'énergie devient l'impossibilité d'un moteur perpétuel, l'information se définit par ce que son support permet de copier. Le carnet se termine par un témoin de non-classicité simulé sur deux qubits.

### Chaînes — Recherche

[Chaînes](Chaines/README.md) lit un programme récent de physique de l'information, la Chain Theory de Wissner-Gross, une prépublication non relue. Chaque carnet applique le même patron. Ce que le carnet rejoue lui-même est **mesuré**, ce qu'il reprend de la source est **cité**, et ce que la source ne prouve pas est listé comme **ouvert**. [Chaînes-01](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) rejoue l'énumération qui mène à une valeur candidate de la constante de structure fine. Les carnets suivants prennent la source chapitre par chapitre : règle de Born et unitarité, mesure, indiscernabilité, énergie, intégrale de chemin, fonction de Wigner, corollaires de mécanique quantique, puis coordonnée d'ordre et groupe des rotations. Les énoncés principaux y sont le plus souvent des théorèmes conditionnels ; avec l'intégrale de chemin, la sous-série rencontre son premier objet que la source déclare ouvert.

## Approfondissements — Licence avancée et Master

Cette section relie les branches. Les approfondissements propres à chaque sous-série sont dans son README.

### Conservation : de l'identité continue au calcul discret

[Jauge-01](Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) étudie un oscillateur isotrope dans le plan. L'invariance par rotation conduit à la conservation du moment angulaire ; une anisotropie fournit un contre-exemple qui montre le rôle de cette hypothèse. Le calcul symbolique et la trajectoire numérique répondent à deux questions complémentaires : quelle identité suit du modèle, et avec quelle précision l'intégrateur la respecte-t-il ?

[Numérique-01](Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb) part de l'équation de Burgers sous forme conservative. Lorsque les caractéristiques se croisent, la solution classique laisse place à une solution faible avec un choc. La condition de Rankine-Hugoniot fixe sa vitesse : pour un état gauche égal à 1 et un état droit nul, elle vaut 0,5. Les flux de Godunov et de Rusanov sont alors comparés à cette référence.

À résolution finie, un choc numérique est étalé : cette diffusion ne suffit pas à déclarer le schéma incorrect. On examine la position du choc, l'erreur en norme L1, le pas de temps sous condition CFL et le comportement quand le maillage est raffiné. Le carnet distingue les propriétés démontrées des contrôles empiriques du code.

### Jauge locale : préserver la structure en changeant de représentation

Dans [Jauge-02](Jauge/Jauge-02-Invariance-Jauge-U1-SU2-Python.ipynb), une phase qui dépend de la position fait apparaître un terme supplémentaire dans la dérivée ordinaire. Le champ de jauge permet de construire une dérivée covariante. Le passage à SU(2) introduit des matrices qui ne commutent pas et un terme d'auto-interaction. Les contrôles confrontent les identités attendues à des exemples numériques et à un contre-témoin abélien.

[Jauge-03](Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb) remplace les champs continus par des transports sur les arêtes d'un réseau. Les produits autour d'une plaquette donnent des observables invariantes de jauge, et les boucles de Wilson rendent la loi d'aire accessible au calcul. Le banc étudié est celui de U(1) compact. En dimension 2, une référence exacte contrôle la simulation : pour β = 0,6, la tension mesurée vaut 1,2499, contre 1,2474 pour la référence.

Cet accord étalonne le Monte Carlo. Il ne démontre ni le confinement d'une théorie non abélienne continue, ni la position d'une transition de phase. En dimension 4, le carnet observe un changement de comportement, sans le localiser.

### Intégrales : comparer les voies de calcul avant d'interpréter les nombres

[Intégrales-01](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) construit le triangle scalaire et compare plusieurs voies de quadrature. Pour la famille isocèle, une expression en fonctions de Clausen fournit un contrôle supplémentaire, avec une valeur spéciale : J(1,1,2) = 2G, où G est la constante de Catalan. L'accord de plusieurs méthodes est utile, mais leur indépendance doit être examinée : les voies du carnet partagent la même paramétrisation.

Le [sunrise](Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb) partage l'ancrage I(0) = J(1,1,1) ≈ 2,343907. Faire varier le moment révèle une structure supplémentaire. [Intégrales-04](Integrales/Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb) fait apparaître une courbe elliptique, mesure ses périodes et les compare à des intégrales elliptiques complètes. Le rapport des périodes varie avec le moment : une valeur spéciale ne décrit pas toute la famille.

La [bulle](Integrales/Integrales-03-Bulle-Premiere-Divergence-Python.ipynb) ouvre une autre difficulté : l'intégrale diverge dans l'ultraviolet. On sépare le terme divergent, la partie finie et la dépendance à l'échelle de soustraction. Dans la convention du carnet, le coefficient du logarithme et la constante finie valent π². Changer de prescription modifie la partie finie : annoncer le nombre sans la convention lui ferait perdre son sens.

Les contre-tests instruisent autant que les accords. Le carnet sur la bulle distingue un artefact de quadrature d'un véritable terme qui décroît avec la coupure. Celui sur le sunrise teste puis refuse deux hypothèses de forme fermée, et attrape un facteur 2 dans une représentation hyperbolique. Les exercices invitent à modifier un paramètre, à anticiper une limite et à confronter plusieurs représentations du même objet.

### Intrication : un mot, deux objets, un témoin

Trois sous-séries emploient le mot « intrication ». [InfoQuant-01](InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) lui donne son sens habituel : un état composé qui ne s'écrit pas comme un mélange de produits. [Chaînes-01](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) l'emploie pour la structure d'une paire dans un axiome combinatoire. InfoQuant-01 commence par un tableau qui sépare les deux emplois. [Constructeur-01](Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb), enfin, se sert d'une mesure d'intrication comme d'un témoin : la négativité vaut 0,5 quand le médiateur est quantique, et zéro quand il est classique. C'est un exemple calculable de non-classicité, pas une expérience de gravité.

### Preuve et code : ce qu'un énoncé formel couvre

Numérique-02 et Jauge-03 rencontrent chacun un énoncé prouvé en Lean, et disent ce que la preuve ne couvre pas. [Numérique-02](Numerique/Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb) compile du C dont le dépôt amont prouve les équations : aucune déclaration ne rattache les théorèmes au code compilé, et c'est donc le carnet qui mesure la conservation et l'ordre. La section 8 de [Jauge-03](Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb) présente un énoncé formel d'existence pour Yang–Mills en dimension 4, en recalcule la partie calculable et rappelle ce que la source laisse hors périmètre : ce n'est pas le problème de l'écart de masse.

### Lire une source de fondements : le cas de Chaînes

[Chaînes-01](Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) rejoue une énumération et examine la valeur candidate obtenue pour la constante de structure fine. Retrouver le calcul de la source contrôle son exécution. Cela ne valide ni l'axiome de départ, ni les conjectures qui relient les objets combinatoires aux particules. Les carnets suivants gardent la même réserve : un nom de la mécanique quantique rattaché à un objet de la source reste un théorème conditionnel, et les prémisses ouvertes sont listées une à une.

### Activités transversales

| Travail proposé | Carnets d'appui | Question à traiter dans le compte rendu |
|---|---|---|
| Rompre une hypothèse | Jauge-01 : isotropie puis anisotropie. | Quelle conservation disparaît, et quel contrôle permet de l'observer ? |
| Raffiner une discrétisation | Numérique-01 : maillage et flux de Burgers. | L'erreur diminue-t-elle comme attendu, et quelle propriété reste à démontrer ? |
| Construire une référence indépendante | Intégrales-01 et 02 : quadrature, valeur spéciale et limite. | Les deux calculs pourraient-ils partager la même erreur de normalisation ? |
| Séparer signal et artefact | Intégrales-03 : coupure et quadrature. | Comment distinguer une erreur numérique d'un terme physique ou d'une convention ? |
| Délimiter une conclusion | Constructeur-01 ou Chaînes-01. | Qu'est-ce qui est calculé ici, supposé par le modèle ou seulement repris d'une source ? |
| Mesurer ce qu'une preuve ne couvre pas | Numérique-02. | Quelle déclaration relierait les théorèmes au code, et que mesure-t-on en son absence ? |

Les exercices des carnets servent de point de départ à ces comparaisons. Conserver les hypothèses, les paramètres, les références et les sorties dans le compte rendu permet à un autre lecteur de comprendre ce qui a été testé.

## Installation — pratique, tous niveaux

Tous les carnets tournent sur le noyau `python3`, sans GPU, et sont livrés avec leurs sorties. NumPy et Matplotlib suffisent pour Numérique-01. Les autres branches ajoutent SciPy, SymPy, mpmath ou pandas. Plusieurs carnets de Chaînes n'utilisent que la bibliothèque standard.

Depuis la racine du dépôt :

```bash
python -m venv .venv-physique
source .venv-physique/bin/activate
python -m pip install jupyterlab ipykernel numpy scipy sympy matplotlib mpmath pandas
python -m ipykernel install --user --name coursia-physique --display-name "Python — Physique"
jupyter lab MyIA.AI.Notebooks/Physique/Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb
```

Sous Windows, activer l'environnement avec `.\.venv-physique\Scripts\Activate.ps1`. Sélectionner le noyau « Python — Physique », puis exécuter les cellules dans l'ordre. Les [commandes communes](../../docs/reference/common-commands.md) complètent l'aide à l'environnement.

Certains carnets demandent davantage :

- **Jauge-04** utilise PyTorch : `python -m pip install torch`. Aucun GPU n'est requis.
- **Numérique-02** demande un compilateur C (`cc`, `gcc` ou `clang`, ou `gcc` dans WSL sur un poste Windows) et un accès réseau pour télécharger le fichier amont. Sans compilateur, il s'arrête sur une erreur explicite.

Les calculs de haute précision et les simulations Monte Carlo demandent plus de temps que les exemples symboliques. Pour reproduire une expérience, conserver la précision numérique, les graines, les paramètres du réseau ou du maillage. Les références analytiques doivent être retrouvées à la tolérance du protocole ; les sorties stochastiques ne sont pas promises identiques bit à bit.

## Pour aller plus loin — Recherche

### Du contrôle numérique à la preuve

Une égalité simplifiée par SymPy, une borne démontrée dans le texte et une erreur mesurée sur quelques maillages n'ont pas la même portée. On peut approfondir chaque carnet en dressant la liste des hypothèses, des étapes démontrées et des propriétés seulement testées. Le raffinement du maillage, la variation de précision et les contre-exemples peuvent réfuter une implémentation ou révéler un oubli ; ils ne remplacent pas une preuve générale de convergence. Numérique-01 nomme trois questions ouvertes sur la preuve de correction d'un schéma, et [un document de méthode](../../docs/reference/gorard-lanyonai-etape3.md) précise ce que les preuves du dépôt amont de Numérique-02 établissent.

Les références des sous-séries conduisent à Noether et aux théories de jauge, aux méthodes de volumes finis, aux intégrales de Feynman et à leurs fonctions spéciales. Dans Intégrales, la structure elliptique ouvre vers les méthodes analytiques du sunrise ; dans Jauge, le passage du réseau au continu demande de traiter séparément les limites de volume, de pas et d'échantillonnage.

### Formalisations Lean

Les carnets de cette famille sont en Python ; les énoncés formels vivent ailleurs dans le dépôt. La violation d'une inégalité de Bell est le témoin opérationnel de l'intrication : sa borne quantique, celle de Tsirelson, est prouvée dans [Lean-13b](../SymbolicAI/Lean/Lean-13b-CHSH-Tsirelson-Native.ipynb), et sa saturation dans [Lean-13c](../SymbolicAI/Lean/Lean-13c-CHSH-Landau-Saturation.ipynb). Les polynômes de Jones que Jauge-03 tire d'une R-matrice sont recalculés par une voie indépendante dans [KNOTS-02](../SymbolicAI/Lean/KNOTS/KNOTS-02-Invariants-Python.ipynb). L'énoncé d'existence Yang–Mills cité par Jauge-03 a sa [cartographie sourcée](../../docs/research/yang-mills-openai-20261028-analyse.md), qui dit ce qui y est prouvé et ce qui reste hors périmètre.

### Fonctions de Green et probabilités

Le carnet [Marches — retour de Pólya et intégrales de Watson](../Probas/Applications/Marches-01-Retour-Polya-Watson-Python.ipynb), dans [Probas/Applications](../Probas/Applications/README.md), offre un pont précis vers les fonctions de Green des marches sur réseau. Comparer les objets, leurs singularités et leurs représentations aide à reconnaître une structure mathématique commune sans confondre les modèles physiques et probabilistes.

### Géométrie et rendu

La relation d'incidence de Jauge-04 décrit des rayons de lumière. La série [GenAI/3D](../GenAI/3D/README.md) étudie des représentations de scènes où la même géométrie sert au rendu.

### Lire les propositions de fondements avec leurs hypothèses

[Constructeur](Constructeur/README.md) et [Chaînes](Chaines/README.md) permettent un travail de lecture critique : reconstruire une implication, identifier ses hypothèses et chercher un contre-témoin. Les bibliographies locales distinguent les textes fondateurs, les résultats repris et les questions encore ouvertes. Un accord avec une constante connue s'examine avec la construction qui l'a produit et les choix qu'elle laisse libres.

## Ressources — tous niveaux

- [Numérique](Numerique/README.md) : équations de conservation, problème de Riemann, schémas et exercices.
- [Jauge](Jauge/README.md) : Noether, symétries locales, calcul sur réseau, spineurs et twisteurs.
- [Intégrales](Integrales/README.md) : intégrales à boucles, fonctions spéciales et bibliographie des objets étudiés.
- [Information quantique](InformationQuantique/README.md) : états mixtes, intrication, témoins et canaux, calculés sur des matrices.
- [Constructeur](Constructeur/README.md) : textes sur les tâches possibles et impossibles en physique.
- [Chaînes](Chaines/README.md) : source étudiée, reproduction et statut des propositions.

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md) · [Licence](../../LICENSE)
