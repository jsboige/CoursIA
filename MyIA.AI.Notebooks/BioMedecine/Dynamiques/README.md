# Dynamiques — trois modèles du vivant, trois contrôles qui savent échouer

[↑ Bio & Médecine](../README.md)

Une équation différentielle en biologie ne se juge pas à l'allure de sa courbe. Une trajectoire qui « ressemble » à un cycle peut violer la structure qui la gouverne ; une épidémie qui s'éteint peut s'éteindre pour la mauvaise raison. Cette sous-série prend trois modèles classiques du vivant et leur donne à chacun un juge extérieur : une solution exacte, une quantité conservée, une équation résolue sans intégrer le système. Puis elle construit un cas où ce juge doit échouer, pour montrer qu'il sait le faire.

Les deux premières feuilles suivent ce programme sur deux terrains différents. Dynamiques-01 travaille en population homogène, où le mélange est parfait ; Dynamiques-02 abandonne cette hypothèse et fait courir l'épidémie sur un graphe de contacts, dont la forme décide à quelle valeur bascule la flambée.

Les carnets s'adressent à un étudiant de licence qui connaît Python et les équations différentielles ordinaires. Aucune connaissance préalable de la dynamique des populations n'est supposée : chaque modèle est introduit, avec ses hypothèses et ce qu'elles laissent de côté.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Dynamiques-01. Trois modèles, trois contrôles, trois contre-témoins, dans l'ordre du carnet.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque section mesure et ce qu'elle laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les extensions prévues de la sous-série et les questions qu'elles ouvrent.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Dynamiques-01 — Populations et épidémies : trois modèles, trois contrôles indépendants](Dynamiques-01-Populations-et-Epidemies-Python.ipynb) | La croissance logistique et sa solution exacte, retrouvée à `6,3e-08` près sur 400 points. Le système proie-prédateur de Lotka-Volterra et son intégrale première $H = \delta x - \gamma \ln x + \beta y - \alpha \ln y$, maintenue à `1,66e-10` en relatif. Le SIR, son seuil $R_0 = 2{,}5$, son pic à `233 487` infectieux (23,35 % de la population) au jour 56, et sa taille finale `892 646`, obtenue deux fois par des voies indépendantes à `0,2` personne près. L'ordre de convergence d'Euler explicite, mesuré par régression log-log entre `0,94` et `0,98`. | Licence : Python, équations différentielles ordinaires. Outils : numpy, scipy, matplotlib. | Les trois exercices, puis Dynamiques-02 et les extensions de la sous-série (voir « Pour aller plus loin »). |
| 02 | [Dynamiques-02 — Épidémies sur réseau : le seuil que les degrés décident](Dynamiques-02-Epidemies-sur-Reseau-Python.ipynb) | Un SIR sur graphe de contacts, simulé par une file d'événements et jugé par la percolation statique (union-find). Les deux voies s'accordent à `0,025` près quand chaque arête transmet indépendamment, et divergent de `0,135` quand une horloge de guérison partagée corrèle les arêtes d'un même sujet. Le contre-témoin : un anneau triangulé où la formule de seuil annonce une flambée à `0,3333` alors que `2,7 %` de la population bascule à $T = 0{,}60$, contre `88,4 %` sur un réseau aléatoire de même degré moyen. | Licence : Python, probabilités élémentaires. Outils : numpy et la bibliothèque standard (`heapq`). | Les trois exercices (bimodalité au seuil, seuils par dichotomie, réparation de l'anneau), puis les extensions de la sous-série. |

Deux carnets. Les feuilles suivantes — simulation stochastique de Gillespie comparée à l'équation déterministe, inférence des paramètres — viendront s'ajouter ici.

## Approfondissements — Licence avancée

### Autour de 01 : trois contrôles, trois natures

Le carnet ne répète pas trois fois le même contrôle. Il en emploie trois de natures différentes, et c'est cette variété qui fait sa valeur pédagogique.

**Une solution exacte.** La logistique $dN/dt = rN(1-N/K)$ s'intègre à la main. Sa forme close sert de juge à un intégrateur adaptatif, réglé à `rtol = 1e-10`. L'écart maximal mesuré porte donc sur l'intégrateur, pas sur le modèle.

**Une quantité conservée.** Lotka-Volterra n'a pas de solution élémentaire, mais il possède une intégrale première : $H$ est constant le long des trajectoires exactes. Un intégrateur qui respecte la structure maintient $H$ ; celui qui la viole dérive, même s'il dessine une boucle plausible. Le carnet mesure `1,66e-10` de dérive relative pour l'intégrateur adaptatif.

**Une équation sans intégration.** La taille finale d'une épidémie SIR vérifie $S_\infty = S_0 \exp(-R_0 (N - S_\infty)/N)$. Cette équation transcendante se résout par dichotomie, sans jamais toucher au système différentiel. La comparaison porte donc sur deux calculs qui ne partagent ni code, ni méthode, ni erreur d'arrondi.

### Autour de 01 : les contre-témoins, et ce qu'ils attrapent

Un contrôle qui ne sait pas échouer ne prouve rien. Le carnet construit trois cas d'échec.

- **Euler explicite contre la logistique.** L'erreur décroît comme le pas : `22,96` pour `h = 2`, `11,74` pour `h = 1`, `6,12` pour `h = 0,5`, `3,10` pour `h = 0,25`. Le rapport des erreurs successives vaut entre `1,92` et `1,98` quand le pas est divisé par deux — l'ordre un du schéma est mesuré, pas supposé.
- **Euler explicite contre l'invariant de Lotka-Volterra.** Avec un pas de `0,5`, la trajectoire sort du domaine positif au 31e pas : un effectif négatif n'a aucun sens biologique et rend $H$ indéfinie. Avec un pas de `0,1`, elle reste dans le domaine mais la dérive relative de $H$ atteint `1,5e+01`, soit 1 500 %. Aux pas de `0,02` et `0,004`, elle retombe à `9,8e-01` puis `1,6e-01`. L'erreur suit la discrétisation, elle n'est pas une faute de calcul.
- **Le seuil épidémique.** Sous $R_0 = 1$, l'infectieux ne monte jamais. La taille finale n'est pourtant pas nulle : `25` personnes pour $R_0 = 0{,}6$ et `98,6` pour $R_0 = 0{,}9$, sur un million d'habitants. Ces valeurs sont celles que prédit $I_0/(1-R_0)$ — les dix cas initiaux guérissent, mais chacun a contaminé avant de guérir. Un modèle qui annoncerait une flambée sous le seuil serait réfuté par cette seule cellule.

### Autour de 02 : deux voies indépendantes, et l'écart qui reste

Le second carnet ne compare pas un modèle à sa solution exacte : il compare un simulateur à un autre calcul du même objet. D'un côté une file de priorité qui ordonne des dates de guérison et de transmission ; de l'autre un union-find qui fusionne des composantes dans un graphe où chaque arête a été gardée avec la probabilité $T$. Rien de commun entre les deux codes, sinon la définition mathématique de l'épidémie.

L'accord n'est pourtant pas total, et c'est le résultat intéressant. Quand chaque arête transmet indépendamment, les deux voies se suivent à `0,025` près. Quand les transmissions d'un même sujet partagent son horloge de guérison — le modèle SIR physique — la simulation reste en dessous, de `0,135` au plus. Le même simulateur, privé de l'horloge partagée, referme l'écart : c'est la corrélation entre les arêtes d'un sujet, et non un défaut de code, qui produit la différence. Un $R_0$ de percolation est donc une borne supérieure de ce que donnera un SIR à durée infectieuse tirée.

Le contre-témoin du carnet porte sur la formule de seuil, pas sur le code. Un anneau 4-régulier, où chaque arête appartient à un triangle, garde exactement les moments de degrés qui fondent la formule — et ne flambe pas au seuil annoncé. La mesure chiffre le mécanisme par la loi $n(1-T)^3$ des points de coupe, et montre qu'à $T = 0{,}90$ la taille finie du réseau suffit à faire réapparaître un grand amas : l'absence de transition ne se voit qu'à la limite thermodynamique.

### Ce que les carnets n'établissent pas

Les trois modèles sont déterministes, à population homogène et mélange parfait. Le carnet ne dit rien de la stochasticité des petites populations, de l'hétérogénéité des contacts, ni de la structure d'âge. Il ne dit rien non plus de la validité biologique des paramètres : $R_0 = 2{,}5$ et une durée infectieuse de sept jours sont des choix illustratifs, pas des estimations.

Dynamiques-02 n'établit rien de plus sur les données réelles : son graphe est un modèle de configuration à degrés indépendants, sans structure de communauté, sans distances géographiques et sans corrélation de degrés. Il ne dit pas non plus quelle horloge décrit une infection réelle — le carnet mesure l'écart entre deux choix, il ne tranche pas lequel est le bon.

Les exercices ouvrent trois pistes dans chaque feuille. Pour Dynamiques-01 : le schéma du point milieu face à Euler, l'ordre auquel Euler conserve l'invariant de Lotka-Volterra sur une grille fine, et la position du pic infectieux comparée à $N/R_0$. Pour Dynamiques-02 : la bimodalité des tailles finales au voisinage du seuil, le seuil mesuré par dichotomie à deux degrés moyens, et la réparation de l'anneau par des arêtes lointaines.

## Installation — pratique, tous niveaux

Les deux carnets tournent sur le noyau `python3`, sans GPU. Dynamiques-01 est déterministe sans graine ; Dynamiques-02 fixe ses graines et rejoue donc ses nombres à l'identique, d'une exécution à l'autre.

```bash
python -m pip install jupyterlab ipykernel numpy scipy matplotlib
jupyter lab MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb
jupyter lab MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-02-Epidemies-sur-Reseau-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** La simulation stochastique de Gillespie, dont la moyenne doit retrouver l'équation déterministe quand le volume croît. L'inférence des paramètres d'un modèle mécaniste, avec l'inférence bayésienne de [Probas/PyMC](../../Probas/PyMC/README.md).

**Questions ouvertes.** À quel volume la moyenne de Gillespie se confond-elle avec la solution déterministe, et à quel volume en diverge-t-elle qualitativement ? Quelle expression donne la taille finale d'un SIR dont les transmissions partagent une horloge, là où la percolation n'en donne qu'une borne ? Que devient le seuil quand les degrés sont corrélés, comme dans un réseau social réel ?

**Ponts.** [Physique/Numerique](../../Physique/Numerique/README.md) mesure ce qu'un schéma fait à une équation de conservation ; les mêmes questions d'ordre et de stabilité reviennent ici. [GameTheory/Dynamics](../../GameTheory/Dynamics/README.md) porte la dynamique des réplicateurs, qui est la mécanique de sélection de l'évolution. [Search](../../Search/README.md) fournit les parcours sur graphe dont Dynamiques-02 emploie une variante minimale.

## Ressources — tous niveaux

- Modèles et contrôles : croissance logistique, Lotka-Volterra, SIR homogène (Dynamiques-01) ; SIR sur graphe de contacts et percolation de liens (Dynamiques-02). Aucune donnée externe ; toutes les valeurs sont simulées à paramètres connus.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
