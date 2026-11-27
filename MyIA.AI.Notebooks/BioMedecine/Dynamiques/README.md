# Dynamiques — trois modèles du vivant, trois contrôles qui savent échouer

[↑ Bio & Médecine](../README.md)

Une équation différentielle en biologie ne se juge pas à l'allure de sa courbe. Une trajectoire qui « ressemble » à un cycle peut violer la structure qui la gouverne ; une épidémie qui s'éteint peut s'éteindre pour la mauvaise raison. Cette sous-série prend trois modèles classiques du vivant et leur donne à chacun un juge extérieur : une solution exacte, une quantité conservée, une équation résolue sans intégrer le système. Puis elle construit un cas où ce juge doit échouer, pour montrer qu'il sait le faire.

Le carnet s'adresse à un étudiant de licence qui connaît Python et les équations différentielles ordinaires. Aucune connaissance préalable de la dynamique des populations n'est supposée : chaque modèle est introduit, avec ses hypothèses et ce qu'elles laissent de côté.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Dynamiques-01. Trois modèles, trois contrôles, trois contre-témoins, dans l'ordre du carnet.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque section mesure et ce qu'elle laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les extensions prévues de la sous-série et les questions qu'elles ouvrent.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Dynamiques-01 — Populations et épidémies : trois modèles, trois contrôles indépendants](Dynamiques-01-Populations-et-Epidemies-Python.ipynb) | La croissance logistique et sa solution exacte, retrouvée à `6,3e-08` près sur 400 points. Le système proie-prédateur de Lotka-Volterra et son intégrale première $H = \delta x - \gamma \ln x + \beta y - \alpha \ln y$, maintenue à `1,66e-10` en relatif. Le SIR, son seuil $R_0 = 2{,}5$, son pic à `233 487` infectieux (23,35 % de la population) au jour 56, et sa taille finale `892 646`, obtenue deux fois par des voies indépendantes à `0,2` personne près. L'ordre de convergence d'Euler explicite, mesuré par régression log-log entre `0,94` et `0,98`. | Licence : Python, équations différentielles ordinaires. Outils : numpy, scipy, matplotlib. | Les trois exercices, puis les extensions de la sous-série (voir « Pour aller plus loin »). |

Un seul carnet pour l'instant. Les feuilles suivantes — épidémie sur réseau de contacts simulée par agents, simulation stochastique de Gillespie comparée à l'équation déterministe, inférence des paramètres — viendront s'ajouter ici.

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

### Ce que le carnet n'établit pas

Les trois modèles sont déterministes, à population homogène et mélange parfait. Le carnet ne dit rien de la stochasticité des petites populations, de l'hétérogénéité des contacts, ni de la structure d'âge. Il ne dit rien non plus de la validité biologique des paramètres : $R_0 = 2{,}5$ et une durée infectieuse de sept jours sont des choix illustratifs, pas des estimations.

Les exercices ouvrent trois pistes : le schéma du point milieu face à Euler, l'ordre auquel Euler conserve l'invariant de Lotka-Volterra sur une grille fine, et la position du pic infectieux comparée à $N/R_0$.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3`, sans GPU. Il est déterministe : aucune graine, chaque exécution rejoue les mêmes nombres.

```bash
python -m pip install jupyterlab ipykernel numpy scipy matplotlib
jupyter lab MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** L'épidémie sur réseau de contacts simulée par agents, contrôlée par le $R_0$ du réseau contre la simulation. La simulation stochastique de Gillespie, dont la moyenne doit retrouver l'équation déterministe quand le volume croît. L'inférence des paramètres d'un modèle mécaniste, avec l'inférence bayésienne de [Probas/PyMC](../../Probas/PyMC/README.md).

**Questions ouvertes.** À quel volume la moyenne de Gillespie se confond-elle avec la solution déterministe, et à quel volume en diverge-t-elle qualitativement ? Un $R_0$ de réseau se calcule-t-il à partir de la distribution des degrés, et à quelles conditions ?

**Ponts.** [Physique/Numerique](../../Physique/Numerique/README.md) mesure ce qu'un schéma fait à une équation de conservation ; les mêmes questions d'ordre et de stabilité reviennent ici. [GameTheory/Dynamics](../../GameTheory/Dynamics/README.md) porte la dynamique des réplicateurs, qui est la mécanique de sélection de l'évolution.

## Ressources — tous niveaux

- Modèles et contrôles : croissance logistique, Lotka-Volterra, SIR. Aucune donnée externe ; toutes les valeurs sont simulées à paramètres connus.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
