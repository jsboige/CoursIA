# Jauge — de Noether au réseau de Wilson

[↑ Physique](../README.md)

Une symétrie continue donne une quantité conservée. Rendue locale, la même symétrie impose un champ de jauge. Posé sur un réseau, ce champ devient calculable, et l'on peut y mesurer une loi d'aire. La sous-série suit cet arc en Python, du théorème de Noether à l'action de Wilson. Elle ouvre ensuite un contrepoint géométrique : le groupe SU(2) revu comme double revêtement des rotations, vers les twisteurs de Penrose.

Les carnets appliquent la même méthode. Une identité est d'abord établie symboliquement, puis contrôlée numériquement contre un seuil annoncé avant la mesure. Un contre-témoin, construit pour échouer, vérifie que le contrôle sait détecter une erreur. La sous-série s'adresse à des étudiants de licence avancée et de master qui connaissent la mécanique lagrangienne, les nombres complexes et le calcul matriciel.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : suivez le parcours principal dans l'ordre des numéros. Jauge-01 se lit sans prérequis de théorie des champs.
- **Vous creusez un palier** : la section « Approfondissements » décrit les deux prolongements de Jauge-03 et les exercices de chaque carnet.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » sépare ce que les carnets mesurent de ce qu'ils citent, et renvoie à la lecture d'un énoncé formel d'existence pour Yang–Mills.

## Parcours principal — Licence avancée et Master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Jauge-01 — Le théorème de Noether en sympy](Jauge-01-Theoreme-Noether-Python.ipynb) · [jumeau C#](Jauge-01-Theoreme-Noether-CSharp.ipynb) | Les équations d'Euler-Lagrange, dérivées puis contrôlées contre la routine de sympy. La variation du lagrangien sous une rotation (nulle) et sous une translation (non nulle). Le courant de Noether $j = m(x\dot y - y\dot x)$, de dérivée nulle symboliquement. Un contrôle numérique sur l'oscillateur isotrope : dérive relative maximale `1.6e-15`, pour un seuil de `1e-08`. Un contre-témoin anisotrope, où la dérive monte à `2.16` : la conservation disparaît avec la symétrie. | Licence avancée : mécanique lagrangienne. Outils : sympy, scipy, numpy, matplotlib. | Exercices : impulsion, potentiel central, énergie. |
| 02 | [Jauge-02 — De la symétrie globale à la jauge locale : U(1) puis SU(2)](Jauge-02-Invariance-Jauge-U1-SU2-Python.ipynb) · [jumeau C#](Jauge-02-Invariance-Jauge-U1-SU2-CSharp.ipynb) | Une phase globale laisse le lagrangien invariant. Une phase locale fait surgir un terme en $\partial\alpha$. La dérivée covariante le compense, et le tenseur $F$ reste invariant. Côté SU(2), les relations de commutation des générateurs sont vérifiées paire par paire, et le commutateur $[D_t, D_x]$ fait sortir le terme d'auto-interaction. Un contrôle numérique à hypothèse pré-enregistrée confirme l'invariance de $\mathrm{Tr}(F F^\dagger)$ : écart relatif maximal `3.92e-15`, seuil `1e-12`. Le contre-témoin applique à SU(2) la seule règle abélienne ; il est détecté (écart `8.16e-01`). Le jumeau C# rejoue le même parcours en arithmétique exacte, sur rationnels et `BigInteger` : les écarts d'invariance deviennent nuls, le contre-témoin est détecté à `1.21e-01`, et une seconde contre-épreuve, que le carnet Python documente sans l'exécuter, mesure une formule de Rodrigues fausse (écart d'unitarité `1.26e-02`, écart d'invariance `1.06e-01`). | Master : matrices de Pauli, dérivées partielles. Outils : sympy, numpy ; jumeau C# sur le noyau `.net-csharp`, sans NuGet. | Exercices : champ de Dirac, doublet scalaire, composante $F^3$. |
| 03 | [Jauge-03 — L'action de Wilson sur réseau : la boucle de Wilson et le confinement](Jauge-03-Action-Wilson-Confinement-Python.ipynb) · [jumeau C#](Jauge-03-Action-Wilson-Confinement-CSharp.ipynb) | Le lien comme transport parallèle discret, la plaquette et sa trace invariante de jauge, l'action de Wilson. La boucle de Wilson, et la différence entre loi d'aire (confinement) et loi de périmètre. Un Monte Carlo U(1) en dimension 2, étalonné contre la loi exacte $\sigma = -\ln(I_1(\beta)/I_0(\beta))$ : à $\beta = 0{,}6$, tension mesurée `1.2499` contre `1.2474` (écart 0,20 %, seuil 5 %) ; à $\beta = 1$, pente `-0.808` contre `-0.807`. En dimension 4, le rapport $\chi(1,1)$ passe de `1.2214` à `0.2867` entre $\beta = 0{,}6$ et $1{,}2$ : la bascule de phase est observée, la transition n'est pas localisée. Le jumeau C# rejoue le même parcours avec la seule bibliothèque standard : tension mesurée `1.2514` (écart 0,33 %), pente `-0.805` contre `-0.807`, et en dimension 4 $\chi(1,1)$ de `1.2236` à `0.2848`. Les polynômes de Jones y sont calculés sur `BigInteger`. Chaque verdict y est doublé d'une assertion qui lève si elle échoue, et la dernière cellule du carnet atteste la parité avec le carnet Python, valeur par valeur. | Master : groupes de matrices, notions de Monte Carlo. Outils : numpy, sympy, mpmath, pandas, matplotlib ; jumeau C# sur le noyau `.net-csharp`, sans NuGet. | Deux prolongements dans le même carnet : nœuds et existence Yang–Mills (voir « Autour de 03 »). |
| 04 | [Jauge-04 — Des points aux spineurs : la relation d'incidence des twisteurs](Jauge-04-Points-Spineurs-Twisteurs-Python.ipynb) | Un point de l'espace-temps écrit comme une matrice hermitienne 2×2, dont le déterminant est la norme de Minkowski. Un point nul vu comme un spineur, à une phase près. SU(2) comme double revêtement des rotations : $U(\theta + 2\pi) = -U(\theta)$, il faut $4\pi$ pour revenir. La relation d'incidence $\omega = iX\pi$, vérifiée sur un rayon entier, et sa loi de transformation, contrôlée sur 200 éléments de SU(2) tirés au hasard (résidu maximal `1.43e-06`). Un noyau de collision de rayons : 60 cas détectés sur 60, aucun faux positif. | Master : algèbre linéaire complexe, relativité restreinte. Outils : PyTorch (`complex64`), matplotlib. | Exercices : carte point-matrice, tour complet, rayons parallèles. |
| 05 | [Jauge-05 — Twisteurs euclidiens : une sphère de structures complexes et le modèle standard](Jauge-05-Twisteurs-Euclidiens-Modele-Standard-Python.ipynb) | Une sphère de structures complexes sur $\mathbb{R}^4$ : chaque quaternion imaginaire unitaire en fournit une, orthogonale et auto-duale, de déterminant $+1$ et de norme $2$. La carte de Hopf $q k \bar q$ en forme close, avec la fibre qui est une phase à droite. Deux contre-témoins : une phase scalaire $e^{i\theta}$ conjugue la direction $k$ autour de $i$, d'un angle $2\theta$ (écart à la forme close `4.44e-16`) ; la carte de la source, écrite $x \mapsto x\cdot u$, produit la seconde composante de chiralité (déterminant `-1.000000000000`, composante auto-duale `1.67e-16`). Les spineurs de Weyl comme espaces propres de $J_3$ ; la demi-puissance du fibré déterminant imposée par la symétrie des poids (asymétrie nulle pour un seul décalage entier). Le compte de dimension de $\mathrm{PT} = \mathbb{CP}^3$ : `15 - 9 = 6`, un compte naïf qui donne `5`, impair. Enfin la table des seize états d'une génération, dont les cinq poids non nuls valent exactement $2\times$ l'hypercharge du modèle standard (écart `0`), et un contre-témoin à $-1/2$ qui est détecté (écart `1.0`). | Master : algèbre linéaire complexe, quaternions. Outils : numpy (`complex128`). | Exercices : inverse de la carte de Hopf, projecteur sur un spineur de Weyl, localiser l'alignement par balayage. |

## Approfondissements — Master et Recherche

La sous-série n'a pas de palier lettré. Ses approfondissements sont des sections des carnets.

### Autour de 03 : la boucle de Wilson hors du réseau

La section 7 de Jauge-03 quitte le réseau. Dans une théorie de Chern–Simons, la valeur moyenne d'une boucle de Wilson est un invariant de nœud. Le carnet construit une R-matrice et vérifie exactement ses relations : inversibilité, Yang–Baxter, Hecke. Il en tire le polynôme de Jones des nœuds $3_1$, $4_1$ et $5_1$, avec la loi du miroir, puis sa spécialisation aux premiers niveaux de la théorie.

Le carnet [KNOTS-02 — Invariants de nœuds](../../SymbolicAI/Lean/Noeuds/KNOTS-02-Invariants-Python.ipynb) calcule les mêmes polynômes par une voie indépendante. Les deux calculs se contrôlent l'un l'autre.

### Autour de 03 : l'énoncé d'existence Yang–Mills

La section 8 présente un énoncé formel d'existence pour Yang–Mills en dimension 4, publié en Lean le 28/10/2026 sous licence Apache-2.0. Le carnet l'énonce et recalcule en Python sa partie calculable, le test de non-liberté. La limite renormalisée doit valoir $3\dim(\mathfrak g)/\pi^4$, soit $9/\pi^4 \approx 0{,}0924$ pour SU(2). Tous les profils libres tendent vers 0, et la cible est atteinte par un modèle explicitement non libre.

**Ce n'est pas le problème Clay.** La source déclare hors périmètre l'écart de masse et l'unicité de la prescription de champ. La lecture détaillée de la soumission est consignée dans [la cartographie sourcée](../../../docs/research/yang-mills-openai-20261028-analyse.md), avec [un outil de relecture rejouable](../../../scripts/ym_openai_20261028/inventory.py).

### Exercices des carnets

- **Jauge-01** : translation de la particule libre, potentiel central quelconque, translation dans le temps et énergie.
- **Jauge-02** : jauge U(1) sur le champ de Dirac, doublet scalaire SU(2), composante $F^3$ explicite.
- **Jauge-03** : loi de périmètre contre loi d'aire, tension de ficelle de SU(2) en couplage fort, rapport $\chi(2,2)$, nœud torique $T(2,7)$ par la R-matrice.
- **Jauge-04** : la carte point-matrice sur un lot tiré par le lecteur, le tour complet du double revêtement, deux rayons parallèles.
- **Jauge-05** : reconstruire un point de la sphère depuis son image de Hopf, écrire le projecteur sur un spineur de Weyl, retrouver par balayage le seul poids qui aligne la table sur l'hypercharge.

Les cellules d'exercice s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Installation — pratique, tous niveaux

Les carnets Python tournent sur le noyau `python3`, sans GPU. PyTorch ne sert qu'à Jauge-04, mpmath et pandas qu'à Jauge-03. Les jumeaux C# de Jauge-02 et de Jauge-03 tournent sur le noyau `.net-csharp` (.NET Interactive) : ils ne chargent aucun paquet NuGet et n'utilisent que la bibliothèque standard.

```bash
python -m pip install jupyterlab ipykernel numpy scipy sympy mpmath pandas matplotlib torch
jupyter lab MyIA.AI.Notebooks/Physique/Jauge/Jauge-01-Theoreme-Noether-Python.ipynb
```

Les tirages aléatoires de Jauge-03, de Jauge-04 et de Jauge-05 sont semés. Le Monte Carlo de Jauge-03 demande plus de temps que les calculs symboliques. L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Physique](../README.md).

Le jumeau C# de Jauge-03 sème ses tirages avec le générateur de .NET, qui n'est pas celui de numpy : les valeurs mesurées diffèrent donc légèrement de celles du carnet Python, sans changer aucun verdict.

## Pour aller plus loin — Recherche

**Ce qui est mesuré, ce qui est cité.** En dimension 2, la tension de ficelle est comparée à une loi exacte : c'est un étalonnage du simulateur. En dimension 4, le carnet observe une bascule entre couplage fort et couplage faible. La valeur de la transition de U(1) compact, proche de $\beta_c \approx 1{,}01$, est citée et non mesurée. Aucun de ces calculs ne démontre le confinement d'une théorie non abélienne continue.

**Périmètre classique.** Jauge-02 traite les champs de jauge classiques, sans quantification. Jauge-04 vérifie la structure classique et numérique de la correspondance des twisteurs, en `complex64`, donc avec un plancher de résidu voisin de $10^{-7}$. Jauge-05 mesure de la géométrie de $\mathbb{R}^4$ et de l'arithmétique de représentations : rien n'y dépend d'une expérience, et il ne prétend pas démontrer la proposition d'unification de sa source, qui reste ouverte.

**Formalisation.** Jauge-01 relève que le théorème de Noether n'est pas formalisé dans Mathlib. L'énoncé d'existence de la section 8 de Jauge-03 est, lui, un objet formel : sa cartographie dit ce qui y est prouvé et ce qui reste hors périmètre.

**Ponts.** [Constructeur](../Constructeur/README.md) relit une conservation comme un énoncé de tâche impossible. La géométrie des rayons de Jauge-04 rejoint les représentations 3D étudiées dans [GenAI/3D](../../GenAI/3D/README.md). La sous-série [KNOTS](../../SymbolicAI/Lean/Noeuds/README.md) reprend les invariants de nœuds de la section 7.

## Ressources — tous niveaux

- E. Noether, *Invariante Variationsprobleme*, Nachr. Ges. Wiss. Göttingen, 235–257 (1918) ; traduction anglaise dans *Transport Theory and Statistical Physics* 1(3), 1971.
- C. N. Yang, R. L. Mills, *Conservation of Isotopic Spin and Isotopic Gauge Invariance*, Phys. Rev. 96, 191 (1954).
- K. G. Wilson, *Confinement of Quarks*, Phys. Rev. D 10, 2445 (1974).
- Source de l'énoncé d'existence : dépôt [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028), licence Apache-2.0.
- Source re-dérivée par Jauge-04 : `twistor-render-core`, licence MIT. Le code est re-dérivé dans le carnet, jamais importé.
- Source distillée par Jauge-05 : P. Woit, *Euclidean Twistor Unification*, arXiv:[2104.05099](https://arxiv.org/abs/2104.05099) (2021), sections 4.1 à 4.3 et 5. La copie utilisée est archivée dans le gisement bibliographique du dépôt, rayon `Physics` ; chaque valeur citée a été relue à cette copie, et les propositions qui ne se ramènent pas à un calcul y sont signalées comme citées.

[↑ Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
