# Applications — des problèmes complets autour du hasard

[↑ Série Probas](../README.md)

Ce dossier réunit des carnets autonomes. Chacun prend un problème entier, le pose, le calcule et dit ce que le calcul établit ; aucun ne suppose les autres. On y rencontre une marche aléatoire qui revient ou ne revient pas à son point de départ, un auditeur qui comprend une exagération, deux observations d'un même phénomène que l'on cherche à comparer, et la géométrie des mesures log-concaves en grande dimension. La sous-série [Percolation](Percolation/README.md) y ajoute une transition de phase sur réseau, mesurée en Python et formalisée en Lean 4.

Les progressions de la série vivent ailleurs : l'inférence bayésienne en C# dans [Infer](../Infer/README.md), sa contrepartie Python dans [PyMC](../PyMC/README.md), la décision sous incertitude dans [DecisionTheory](../DecisionTheory/README.md). Les carnets d'ici s'adressent à des étudiants de licence avancée et de master qui ont vu les probabilités discrètes et continues. Ils ont un trait commun : une valeur n'y est annoncée qu'après avoir été confrontée à une référence, et un carnet peut conclure qu'il n'a pas obtenu ce qu'il cherchait.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : choisissez une question dans le parcours principal. Les carnets se lisent dans n'importe quel ordre ; celui des marches aléatoires demande le moins de prérequis.
- **Vous creusez** : « Approfondissements » décrit la méthode que ces carnets partagent et leurs exercices ; « Sous-séries » présente Percolation.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » dit ce que chaque carnet laisse ouvert et où se prolonge sa question.

## Parcours principal — Licence avancée et Master

| Question | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| Une marche aléatoire revient-elle à son point de départ ? | [Marches-01 — Le retour, de Pólya au « problème final » de Watson](Marches-01-Retour-Polya-Watson-Python.ipynb) | Le théorème de Pólya, lu sur une série génératrice : elle diverge en dimension 1 et 2, elle sature en dimension 3. La simulation le montre à horizon fini : la fraction des marches revenues en 2000 pas vaut `0.9832`, `0.6915` puis `0.3326` en dimension 1, 2 et 3. En dimension 3, la probabilité de retour de la marche isotrope se ramène à l'intégrale de Watson. Le calcul numérique et la forme fermée en fonctions $\Gamma$ coïncident sur `22.755` chiffres, pour une probabilité de retour d'environ 0,3405. Le carnet traite ensuite la marche anisotrope de taux de saut 1/2, 1/3 et 1/6 : sa probabilité de retour, calculée à haute précision, vaut environ 0,3791. Une simulation indépendante la retrouve par en dessous, avec un biais d'horizon mesuré plutôt qu'ignoré. | Licence avancée : probabilités, intégrales. Outils : numpy, mpmath. | Exercices : dimension 4, limite d'un taux de saut nul, reconnaissance de constante. |
| Comment un auditeur comprend-il une exagération ? | [Pyro_RSA_Hyperbole — Le cadre Rational Speech Act](Pyro_RSA_Hyperbole.ipynb) | Le cadre RSA modélise la conversation comme un raisonnement emboîté : un auditeur littéral, un locuteur qui choisit l'énoncé le plus informatif, un auditeur pragmatique qui raisonne sur ce choix. Premier exemple : devant quatre objets, dire « some » rend improbable l'état où tous sont bleus. C'est l'implicature scalaire. Second exemple : l'hyperbole. L'état joint un prix et un degré d'irritation, et une « question en discussion » dit ce que le locuteur veut transmettre. À l'énoncé « 10000 », l'état de prix 50 avec irritation reçoit une probabilité de `0.1719`, contre `0.0190` sans irritation : l'exagération signale l'affect, pas le prix. Le carnet termine sur le halo pragmatique : « 50 » se lit « environ 50 », « 51 » se lit au plus près. L'inférence est exacte, par énumération des états. | Master : inférence bayésienne, notions de PyTorch. Outils : pyro-ppl, torch, matplotlib. | Exercices : prior non uniforme, rationalité du locuteur, question « est-ce cher ? », halo au multiple de 100. |
| Que partagent deux observations d'un même phénomène ? | [Quotients, fibres et recollement — ce qui survit à la projection](Quotients-Fibres-Recollement-Python.ipynb) | Un protocole en quatre temps pour comparer deux représentations autrement que par leur proximité. On construit un couple gaussien de corrélation 0,6, puis on mesure ce qu'il partage : l'information mutuelle estimée vaut `0.2645` nats, pour `0.2231` en théorie. L'écart est une sur-estimation, de signe stable sur huit graines ; la correction de Miller–Madow en prédit la direction, pas l'ampleur. On cherche ensuite un quotient commun : une variable grossière qui rendrait les deux observations presque indépendantes. Le quotient essayé échoue, car l'information conditionnelle monte à `0.4453` nats, soit un rapport de `1.684`. Le quatrième temps, la composition de transports, n'est donc pas tenté, et le carnet l'écrit. | Master : entropie, information mutuelle. Outils : numpy, scipy. | Exercices : couple lié non linéairement, raffinement du quotient, cas à quotient opérationnel. |
| Que devient une mesure log-concave quand la dimension grandit ? | [Probas-KLS-Concentration — trou spectral, constante de Cheeger et thin-shell](Probas-KLS-Concentration.ipynb) | Trois mesures isotropes — gaussienne, cube, simplexe — suivies de la dimension 2 à la dimension 20. La marche hit-and-run, dont le temps d'autocorrélation d'une coordonnée croît avec la dimension : de `3.0` à `123.2` sur le cube, de `3.9` à `386.5` sur le simplexe. La constante de Cheeger, sondée par des demi-espaces : la sonde rend `0.7979` sur la gaussienne, valeur exacte $\sqrt{2/\pi}$, et reste près de $1/\sqrt{3}$ sur le cube à toutes les dimensions. La variance thin-shell, confrontée à ses formules exactes : en dimension 20, `40.09`, `16.01` et `63.68` pour des valeurs exactes de 40, 16 et 63,91. Le carnet dit pourquoi ces mesures ne démontrent pas la conjecture KLS : un balayage de demi-espaces ne détermine pas l'infimum pris sur tous les ensembles. | Master et Recherche : chaînes de Markov, inégalités de concentration, vues dans [PyMC](../PyMC/README.md) et [Infer](../Infer/README.md). Outils : numpy, scipy, matplotlib. | Exercices : sonde direction par direction, estimateur sur un processus à deux modes, effet de l'isotropisation. |

## Approfondissements — Master

### Mesurer contre une référence : la méthode commune

Ces carnets partagent une façon de travailler, qui vaut d'être lue pour elle-même.

- **Calculer d'abord, comparer ensuite.** Dans Marches-01, toute constante est obtenue par une route numérique avant d'être confrontée à sa forme fermée, jamais l'inverse. Le carnet travaille à 40 chiffres pour que la comparaison ait un sens.
- **Faire rejouer le résultat par une route qui peut échouer.** La probabilité de retour anisotrope est retrouvée par simulation sur quatre graines. Les quatre écarts sont négatifs, avec des z-scores de `-4.00` à `-0.39` : un horizon fini oublie les retours tardifs. Le carnet mesure ce déficit, vérifie qu'il décroît comme l'inverse de la racine de l'horizon, puis construit un estimateur à deux horizons dont l'erreur relative va de `0.40 %` à `2.03 %`.
- **Étalonner l'instrument sur un cas connu.** Probas-KLS-Concentration valide chaque sonde avant de s'en servir : un processus AR(1) de trou spectral connu pour le temps d'autocorrélation, la gaussienne pour la constante de Cheeger, trois formules exactes pour la variance thin-shell.
- **Mesurer un signe au lieu de le recopier.** Le carnet des quotients ne reprend pas d'un manuel le sens du biais de son estimateur. Il le calcule, puis le rejoue sur huit tirages : l'écart à la théorie va de `+0.0151` à `+0.0481` nats, toujours du même signe.
- **Dire ce qui n'est pas atteint.** Le carnet des quotients s'arrête avant son dernier temps, celui de la conjecture KLS borne la portée de ses tables, et celui des marches distingue ses valeurs vérifiées de valeurs certifiées.

### Exercices des carnets

- **Marches-01** : la probabilité de retour en dimension 4, la limite où un taux de saut tend vers zéro et où la récurrence de la dimension 2 réapparaît, la reconnaissance d'une constante dans un anneau déclaré à l'avance, avec le droit de refuser.
- **Pyro_RSA_Hyperbole** : un prior non uniforme sur les états, l'effet de la rationalité `alpha` du locuteur sur l'hyperbole, la question « isExpensive », l'extension du halo pragmatique à l'arrondi au multiple de 100.
- **Quotients, fibres et recollement** : un couple lié non linéairement où l'ajustement affine échoue, le raffinement du quotient et le démasquage d'un quotient déguisé, la construction du cas où la composition de transports devient mesurable.
- **Probas-KLS-Concentration** : la sonde de demi-espaces sur le simplexe, direction par direction, l'estimateur d'autocorrélation sur un processus à deux modes, la variance thin-shell du cube non isotrope.

Les cellules d'exercice s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Sous-séries — Master

### Percolation — Master

[Percolation](Percolation/README.md) garde chaque arête d'un réseau avec une probabilité $p$ et suit la transition qui en résulte : sous un seuil le réseau reste en morceaux, au-dessus une composante géante absorbe l'essentiel des sommets. La sous-série mesure cette transition sur des tores finis, en Python. Elle part du régime supercritique, s'installe au point critique pour en mesurer les exposants, reprend ces mesures à plus grande taille, confronte une loi d'échelle au théorème de *supercritical sharpness*, puis mesure la dimension fractale de l'amas critique. Des carnets Lean 4 l'accompagnent : ils lisent le lake `percolation_lean`, qui prouve sans `sorry` un noyau fini, de la corrélation positive des événements croissants à une inégalité de sharpness finie.

Sa règle est celle du dossier : un tore fini n'est pas le réseau infini de la théorie, chaque mesure est rapportée avec son écart à la valeur de la littérature, et le palier consacré à la sharpness conclut que sa fenêtre de mesure ne retrouve pas la loi visée. L'entrée est [Percolation-01](Percolation/Percolation-01-Supercritique-Python.ipynb), qui se lit sans prérequis de physique statistique. Marches-01 pose la question voisine par l'autre bout : le retour à l'origine plutôt que la connectivité.

## Installation — pratique, tous niveaux

Les carnets du dossier tournent sur le noyau `python3`, sans GPU.

```bash
python -m pip install jupyterlab ipykernel numpy scipy matplotlib mpmath pyro-ppl torch
jupyter lab MyIA.AI.Notebooks/Probas/Applications/Marches-01-Retour-Polya-Watson-Python.ipynb
```

Le fichier [`requirements.txt`](../requirements.txt) de la série couvre ces dépendances, sauf `mpmath`, que la ligne ci-dessus ajoute pour Marches-01. Le carnet RSA imprime la version de Pyro avec laquelle il a été exécuté, `1.9.1`. Les tirages sont semés, et les carnets qui comparent plusieurs graines les impriment.

La sous-série Percolation demande en plus `networkx`, et Lean 4 pour ses carnets formels : son README détaille l'installation.

## Pour aller plus loin — Recherche

**Ce que « fermer » un problème veut dire.** Marches-01 rapporte que la question anisotrope de Watson, posée en 1939, a été close en 2026 par une certification numérique : une arithmétique par boules encadre l'intégrale à précision arbitraire, sans forme fermée simple. Le carnet ne refait pas cette certification. Il calcule à haute précision, et dit que ses valeurs sont vérifiées numériquement, pas certifiées.

**Des marches aux intégrales de réseau.** L'intégrale de Watson donne le nombre moyen de visites à l'origine. C'est la valeur à l'origine de la fonction de Green du réseau cubique simple, l'objet que nomme le titre de la référence de 1973. La série [Physique — Intégrales](../../Physique/Integrales/README.md) applique les mêmes règles de méthode à des intégrales de Feynman.

**La conjecture KLS.** Elle compare la constante isopérimétrique prise sur tous les ensembles à celle des seuls demi-espaces. Le carnet ne sonde que des demi-espaces, par Monte-Carlo. Il étalonne ses instruments et montre ce qu'une expérience numérique peut dire, sans prétendre tester la conjecture. Il dérive au passage la variance thin-shell exacte du simplexe isotrope, puis la vérifie à 3 % près sur six dimensions. Le ralentissement de la marche hit-and-run, observé sur une coordonnée, ne donne pas une loi de mélange générale.

**Du quotient au recollement.** Le carnet des quotients n'atteint pas son critère de fond : un défaut de recollement devrait produire un témoin opérationnel, pas un résidu. Il nomme les suites possibles : un quotient à plusieurs dimensions, puis des représentations à valeurs dans un groupe, où la distance entropique de Ruzsa deviendrait applicable. Cette distance est mesurée dans le carnet [ANALYSE-04](../../SymbolicAI/Lean/Analyse/ANALYSE-04-PFR-Primitives-Python.ipynb), dans une autre série.

**Au-delà de l'énumération.** Le carnet RSA calcule par recherche exhaustive, ce qui convient à de petits espaces d'états. Pour un domaine plus grand, il renvoie à l'échantillonnage MCMC et à l'inférence variationnelle. Il indique aussi comment un affect à deux dimensions, valence et intensité, permet de modéliser l'ironie.

**Formalisations Lean.** Les énoncés formels du dossier sont ceux de la sous-série Percolation. Son lake [`percolation_lean`](Percolation/percolation_lean/) reste fini et uniforme : le cas de probabilité $p$ quelconque, la grille infinie et l'existence d'un seuil critique sont hors de sa portée.

## Ressources — tous niveaux

- G. Pólya, *Mathematische Annalen* **84**, 149–160 (1921) : le théorème de récurrence.
- G. N. Watson, « Three Triple Integrals », *Q. J. Math.* **10**(1), 266–276 (1939), doi:10.1093/qmath/os-10.1.266 : l'intégrale isotrope, exprimée en intégrales elliptiques complètes. L'article n'est pas en accès ouvert.
- G. S. Joyce, « On the simple cubic lattice Green function », *Phil. Trans. R. Soc. Lond. A* **273**, 583–610 (1973) : la fonction de Green du réseau cubique simple, dont le carnet recalcule la valeur à l'origine, environ 1,5164.
- M. D. Schwartz, *Vibe physics* et *Claude-shaped science* (essais, 2025) ; article associé [arXiv:2601.02484](https://arxiv.org/abs/2601.02484) (2026) : le récit de la clôture du problème anisotrope.
- [Pyro](https://pyro.ai/) : la bibliothèque de programmation probabiliste du carnet RSA.
- Chaque carnet donne sa bibliographie en fin de texte : géométrie des mesures log-concaves pour Probas-KLS-Concentration, pragmatique probabiliste pour Pyro_RSA_Hyperbole.

[↑ Série Probas](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
