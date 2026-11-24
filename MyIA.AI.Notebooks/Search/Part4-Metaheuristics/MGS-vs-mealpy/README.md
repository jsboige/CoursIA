# MGS vs mealpy — campagne comparative

[↑ Partie 4 : Métaheuristiques composables](../README.md) · [← MGS-21 : représentation contre algorithme](../MGS-21-Representation-vs-Algorithme.ipynb) · [Entrée : MGS-22](MGS-22-MGS-vs-Mealpy.ipynb)

Quand deux bibliothèques proposent « le même » algorithme d'optimisation, que compare-t-on au juste en les faisant courir l'une contre l'autre ? Cette sous-série répond par l'expérience. Elle oppose MetaGeneticSharp (MGS), la bibliothèque C# de la Partie 4, à mealpy, une bibliothèque Python de métaheuristiques, sur un même Sudoku, avec le même budget d'évaluations, les mêmes graines et la même fonction de coût. Neuf paires d'algorithmes passent au banc, une par carnet, puis un dernier carnet relit les neuf résultats ensemble.

La leçon tient en deux axes que le temps de calcul brut mélange. Le **coût par évaluation** penche du même côté dans presque toutes les paires : c'est une affaire de langage et de moteur. La **qualité de la solution**, elle, change de camp d'une paire à l'autre : MGS termine devant sur quatre paires, mealpy sur cinq, et l'écart de médiane va de 11,5 conflits en faveur de MGS à 10 en faveur de mealpy. Aucune des deux bibliothèques n'est « la meilleure » : ce qui décide, c'est l'algorithme, ses paramètres par défaut et la façon dont il réinsère ses solutions.

## Comment lire ce README — découverte

Ce README suit le principe de lecture à trois vitesses du dépôt ([choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture)).

- **Vous découvrez** : lisez l'ouverture ci-dessus, puis le tableau du parcours principal. Le premier carnet pose le protocole, le dernier donne la vue d'ensemble ; à eux deux ils suffisent pour saisir la méthode et le verdict.
- **Vous creusez une paire** : chaque ligne du tableau renvoie à un paragraphe des approfondissements, qui dit quelle expérience le carnet ajoute au simple duel et sur quoi portent ses exercices.
- **Vous cherchez la recherche** : la section « Pour aller plus loin » donne les limites du banc et les questions que la campagne laisse ouvertes.

## Parcours principal — lecture guidée et prérequis

Tous les carnets partagent le même protocole, posé dans le premier et détaillé [plus bas](#le-protocole-commun) : une grille de Sudoku facile, une représentation continue des cases vides, environ 8 000 évaluations par course, quatre graines, et une qualité mesurée en nombre de conflits restants (zéro signifie grille résolue). Les valeurs du tableau sont des médianes sur les quatre graines, suivies de l'étendue entre crochets ; plus c'est bas, mieux c'est.

<a id="table-des-paires"></a>

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|----------|--------------------|---------------------|------------------|
| 22 | [Le banc fondateur : essaim particulaire](MGS-22-MGS-vs-Mealpy.ipynb) | Poser un protocole apparié et le faire tourner sur l'essaim particulaire (PSO). MGS finit à 17,0 [12-22], mealpy à 28,5 [26-31] : les étendues ne se touchent pas. Une expérience résolue montre d'où vient l'écart. | Licence. Avoir lu [MGS-21](../MGS-21-Representation-vs-Algorithme.ipynb) pour la représentation continue du Sudoku. | [Autour de 22](#autour-de-22) |
| 23 | [Évolution différentielle](MGS-23-DifferentialEvolution-vs-Mealpy.ipynb) | Écarter un confondant avant de conclure : les deux bibliothèques n'ont pas le même facteur de différence par défaut. mealpy 21,5 [20-27], MGS 25,5 [20-29], étendues chevauchées. | Licence. Le protocole de 22. | [Autour de 23](#autour-de-23) |
| 24 | [Recuit simulé](MGS-24-SimulatedAnnealing-vs-Mealpy.ipynb) | Deux architectures sous un même nom : un recuit à population contre un marcheur unique. MGS 27,0 [22-28], mealpy 31,0 [27-34]. | Licence. Le protocole de 22 ; le critère de Metropolis ([MGS-19](../MGS-19-MetropolisReinsertion.ipynb)). | [Autour de 24](#autour-de-24) |
| 25 | [Optimisation par baleines](MGS-25-WhaleOptimisation-vs-Mealpy.ipynb) | Isoler un opérateur par une troisième colonne : la spirale de MGS, sa variante sans spirale, mealpy. 49,5, 49,5 et 51,0 : la spirale ne change rien sur ce paysage. | Licence. Le protocole de 22. | [Autour de 25](#autour-de-25) |
| 26 | [Optimiseur d'équilibre](MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb) | Chercher un écart ailleurs que dans les formules : MGS est un portage déclaré du code mealpy, et pourtant mealpy finit à 25,0 [21-31] contre 35,0 [35-41]. | Licence avancée. Le protocole de 22 ; la notion de réinsertion ([MGS-02](../MGS-02-Composition.ipynb)). | [Autour de 26](#autour-de-26) |
| 27 | [Investigation criminalistique](MGS-27-ForensicBasedInvestigation-vs-Mealpy.ipynb) | Deux portages du même article qui ont dérivé. MGS 37,0 [25-39], mealpy 43,5 [43-45], MGS devant sur les quatre graines. | Licence avancée. Le protocole de 22. | [Autour de 27](#autour-de-27) |
| 28 | [Essaim sans vitesse](MGS-28-BareBonesPSO-vs-Mealpy.ipynb) | Construire le jumeau qui manque à mealpy, puis décomposer l'écart en deux : l'ancrage de la formule (nul) et le reste du moteur (30,5 [29-31] contre 25,5 [19-27]). | Licence avancée. Les carnets 22 et 23. | [Autour de 28](#autour-de-28) |
| 29 | [Algorithme génétique](MGS-29-GA-vs-Mealpy.ipynb) | La revanche à armes classiques : mealpy 12,5 [9-16], MGS 13,5 [12-18], « comparable » selon le critère annoncé. L'écart de l'essaim ne se reproduit pas. | Licence. Le protocole de 22 ; les opérateurs génétiques ([MGS-01](../MGS-01-Introduction.ipynb)). | [Autour de 29](#autour-de-29) |
| 30 | [Recherche par dispersion](MGS-30-ScatterSearch-Decomposition.ipynb) | Reconstruire un algorithme absent de mealpy et ablater une couche côté MGS : la diversité du jeu de référence ne paie pas ici (54,0 avec, 52,0 sans, 51,5 pour le jumeau). | Licence avancée. Les carnets 22 et 28. | [Autour de 30](#autour-de-30) |
| 31 | [Synthèse croisée](MGS-31-Synthese-Croisee.ipynb) | Relire les neuf paires ensemble sans rien ré-exécuter : tableau croisé, contrôle d'intégrité, forme des écarts, et le verdict « coût systématique, qualité spécifique ». | Tous niveaux pour le verdict ; Licence pour la méthode. Aucune paire n'est un prérequis strict. | [Autour de 31](#autour-de-31) |

Les carnets se lisent dans l'ordre des numéros : chacun referme une question et en ouvre une pour le suivant. Un lecteur pressé peut lire 22, une paire au choix, puis 31.

## Approfondissements — Licence et lectures avancées

### Le protocole commun

Le carnet 22 pose le protocole, et tous les suivants le reprennent à l'identique. Tout écart est déclaré dans le carnet concerné.

- **Problème.** Une grille de Sudoku facile à 36 cases vides, la même que celle du carnet [MGS-21](../MGS-21-Representation-vs-Algorithme.ipynb). Chaque case vide est un réel de l'intervalle [1, 10), ramené à un chiffre par arrondi.
- **Coût.** Le nombre total de conflits sur les rangées, les colonnes et les blocs. Il est implémenté deux fois, en C# et en Python, et les deux versions sont vérifiées égales sur trois vecteurs témoins avant toute course.
- **Budget.** Environ 8 000 évaluations par course, soit une population de 50 individus sur 160 générations ou époques. Les évaluations réellement consommées sont comptées, parce que les deux moteurs ne dépensent pas toujours exactement leur budget.
- **Graines.** Les quatre mêmes graines des deux côtés, et un contrôle de déterminisme : relancer une course avec la même graine doit redonner le même résultat.
- **Mesures.** La qualité est le nombre de conflits en fin de course, résumé par la médiane et l'étendue. Le temps est une médiane de trois répétitions par graine. Le coût de la fonction de fitness seule est mesuré à part, pour séparer ce qui vient du langage de ce qui vient de l'algorithme.
- **Vérification croisée.** La meilleure solution trouvée par mealpy est recomptée par la fonction de coût C#.
- **Critère annoncé d'avance.** Un moteur « domine » si sa médiane est strictement plus basse et si ses plus mauvais résultats restent sous les meilleurs de l'autre. Sinon le verdict est « comparable ».

Les deux bibliothèques tournent dans la même exécution : le noyau .NET charge MGS directement et pilote mealpy à travers un pont vers Python.

### Autour de 22

Le duel sur l'essaim particulaire sert de modèle aux suivants : sanité de la fonction de coût, pont vers Python, banc, lecture des trajectoires à quatre points de passage, vérification croisée. La forme de l'écart y est une précipitation précoce : MGS prend l'avantage dans le premier quart du budget et le garde. L'expérience résolue de la troisième partie retire la mutation du composé MGS : l'essaim se fige alors sur un plateau à 43,5 [39-48], parce qu'une vitesse bornée sur un objectif arrondi finit par ne plus rien déplacer. Les exercices proposent la revanche avec un algorithme génétique, un budget quadruplé et le profilage de la fonction de fitness.

### Autour de 23

L'évolution différentielle de mealpy travaille par défaut avec un facteur de différence cinq fois plus petit que celui de MGS. Le carnet transforme cette observation en quatre expériences dont le verdict est écrit avant la mesure : donner à mealpy le facteur de MGS (42,5, le confondant est rejeté), donner à MGS celui de mealpy (25,5, aucune amélioration), ramener dans le domaine les propositions qui en sortent (27,5, aucune amélioration), faire croître le facteur au fil de la course (25,0, un compromis : meilleur au premier quart, pas à la fin). Les exercices portent sur la sensibilité au facteur, le budget quadruplé et le profilage.

### Autour de 24

Les deux recuits ne se ressemblent que par le nom. Celui de MGS fait évoluer une population dont la réinsertion suit le critère de Metropolis ; celui de mealpy promène une seule solution, à raison d'une évaluation par époque. Le carnet aligne les budgets (8 000 époques côté mealpy) et discute ce que l'on compare vraiment quand les architectures diffèrent. Les exercices demandent d'aligner la température initiale, puis la taille du pas, et de quadrupler le budget.

### Autour de 25

L'optimisation par baleines déplace les solutions le long d'une spirale autour de la meilleure. MGS en fournit deux versions, avec la spirale et avec une simple combinaison convexe, ce qui donne une ablation gratuite : les deux finissent à la même médiane, 49,5, devant mealpy à 51,0 [50-54]. L'opérateur emblématique de l'algorithme n'apporte rien sur un objectif en paliers. Les exercices portent sur le budget quadruplé, le coefficient de mélange et le profilage.

### Autour de 26

C'est la paire la plus instructive pour qui porte du code d'une bibliothèque à l'autre. Les constantes et la composition du pool d'équilibre sont les mêmes des deux côtés, et l'écart est pourtant le plus grand de la campagne en faveur de mealpy. Trois expériences correctives le décomposent : une réinsertion gloutonne par individu, optionnelle, ramène MGS à 32,0 [30-39] ; un instrument qui compte les tirages dans le pool montre que le portage d'origine ne tirait jamais son meilleur membre ; borner les positions au domaine dégrade le résultat (34,5). Les exercices portent sur le budget quadruplé, la taille de population à budget constant et le profilage.

### Autour de 27

L'algorithme a quatre phases, et les deux implémentations s'écartent sur deux d'entre elles : la loi du bruit de la première phase (gaussienne d'un côté, uniforme de l'autre) et le détail des appariements. Le carnet déclare ces dérives plutôt que de les corriger, et constate une séparation totale en faveur de MGS. Comme l'algorithme n'a aucun paramètre que l'on pourrait transporter d'une bibliothèque à l'autre, il n'y a pas de confondant à écarter. Les exercices font varier le budget (quadruplé, puis divisé par quatre) et la taille de population à budget égal.

### Autour de 28

mealpy propose plusieurs variantes d'essaim particulaire, mais pas celle qui se passe de vitesse. Le carnet construit donc le jumeau lui-même, en sous-classant l'optimiseur de base de mealpy, et fixe les formules avant de mesurer. Trois bras : le composé MGS, un jumeau mealpy aligné sur la sémantique de MGS, un jumeau mealpy fidèle à l'article d'origine. Les deux jumeaux donnent exactement les mêmes résultats graine par graine, donc le choix d'ancrage ne compte pas ; l'écart de cinq conflits avec MGS vient du reste du moteur. Les exercices portent sur le budget quadruplé, le plancher d'écart type qui empêche le gel, et le profilage.

### Autour de 29

Le composé génétique par défaut de MGS (sélection élitiste, croisement et mutation uniformes) affronte l'algorithme génétique de base de mealpy. Les médianes sont à un conflit l'une de l'autre et les étendues se chevauchent. Le carnet relève un détail qui compte pour la lecture : à nombre de générations égal, les deux moteurs ne consomment pas le même nombre d'évaluations, et MGS en dépense moins. Les trois exercices sont intercalés dans le carnet : compter les conflits par rangée, tester la sensibilité sur huit graines, tracer la convergence époque par époque.

### Autour de 30

Un balayage des optimiseurs de mealpy n'en trouve aucun qui implémente la recherche par dispersion. Le carnet reconstruit donc un jumeau, formules fixées d'avance, et ajoute un bras d'ablation côté MGS : le jeu de référence complet, qui mêle qualité et diversité, contre un jeu de référence réduit à la qualité. Sur ce Sudoku et à ce budget, la diversité coûte plus cher par évaluation et ne rapporte rien. C'est la seconde décomposition de la campagne, et elle répond à l'inverse de celle du carnet 28 : ici le moteur est constant et c'est la stratégie qui varie. Les exercices portent sur le budget quadruplé, un balayage de la part de qualité dans le jeu de référence, et le profilage.

### Autour de 31

La synthèse ne relance aucune course. Elle relit les sorties archivées des neuf carnets de paires, recalcule chaque médiane et chaque étendue à partir des résultats par graine, et vérifie que ses chiffres retombent sur les résumés imprimés par chaque carnet. Elle en tire un tableau croisé et deux graphiques, puis trois lectures.

- **La qualité.** MGS est devant sur l'essaim particulaire, le recuit, les baleines et l'investigation criminalistique ; mealpy sur l'évolution différentielle, l'optimiseur d'équilibre, l'essaim sans vitesse, l'algorithme génétique et la recherche par dispersion.
- **Le coût.** mealpy coûte plus cher par évaluation dans huit paires sur neuf ; l'essaim particulaire fait exception.
- **La forme des écarts.** Elle n'est lisible que pour les quatre paires dont le banc journalise des points de passage (carnets 22, 23, 28 et 30). Les deux décompositions s'y répondent : à formule constante, l'écart du carnet 28 vient du moteur ; à moteur constant, celui du carnet 30 vient de la stratégie.

Un épilogue rapporte ce que devient la paire du recuit quand on quadruple le budget : l'écart ne se referme pas, il se creuse en faveur de MGS. Les exercices font calculer une médiane à la main, lire une étendue comme un signal de variance et classer la forme d'un écart.

## Installation — pratique, tous niveaux

Les dix carnets tournent sous le noyau C# de .NET Interactive et demandent trois choses.

| Besoin | Ce qu'il faut | Comment |
|--------|---------------|---------|
| MetaGeneticSharp | Le sous-module `MetaGeneticSharp` compilé en `Debug` pour `net9.0` : les carnets chargent ses bibliothèques par chemin relatif | Commandes dans la [configuration de la Partie 4](../README.md#configuration-requise) |
| mealpy | Un interpréteur CPython où `mealpy` s'importe | `pip install mealpy`, ou le fichier [`requirements.txt`](../../requirements.txt) de la série |
| Pont entre les deux | Le paquet NuGet `pythonnet`, que chaque carnet télécharge lui-même, et [`PythonNetLoader.cs`](../../../Config/PythonNetLoader.cs), qui trouve l'interpréteur | Rien à faire si `mealpy` est installé dans un Python standard ; sinon, pointer la variable d'environnement `PYTHONNET_PYDLL` vers la bibliothèque Python voulue |

`PythonNetLoader.cs` retient `PYTHONNET_PYDLL` si elle est définie, et sinon le premier interpréteur installé qui importe `mealpy`, sous Windows, Linux ou macOS. La première cellule du pont affiche la version chargée : les sorties archivées ont été produites avec mealpy 3.0.2. L'interface de la série 3 de mealpy compte ici, car la graine s'y passe à l'appel de résolution et non au constructeur.

Aucune donnée n'est à télécharger : la grille est écrite dans les carnets. Aucun GPU n'est nécessaire. Le carnet de synthèse lit les neuf autres sur le disque ; il faut donc les garder à côté de lui.

Les résultats de qualité sont reproductibles à la graine près. Les temps, eux, dépendent de la machine : attendez-vous à retrouver le sens des écarts de coût, pas leurs valeurs.

## Pour aller plus loin — recherche

### Ce que le banc ne dit pas

- **Un seul paysage.** Toute la campagne porte sur une grille de Sudoku facile, dans une représentation continue arrondie qui produit de larges plateaux. Aucun des deux moteurs ne résout la grille dans ce cadre : le banc compare des façons d'échouer plus ou moins près du but, et le carnet [MGS-21](../MGS-21-Representation-vs-Algorithme.ipynb) explique pourquoi la représentation pèse plus que l'algorithme.
- **Un seul budget.** Presque tous les carnets proposent en exercice de quadrupler le budget, et l'épilogue de la synthèse montre sur une paire que le classement peut s'accentuer. Rien ne garantit qu'il se conserve ailleurs.
- **Quatre graines.** C'est assez pour voir une séparation totale, pas pour départager deux médianes voisines. Le critère annoncé d'avance répond « comparable » dans ce cas, et il faut le prendre au mot.
- **Des paramètres par défaut.** Chaque bibliothèque court avec ses réglages d'origine, sauf expérience déclarée. Le carnet 23 montre ce qu'un seul paramètre par défaut peut déplacer.
- **Des temps d'horloge.** Le coût par évaluation mêle le langage, le pont vers Python et la mécanique de chaque moteur. La mesure de la fitness seule isole le premier terme ; les deux autres restent confondus.

### Questions ouvertes

- Les écarts de qualité tiennent-ils sur un paysage sans plateaux, par exemple les fonctions continues des carnets [MGS-06](../MGS-06-Benchmarks.ipynb) et [MGS-18](../MGS-18-CecBanc.ipynb) ?
- La réinsertion gloutonne par individu, qui rapproche MGS de mealpy dans le carnet 26, aiderait-elle ou nuirait-elle dans les paires où MGS est devant ?
- La diversité du jeu de référence, inutile ici, redevient-elle utile sur un problème multimodal ou à budget plus large ?

### Liens avec les autres parcours

- [Partie 4 : Métaheuristiques composables](../README.md) présente la bibliothèque et l'idée que les composants comptent plus que les métaphores.
- [Search-11 : métaheuristiques](../../Part1-Foundations/Search-11-Metaheuristics.ipynb) introduit en Python les familles d'algorithmes comparées ici, déjà avec mealpy.

## Ressources — tous niveaux

- [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) : le code source de la bibliothèque C# et ses tests.
- [mealpy](https://pypi.org/project/mealpy/) : la bibliothèque Python, telle que `pip` l'installe.
- Les articles d'origine des algorithmes les moins classiques sont cités dans les carnets qui les comparent : l'optimisation par baleines dans [le carnet 25](MGS-25-WhaleOptimisation-vs-Mealpy.ipynb), l'optimiseur d'équilibre dans [le carnet 26](MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb), l'investigation criminalistique dans [le carnet 27](MGS-27-ForensicBasedInvestigation-vs-Mealpy.ipynb), l'essaim sans vitesse de Kennedy (2003) dans [le carnet 28](MGS-28-BareBonesPSO-vs-Mealpy.ipynb), la recherche par dispersion dans [le carnet 30](MGS-30-ScatterSearch-Decomposition.ipynb).
