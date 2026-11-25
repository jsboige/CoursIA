# Sudoku — frontière de l'inférence pure sur les grilles de niveau ≥ 13 : pré-enregistrement

- **Statut** : protocole scellé **avant** tout code de mesure et **avant** toute exécution sur une grille de niveau ≥ 13.
- **Parent** : issue #27214 (volet 3 de l'Epic #26242) ; carte des techniques : #27533.
- **Lane** : `myia-po-2028:CoursIA`.
- **Scellé le** : 2026-11-25, `main` au commit `edbdbb0d44`.
- **Ordre vérifiable** : ce document est le premier commit de sa branche ; l'instrument `scripts/path_profile.py` et son test viennent après lui.

## 1. La question

Le mainteneur a posé la question sur l'issue #27214 (commentaire du 2026-11-25T17:46:40Z), la veille du scellement. L'extrait qui fonde ce protocole, cité tel quel :

> La prédiction du mainteneur reflétant la conversation avec le mandataire récetteur, qui n'a pas besoin d'être vraie, et si elle ne l'est pas, ça sera une belle découverte dans la communauté des solveurs de sudoku, est que les derniers gestes d'inférence pure permettant de finir les sudokus de niveau >=13 seront plus lourds, de même que les 2 derniers gestes permettant de terminer le dernier étage d'un Rubik's cube, et que cela se lit sans doute dans la topologie de l'espace des états.

Le même commentaire borne le périmètre de deux façons, que ce protocole respecte :

- la frontière visée est celle de « l'ensemble des techniques recensées », pas celle d'un nombre restreint d'entre elles ;
- l'identification des gestes qui comblent les besoins d'exploration résiduels relève de « l'apprentissage symbolique », et le solveur exact sert « seulement comme oracle ».

Ce document transforme la prédiction en hypothèses falsifiables, fixe la règle de décision avant la mesure, et nomme ce qui manque pour l'exécuter. **Il ne contient aucun résultat sur les grilles de niveau ≥ 13** : le dépôt n'en contient aucune (§6).

## 2. Trois objets à ne pas confondre

Une « frontière » s'écrit souvent comme un seul nombre, qui mélange trois mesures distinctes. Elles sont séparées ici et le resteront dans tout rapport issu de ce protocole.

1. **Le catalogue sourcé.** L'ensemble des techniques recensées chez des implémentations publiques, avec pour chacune son statut dans le dépôt. Il dit ce qui *pourrait* être instrumenté.
2. **La couverture mesurée.** La part des grilles d'un corpus donné qu'un ensemble de règles `R` donné résout sans recherche, strate par strate. Elle dit ce que `R` *fait* sur *ce* corpus.
3. **Les arrêts résiduels.** Pour chaque grille que `R` ne résout pas, l'état où il s'arrête : nombre de pas, règles déclenchées, cases vides restantes, topologie de l'état. Ils disent *où* la frontière se trouve pour `R`.

Une augmentation du catalogue (1) qui ne change pas la couverture (2) n'a rien déplacé. Une couverture mesurée sur trois strates générées par un autre critère ne dit rien des niveaux ≥ 13. Un arrêt résiduel n'est pas un défaut du solveur : c'est la mesure.

### 2.1 État au scellement

Mesuré sur `main` au commit `edbdbb0d44`.

**Règles instrumentées.** `RULE_ORDER`, dans `MyIA.AI.Notebooks/Sudoku/scripts/inference_trace.py` (lignes 152-154), compte 11 règles : `naked_single`, `hidden_single`, `naked_pair`, `naked_triple`, `naked_quad`, `hidden_pair`, `hidden_triple`, `hidden_quad`, `pointing_pair`, `locked_claiming`, `x_wing`.

**Catalogue.** La carte du lot 1 (#27533, commentaire du 2026-11-21T07:42Z) recense 19 instances de techniques dans les 12 familles du dépôt amont. Onze sont instrumentées. **Huit manquent** : `swordfish`, `jellyfish`, `xy_wing`, `xyz_wing`, `xy_chain`, `unique_rectangle`, `hidden_rectangle`, `avoidable_rectangle`. Les PR #27898 (poissons d'ordre 3 et 4) et #27903 (`xy_wing`, `xyz_wing`) sont ouvertes au scellement et en couvrent quatre.

**Au-delà des 12 familles.** La même carte liste 28 lignes supplémentaires. Trois sont des méthodes exactes et non des techniques humaines (retour arrière, liens dansants, SAT). Trois relèvent du raisonnement hypothétique et sont à étudier à part, comme le demande l'Epic (chaînes de forçage, nishio, réseaux de forçage). Restent **22 lignes non hypothétiques non embarquées**, dont deux sont des variantes de l'unicité sans puissance ajoutée (`full_house`, `law_of_leftover`) : **20 techniques peuvent encore déplacer la frontière** sans sortir de l'inférence pure.

**Couverture mesurée par `R`.** D'après le corps de la PR #27754, fusionnée le 2026-11-25T20:27:08Z, sur dix grilles de chaque strate du corpus généré : facile 10/10, moyen 5/10, difficile 1/10, avec 30 traces sur 30 acceptées par l'oracle. Ce sont les strates du corpus généré, définies par le nombre de décisions d'un retour arrière, **pas** des niveaux d'une échelle publiée.

**Ce que cet état dit de la frontière.** Rien sur les niveaux ≥ 13. Il dit seulement où en est `R` sur un corpus qui n'est pas étiqueté par une échelle.

### 2.2 Ce qui manque au catalogue, par nature de manque

| Nature du manque | Contenu | Ce qui le comble |
|---|---|---|
| Instances Kermalis non embarquées | 8 (§2.1) | lots 3 à 5 de #27533 |
| Techniques hors Kermalis, inférence pure | 20 lignes (§2.1) | strates suivantes, ordre à arbitrer sur la mesure |
| Raisonnement hypothétique | 3 lignes | étude séparée, hors du périmètre « sans recherche » de cet Epic |
| Bibliographie de définition | les définitions de référence citées par le catalogue ne sont pas archivées au gisement bibliographique, qui ne détient sur le sujet que l'article de Norvig | dépôt au gisement avant toute rédaction qui en dépend |
| Licence | un dépôt sous GPL-3.0 (définition seulement), un dépôt sans licence (rien n'en part) | rédaction depuis la définition, pas depuis le code |

Le compte « 8 + 20 » est un compte de **lignes d'un tableau**, pas une mesure de puissance : deux techniques peuvent être équivalentes sur le corpus, et une technique peut n'y tirer sur aucune grille. La mesure qui compte est la re-mesure de la couverture après chaque lot, que #27533 exige.

## 3. Vocabulaire

- **`R`** : l'ensemble des règles d'un `InferenceSolver`, à savoir le tuple `RULE_ORDER` au commit mesuré. `R` évolue avec les lots ; toute mesure nomme le commit et le contenu de `RULE_ORDER`.
- **Politique de `R`** : à chaque pas, la première règle de `RULE_ORDER` qui trouve un pas est appliquée, dans l'ordre de balayage de l'organe. C'est une politique « la plus légère d'abord ».
- **Rang** d'une règle : sa position (à partir de 1) dans `RULE_ORDER`. Le rang est une **échelle ordinale du catalogue**, dans l'ordre de puissance croissante que lui donne le lot 1. Ce n'est **pas** une mesure de difficulté humaine.
- **Singleton** : une règle de rang 1 ou 2, qui place une valeur.
- **Geste** : un pas de rang ≥ 3, qui élimine des candidats.
- **Trace** : la suite des pas rendue par `solve()`, vérifiée par `verify_trace`.
- **État** : la grille et ses candidats à un instant de la trace.

## 4. Variables observées

Toutes sont calculées par grille, par le même module, sans paramètre laissé à l'analyste.

### 4.1 Grille résolue par `R`

| Variable | Définition |
|---|---|
| `P` | longueur du chemin, en pas |
| `r_max` | rang le plus élevé de la trace |
| `pos_r_max` | position (à partir de 0) du premier pas de rang `r_max`, divisée par `P - 1` ; 0 = premier pas, 1 = dernier ; non définie si `P = 1` |
| **geste final** | le dernier geste de la trace ; de l'état qui le précède, des singletons seuls terminent la grille |
| `rank_last` | rang du geste final ; **non défini** si la trace n'a aucun geste |
| `support_last` | nombre de cases distinctes citées par les prémisses du geste final ; pour les règles dont les prémisses ne nomment pas les cases mais les unités ou la valeur (`pointing_pair`, `locked_claiming`, `x_wing`), nombre de cases portant cette valeur sur ces unités, recalculé sur l'état qui précède le geste ; `None` si le module ne connaît pas la règle |
| `elim_last` | nombre de candidats éliminés par le geste final |
| `collapse` | nombre de pas qui suivent le geste final ; ce sont des singletons par construction |
| `tangle_last` | enchevêtrement (§4.3) de l'état qui précède le geste final |

### 4.2 Grille non résolue par `R` (arrêt)

| Variable | Définition |
|---|---|
| `steps_stall` | nombre de pas avant l'arrêt |
| `rank_hist` | histogramme des rangs déclenchés |
| `empty_stall` | cases vides à l'arrêt |
| `cands_stall` | candidats restants à l'arrêt |
| `tangle_stall` | enchevêtrement de l'état d'arrêt |

### 4.3 Enchevêtrement d'un état (`tangle`)

C'est la variable par laquelle la « topologie de l'espace des états » reçoit une définition calculable. **Cette définition est une lecture de la lane, soumise à arbitrage : le mainteneur a nommé la topologie sans la définir, et une autre définition est possible.**

- **Nœuds** : chaque candidat `(case, chiffre)` de l'état.
- **Lien** : entre deux candidats qui s'excluent — deux chiffres d'une même case, ou un même chiffre en deux cases d'une même unité. C'est le graphe dans lequel se déplace une chaîne d'inférence : d'un candidat vers un candidat qu'il exclut.
- **`tangle`** : taille de la plus grande composante connexe du graphe, divisée par le nombre de nœuds. Il vaut 1 quand tous les candidats forment un seul bloc ; il décroît quand l'état se fragmente en sous-ensembles qui ne s'excluent plus entre eux. Un état sans candidat (grille complète) n'en a pas : la variable vaut alors `None`.

Le lien fort (deux candidats d'une même unité portant le même chiffre, les deux seuls à le porter) est un cas particulier du lien ci-dessus et n'en change pas la connexité. La variable mesure donc la **connexité du graphe d'exclusion**, et non la densité des liens forts : compter ces liens serait une autre lecture de « topologie », non retenue ici.

## 5. Hypothèses

### 5.1 La prédiction du mainteneur, opérationnalisée

Elle se lit : « les derniers gestes d'inférence pure des grilles de niveau ≥ 13 seront plus lourds ». Quatre lectures, qui ne s'excluent pas.

| Code | Lecture de « plus lourd » | Prédiction sur les grilles résolues par `R` |
|---|---|---|
| **H-W1** (primaire) | plus haut dans le catalogue | `rank_last` plus élevé sur `S_haut` que sur `S_bas` |
| H-W2 | plus de cases concernées | `support_last` plus élevé sur `S_haut` |
| H-pos | plus tard dans la résolution | `pos_r_max` plus grand sur `S_haut` |
| H-collapse | moins de résolution « toute faite » après lui | `collapse` plus court sur `S_haut` |

### 5.2 La lecture topologique (exploratoire)

| Code | Prédiction |
|---|---|
| T | `tangle_last` plus élevé sur `S_haut` que sur `S_bas` |

T est **l'interprétation de la lane** de « cela se lit sans doute dans la topologie de l'espace des états », par analogie avec les derniers gestes d'un Rubik's cube, qui demandent une coordination globale. Elle est mesurée et publiée quoi qu'il arrive, mais **un verdict sur T n'est pas un verdict sur la prédiction du mainteneur** : il porte sur une définition que le mainteneur n'a pas écrite.

### 5.3 Strates

Les strates sont celles d'une **échelle de niveaux publiée et vérifiable**, à identifier (§6).

- `S_haut` : niveaux 13, 14 et 15.
- `S_milieu` : niveaux 6 à 12.
- `S_bas` : niveaux 1 à 5.

Une strate est **définie par l'échelle, jamais par le comportement de `R`** : définir `S_haut` comme « les grilles que `R` ne résout pas » rendrait la prédiction circulaire.

## 6. La jambe L0 — conditions préalables, non satisfaites au scellement

Mesuré au scellement.

- **L0.a — la source de l'échelle.** Les « 15 niveaux » ne sont définis nulle part dans le dépôt. Le carnet `Sudoku-21-DifficultyMeasures-Python.ipynb` classe leurs libellés en « hypothèse non sourcée » ; le volet 2 de l'Epic #26242 les nomme « des hypothèses à documenter, pas une norme universelle présumée ». Le gisement bibliographique ne détient sur le sujet que l'article de Norvig. **Condition** : une publication ou un site vérifiable qui définit l'échelle et ses seuils, archivé au gisement, avec le texte exact de la définition de chaque niveau.
- **L0.b — le corpus étiqueté.** Aucune grille du dépôt ne porte un niveau d'une échelle. **Condition** : un corpus dont chaque grille porte un niveau de l'échelle de L0.a, avec provenance, licence et droits de redistribution établis. Les grilles non redistribuables restent hors dépôt, avec leur chemin et une procédure de reproduction.
- **L0.c — l'empreinte.** **Condition** : la liste des grilles, leur `sha256`, leur niveau et la référence de l'échelle sont commités **avant** toute exécution.

**Tant que L0 n'est pas satisfaite, l'étude de §7 n'est pas exécutable sur les niveaux ≥ 13.** Une demande d'arbitrage est inscrite au registre des questions de la lane pour L0.a et L0.b. Elle n'arrête rien : les lots du catalogue (§2.2) et le pilote (§9) ne dépendent pas d'elle.

### 6.1 Repli si l'échelle n'est jamais sourcée

L'étude ne peut alors pas tester la prédiction du mainteneur, et **ne doit pas prétendre l'avoir fait**. Ce qui reste mesurable est une frontière **définie par machine** : les grilles triées par le critère de leur générateur (décisions d'un retour arrière) ou par un solveur de référence nommé. Un tel résultat se publie sous son propre nom (« frontière pour `R` sur le corpus X, trié par Y ») et **jamais** sous le nom de niveaux ≥ 13.

## 7. Règle de décision (scellée)

### 7.1 Test primaire — H-W1

- **Comparaison** : `rank_last` de `S_haut` contre `rank_last` de `S_bas`.
- **Statistique** : `U` de Mann-Whitney, unilatérale (`S_haut` plus grand).
- **Valeur `p`** : test de permutation sur `U`. Énumération exhaustive si le nombre d'assignations est ≤ 500 000 ; sinon 100 000 tirages avec la graine `20261125`.
- **Seuil** : `p < 0,05`.
- **Plus petit effet d'intérêt** : médiane de `S_haut` − médiane de `S_bas` ≥ 2 rangs.
- **Grilles sans geste final** (`rank_last` non défini) : comptées et publiées à part ; elles n'entrent pas dans le test. Si `S_haut` en contient, la prédiction est contredite pour ces grilles, et le rapport le dit.

| Verdict | Condition |
|---|---|
| `SOUTENUE` | `p < 0,05` **et** écart des médianes ≥ 2 rangs |
| `REFUTEE` | écart des médianes ≤ 0 **et** `p < 0,05` dans le sens contraire |
| `NON CONCLUANTE` | tout autre cas |

### 7.2 Tests secondaires

Même schéma (permutation unilatérale, seuil 0,05), avec correction de Holm sur les trois prédictions secondaires de §5.1. Plus petits effets d'intérêt : H-W2 ≥ 2 cases, H-collapse ≥ 2 pas. H-pos se teste sur `S_haut` seule : la part de grilles avec `pos_r_max ≥ 0,5` est comparée à 0,5 par un test binomial exact unilatéral. T (§5.2) se publie **sans** correction et porte l'étiquette « exploratoire ».

### 7.3 Porte de faisabilité

L'étude n'est déclarée exécutable que si **au moins 20 grilles de `S_haut` sont résolues par `R`** et portent un geste final. En dessous, la prédiction n'est pas testable sous cette forme : **le résultat est alors la frontière elle-même**, c'est-à-dire la liste des arrêts résiduels de `S_haut` (§4.2), et ce résultat se publie comme tel.

### 7.4 Conditions de réfutation de cette opérationnalisation

- **R-a** : le test primaire n'est pas `SOUTENUE`.
- **R-b** : médiane de `pos_r_max` sur `S_haut` < 0,5 — le geste le plus lourd se situe au milieu du chemin, pas à son terme.
- **R-c** : moins de 20 grilles de `S_haut` résolues par `R` (§7.3).

### 7.5 Corpus et exclusions

- **Corpus fixé avant l'exécution** (L0.c) : liste, `sha256`, niveau, référence de l'échelle.
- **Échantillonnage** : toutes les grilles d'une strate si elle en compte ≤ 400 ; sinon 400 tirées sans remise avec la graine `20261126`.
- **Exclusions, et aucune autre** : lignes vides ou de commentaire ; doublons exacts (un seul exemplaire conservé, compté) ; grilles sans solution unique, écartées par l'oracle et comptées ; traces refusées par `verify_trace`, comptées et publiées.
- **Aucune grille n'est retirée pour son résultat.**

### 7.6 Un seul oracle

`dlx_certificates.solve_certificate` sert **exclusivement** à trois choses : établir l'unicité de la solution, fournir la solution de référence, et vérifier chaque pas par `verify_trace`. **Il ne fournit jamais une étape d'inférence.**

### 7.7 Limites nommées

- **Dépendance à la politique.** Les variables dépendent de la politique « la plus légère d'abord » et de l'ordre de balayage de l'organe. Une autre politique donne un autre chemin sur la même grille. Les conclusions sont conditionnelles à cette politique.
- **Conclusion conditionnelle.** Tout verdict porte sur « les grilles de niveau ≥ 13 que `R` résout ». Si `R` bute sur la majorité de `S_haut`, le verdict décrit une minorité, et le rapport le dit avec le compte.
- **Le rang n'est pas la difficulté.** Un rang plus élevé signifie « plus haut dans le catalogue », pas « plus dur pour un humain ».
- **`tangle` est une définition parmi d'autres** (§4.3).

## 8. Apprentissage symbolique et solveur exact : la séparation

Le mainteneur demande que l'apprentissage symbolique reste « distinct du solveur exact, utilisé seulement comme oracle ». Trois rôles, trois objets, aucun passage de l'un à l'autre en dehors des flèches nommées.

| Rôle | Objet | Ce qu'il produit | Ce qu'il ne produit jamais |
|---|---|---|---|
| Solveur exact | `dlx_certificates` | unicité, solution de référence, vérification de chaque pas | une étape d'inférence, une règle |
| Solveur d'inférence pure | `InferenceSolver` et `R` | la trace vérifiée, qui est la **donnée** de l'étude | une décision fondée sur une recherche |
| Apprenant symbolique | à concevoir (pli suivant) | des **motifs candidats** de geste | une règle, tant que §8.1 n'est pas satisfait |

### 8.1 Le chemin d'un motif candidat vers une règle

Un motif produit par l'apprenant ne devient une règle qu'après, dans cet ordre :

1. une implémentation explicite dans `inference_trace.py`, sous un nom `Step.rule` figé ;
2. un témoin négatif fourni par l'oracle : une variante incorrecte du motif, et la preuve qu'elle élimine un candidat présent dans une solution compatible ;
3. la preuve Lean de sa correction, au volet 4 de l'Epic.

### 8.2 Ce que l'apprenant a le droit de voir

- **En entrée** : des états d'arrêt de `R`, et pour chacun une étiquette booléenne par candidat, « sûr à éliminer » ou non, calculée par l'oracle. Un candidat est sûr à éliminer s'il n'apparaît dans **aucune** solution compatible ; la grille étant à solution unique (établie par l'oracle), il suffit qu'il soit absent de la solution.
- **Jamais en entrée** : l'étiquette de strate, ni la solution elle-même. L'étiquette booléenne est dérivée de la solution et le lui doit : c'est la raison pour laquelle un motif n'est retenu que s'il **s'énonce sans elle** (un motif sur les candidats et les unités de la grille), et s'il est validé **sans étiquette**.
- **En validation** : des grilles et des graines disjointes de celles de l'apprentissage.

**L'exécution de cette jambe n'est pas ce grain.** Ce grain livre le protocole, l'instrument de mesure et le pilote. L'apprenant est un pli suivant de #27214.

## 9. Pilote (non compté)

Le pilote vérifie **seulement** que l'instrument s'exécute et que ses variables sont calculables. Il tourne sur les six corpus de `main` (`Puzzles/Sudoku_gen_{facile,moyen,difficile}.txt`, `Sudoku_Easy51.txt`, `Sudoku_hardest.txt`, `Sudoku_top95.txt`), avec le `R` du commit mesuré.

- Il est **étiqueté « pilote, non compté »** : aucune de ses valeurs n'entre dans un verdict de §7.
- Aucun de ces corpus n'est étiqueté par une échelle : **le pilote ne dit rien des niveaux ≥ 13**.
- Ses valeurs sont ajoutées sous le titre §10, en un commit distinct, **sans modification d'aucune règle de ce document**. Tout autre changement est une révision (§11).
- S'il révèle un défaut de comparabilité d'une variable, ce défaut est réglé par une révision v2 (§11), pas par un ajustement silencieux.

## 10. Valeurs du pilote

Ajoutées après exécution, conformément à §9. Cette section est vide au scellement.

## 11. Révision

**Une seule révision v2 est permise**, en un commit séparé, qui nomme les valeurs de la v1 et son motif. Le seul motif admis est un **défaut de comparabilité** (une variable non calculable sur une strate, une définition ambiguë). Un résultat déplu n'est jamais un motif : changer la règle après avoir vu le résultat, c'est le travers même que le pré-enregistrement existe pour empêcher. La v2 est écrite **avant** toute exécution sur `S_haut`.

## 12. Ce qui est publié quoi qu'il arrive

- Le verdict nommé de §7.1, et la liste des prédictions tombées de §5.
- Les comptes de §7.5 : doublons, grilles non uniques, traces refusées, grilles sans geste final.
- Les arrêts résiduels de `S_haut`, dans leur ensemble.
- Le commit de `R`, le corpus et son empreinte, la référence de l'échelle.

Une prédiction réfutée sur ce protocole est un résultat, et se publie comme tel : c'est le sens de la remarque du mainteneur selon laquelle une prédiction fausse « sera une belle découverte dans la communauté des solveurs de sudoku ».

## Voir aussi

- Issue #27214 — volet 3, format de trace et couverture sans recherche.
- Issue #27533 — carte des techniques et onboarding par lots.
- Epic #26242 — « Sans gomme » et le périmètre de l'inférence pure.
- `MyIA.AI.Notebooks/Sudoku/scripts/inference_trace.py` — l'organe de trace, de vérification et de couverture.
- `MyIA.AI.Notebooks/Sudoku/scripts/path_profile.py` — l'instrument de mesure de ce protocole.
