# Causalité — quel effet peut-on identifier ?

[↑ Série Probas](../README.md)

Recevoir un mentorat et progresser vont de pair. Cela signifie-t-il qu'attribuer un mentor ferait progresser un élève ? Le parcours part de cette différence entre observation et intervention, puis examine ce qui reste identifiable quand le graphe, le mécanisme ou les mesures sont incertains. Prérequis : probabilités conditionnelles et lecture d'un graphe orienté sans cycle.

## Comment lire ce README — découverte

[Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : chaque palier change une hypothèse de l'étude.

- Vous découvrez : partez du mentorat, puis identifiez un effet avant de l'estimer.
- Vous creusez un palier : choisissez la difficulté qui vous concerne, par exemple un instrument faible ou un confondeur caché.
- Vous cherchez la recherche en cours : comparez les effets conditionnels sur deux populations au palier 10b.

## Parcours principal — licence avancée et master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 00 | [Observer ou intervenir](Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb) | Dans le monde simulé du mentorat, la réussite vaut 0,7078 chez les bénéficiaires, mais 0,6063 si l’on attribue le mentorat par intervention. | Licence | — |
| 01 | [Calculer avec do](Causalite-01-Calcul-Do-Python.ipynb) | Couper les flèches entrantes et tester la séparation dans le graphe. Distinguer ajustement, médiation et transport vers une autre population. Le carnet exécute les quatre tâches de la fusion de données (sous sélection, la pondération inverse ramène l’effet de 1,029 à 0,808 pour une vérité de 0,800), rend le théorème de la hiérarchie causale vérifiable à la machine avec deux modèles de même loi jointe aux interventions opposées, et relie le calcul do à l’attribution de Shapley. | Licence | — |
| 02 | [Nommer la quantité à estimer](Causalite-02-DoWhy-Estimand-Intervention-Python.ipynb) | En rééducation, l’effet naïf vaut 3,274, contre 2,382 après ajustement pour une cible de 2,390. Un test placebo favorable ne valide pas le graphe. | Master | — |
| 03 | [Poser un contrefactuel individuel](Causalite-03-DoWhy-Contrefactuel-Individuel-Python.ipynb) | Reconstruire les bruits pour un même individu avant de changer son traitement ; une moyenne nulle peut masquer des effets opposés. | Master | — |
| 04 | [Découvrir le graphe](Causalite-04-DoWhy-Decouverte-Structure-Python.ipynb) | PC retrouve le squelette sans orienter toutes les arêtes. Des orientations compatibles avec les observations donnent pourtant des effets différents. | Master | — |
| 05 | [Tester la sensibilité](Causalite-05-DoWhy-Sensibilite-Confondeur-Python.ipynb) | Évaluer la force nécessaire à un confondeur caché pour annuler un effet ; distinguer robustesse de l’estimation et preuve d’absence de confusion. | Master | — |
| 06 | [Éprouver un instrument](Causalite-06-DoWhy-Instrument-Faible-Python.ipynb) | Comparer les statistiques de première étape (2 333,75 et 6,71). Une forte association avec le traitement ne garantit pas l’exclusion. | Master | — |
| 07 | [Exploiter une quasi-expérience](Causalite-07-Quasi-Experimentales-Python.ipynb) | Comparer différences de différences, contrôle synthétique, discontinuité et variables instrumentales ; chercher un placebo ou une rupture des hypothèses. | Master | — |
| 08 | [Décomposer un écart entre groupes](Causalite-08-Equite-Causale-Python.ipynb) | Séparer effets directs, indirects et association non causale ; supprimer le chemin direct ne supprime pas forcément l’écart observé. | Master | — |
| 09 | [Émuler un essai cible](Causalite-09-Hernan-Emulation-Essai-Cible-Python.ipynb) | Définir le protocole avant l’analyse. Quand un confondeur varie avec les traitements antérieurs, comparer g-formule, pondération et ajustement naïf. | Master | — |
| 10 | [Interroger des sujets simulés](Causalite-10-Science-Sociale-Automatisee-Python.ipynb) | Comparer les réponses de modèles de langage à un mécanisme vendeur connu : deux quantifications de Qwen2.5-0.5B (AWQ et GPTQ) répondent sur trois graines, soit 450 exécutions exploitables. Une sensibilité au libellé mesure le comportement du simulateur, pas celui de vendeurs humains. | Master | [10b](Causalite-10b-ML-CATE-CFRNet-TARNet-Python.ipynb) |

## Approfondissements — master et recherche

**Autour de 10 : pour qui le traitement fonctionne-t-il ?** [Effets conditionnels, TARNet et CFRNet](Causalite-10b-ML-CATE-CFRNet-TARNet-Python.ipynb) compare des estimateurs sur des données dont l'effet est connu. La PEHE mesure l'erreur sur les effets individuels, pas l'erreur de prédiction du résultat observé. Sur IHDP (Hill, 2011 : 747 unités, 25 covariables), TARNet atteint une PEHE médiane de 0,281, mais ne conserve pas cet avantage sur les simulations ACIC. La leçon mesurée est la régularisation : sans dropout ni pénalité ℓ2, le même réseau finit dernier avec une PEHE de 1,484. Le classement dépend donc du monde où on l'éprouve.

**Du graphe à l'expérience.** Pour mettre une identification à l'épreuve, reprendre le palier 01 avec un chemin qui contourne le médiateur. Au palier 04, augmenter l'effectif ne suffit pas à distinguer des graphes observationnellement équivalents. Au palier 06, ajouter un effet direct de l'instrument sur la réponse : le logiciel peut encore rendre un nombre alors que l'interprétation causale ne tient plus.

### Travaux pratiques de Causalite-01

1. **Ajouter un second confondeur à la backdoor** — étendre l'ensemble d'ajustement à `{aptitude, motivation}`.
2. **Rompre le critère front-door** — ajouter un chemin direct qui contourne le médiateur et vérifier que l'identification front-door échoue.
3. **Comparer effet naïf et effet ajusté** — générer un nouveau jeu à effet vrai connu, mesurer l'écart dû au confondeur.
4. **Le compromis biais-variance du transport stratifié** — refaire le transport de la tâche 4 à K ∈ {3, 20, 100} strates : biais résiduel intra-strate à petit K, variance Monte-Carlo à grand K.

### Travaux pratiques de Causalite-03

1. **Le contrefactuel inverse** — pour un étudiant non traité à `V > 0`, estimer son `Y` sous `T := 1` et comparer à son observation : aurait-il gagné au mentorat ?
2. **La CATE par sous-groupe** — déduire de la série d'écarts individuels l'effet moyen pour `V > 0.5` vs `V < -0.5`, interpréter le signe.
3. **La méthode survit-elle au tirage ?** — re-générer le monde (`seed=7`), refitter, re-mesurer moyenne et écart-type des écarts : la structure doit survivre, pas les individus.

### Travaux pratiques de Causalite-06

1. **L'exclusion respectée vs VIOLEE** — générer un DGP `effet_direct_z = 0.5`, vérifier que `dowhy` identifie l'estimand `iv`, et constater l'écart entre `tau dowhy` et `TAU_VRAI = 2.0` ; verdict local NON_IDENTIFIABLE en mode terrain.
2. **Le F-stat comme garde-fou** — faire varier la taille d'échantillon `n ∈ {500, 1000, 2000, 5000}` sur instrument faible, observer comment le F-stat monte avec `n` (sans faire passer l'identification, qui reste structurelle).
3. **Verdict NON_IDENTIFIABLE sur DAG incomplet** — démontrer que `dowhy` identifie un estimand `iv` même quand l'exclusion est structurellement violée ; le verdict NON_IDENTIFIABLE doit venir du praticien, pas de `dowhy`.

### Travaux pratiques de Causalite-04

1. **L'ambiguïté ne se résout pas avec des données** — pour `n ∈ {500, 2000, 10000}`, constater que le CPDAG de PC garde `C–X` et `X–M` ambiguës : la classe de Markov est une borne structurelle, pas un problème de taille d'échantillon.
2. **`alpha` de PC, le compromis mesuré** — pour `alpha ∈ {0.2, 0.05, 0.01}` sur 5 seeds : arêtes parasites à `0.2`, v-structure perdue environ 1 seed sur 4 à `0.05` (mesuré sur ce monde), propre à `0.01` au prix de la puissance sur signaux faibles — il n'y a pas d'alpha gratuit.
3. **Diagnostiquer l'échec silencieux de LiNGAM** — sur 5 seeds gaussiens : DAG complet, faux et instable inter-seeds ; l'instabilité est le seul signal que l'hypothèse de non-gaussianité ne tient pas, la librairie reste muette.

### Travaux pratiques de Causalite-05

1. **Le rapport de forces** — renforcer le cache (`coef_u_*=1.8`) : la robustness value MONTE avec l'association observée (ça survit encore) ; affaiblir le signal (`tau=0.2, bruit_y=3.0`) : le RV passe sous le R² réel de U et le verdict bascule en ANNULABLE — c'est l'effet faible qu'on annule, pas le cache fort.
2. **L'E-value de l'IC et la taille d'échantillon** — à `n=10000` l'IC se resserre, sa borne s'éloigne de 1 et l'E-value de l'IC monte vers celui de l'estimé ; l'estimé ponctuel (biais constant de U) bouge à peine.
3. **Γ\* d'un effet plus faible** — reprendre le monde binaire à `b_x=0.2`, ré-apparier et recalculer Γ* : plus proche de 1 ; Γ\* mesure la solidité statistique face au pire des mondes, pas la vérité de l'effet.

### Travaux pratiques de Causalite-08

1. **Casser l'identité linéaire** — ajouter une interaction `A × W` dans l'équation de `Y` : l'identité simple `NDE − NIE = TE` ne tient plus, mais Lem 4.1 et Thm 4.2 (algébriques) tiennent à la précision machine.
2. **Str-DE-fair n'efface pas l'écart observé** — mettre le coefficient direct `A → Y` à zéro : NDE ≈ 0 mais la TV reste positive (canal indirect + spurieux) ; la règle des 80 % mesure l'écart, pas la discrimination directe.
3. **La règle des 80 % sur d'autres attributs du crédit allemand** — `foreign_worker` (groupe de référence minuscule : quelle confiance au ratio ?) et l'âge binarisé à 25 ans.

### Travaux pratiques de Causalite-10

1. **Le parseur de secours** — le parseur strict compte `None` toute réponse non conforme ; écrire un parseur fallback (DECLINE/REFUSE/NO d'un côté, ACCEPT/YES/OK de l'autre, trancher seulement si un seul camp apparaît) et mesurer le taux de récupération sur une copie perturbée du registre, puis le déplacement des β̂ — sur les runs committés la conformité du format est de 1,0 : il n'y a rien à récupérer, l'exercice consiste à fabriquer les pannes que le parseur doit absorber.
2. **Les coefficients standardisés** — calculer les β* (β × σ(cause) / σ(réponse)) des trois causes sur les sujets simulés : quelle cause domine la décision du vendeur ? (comparer les amplitudes plutôt que les unités).
3. **La sensibilité au libellé** — rejouer la cellule pilote avec une paraphrase du prompt (par ex. « Would you sell your mug at that price? », offre mécanique inchangée à 0.8 × budget, sinon le β vrai ne tient plus) et mesurer combien de réponses changent : c'est le bruit de mesure propre aux sujets simulés.

### Travaux pratiques de Causalite-10b

1. **Ablation de la pénalité MMD** — balayer α ∈ {0, 0.5, 1, 2} (3 graines) : sur cette réplique la PEHE croît avec α ; trouver un régime (petit α, noyau non linéaire) où CFRNet repasse devant TARNet.
2. **Ablation du tronc partagé** — définir un T-Learner neuronal (deux réseaux indépendants, un par bras, sans représentation commune) et mesurer sa PEHE contre TARNet sur les 5 graines.
3. **GANITE from scratch** — générateur de contrefactuels + discriminateur ; comparer sa PEHE à TARNet sur 3 graines.
4. **CEVAE simplifié** — VAE à facteur latent z portant confondeur et hétérogénéité ; ITE par différence de décodages à z échantillonné.
5. **Dragonnet** — tronc partagé + tête outcome + tête propension, régularisation ciblée ε ∈ {0, 0.1, 1} ; mesurer la PEHE par strate de propension.

## Installation — pratique

Les carnets utilisent Python ; les paliers 04 à 07 déclarent le noyau `coursia-ml-training`, les autres `python3`. Voir les [dépendances de la série](../requirements.txt). `dowhy` identifie une expression à partir du graphe, l'estime puis propose des tests de réfutation ; `causal-learn` intervient dans la découverte de structure. Les réponses déjà enregistrées au palier 10 se distinguent d'une nouvelle campagne, qui nécessite un serveur de génération.

## Pour aller plus loin — recherche

Comparer [l'intervention par graphe de facteurs](../Infer/Infer-05-Causal-Inference.ipynb), [l'opérateur `pm.do`](../PyMC/PyMC-05-Causal-Inference.ipynb) et [le contrefactuel logique](../../SymbolicAI/Tweety/Tweety-11-Causal-Python.ipynb). L'[émergence causale](../../IIT/ICT-Series/ICT-04-CausalEmergence-Python.ipynb) pose une question différente : à quelle échelle décrire le système pour rendre ses transitions plus informatives ?
