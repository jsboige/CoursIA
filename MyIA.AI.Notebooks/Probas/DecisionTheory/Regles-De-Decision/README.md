# Règles de décision — corrélation, causalité et procédure

[← Série Probas](../../README.md) | [↑ Arc Théorie de la Décision](../README.md) | [Pont causal `Causal-Bridges`](../Causal-Bridges/README.md)

Cette sous-série étudie une question qui survient après le calcul de l'utilité espérée : **quelle distribution de probabilité une règle de décision doit-elle utiliser ?** Observer qu'un acte est associé à un bon résultat, provoquer cet acte et choisir la procédure qui le produit sont trois opérations différentes. Les confondre fait diverger les recommandations précisément dans les problèmes où l'acte renseigne sur l'agent ou sur son environnement.

**Prérequis** : probabilités conditionnelles et espérance, notions de graphes orientés acycliques. Le carnet introduit les modèles causaux structurels nécessaires ; la lecture de [CausalBridges-01](../Causal-Bridges/CausalBridges-01-Do-Calculus.ipynb) donne un complément sur le do-calculus.

**Stack** : Python 3 (kernel `python3`), `numpy`, `pandas`, `matplotlib` et [`dowhy`](https://www.pywhy.org/dowhy/). Les comparaisons de règles reposent sur une énumération exacte de petits modèles causaux finis ; `dowhy` fournit l'estimation causale sur les échantillons simulés. Aucun GPU, service distant ou secret n'est requis.

## Contenu

| Notebook | Durée | Concepts |
|---|---|---|
| [ReglesDeDecision-01 — EDT, CDT, CCDT et UDT](ReglesDeDecision-01-EDT-CDT-CCDT-UDT.ipynb) | ~65 min | Conditionnement $P(O\mid A)$ contre intervention $P(O\mid do(A))$ ; mondes du tabagisme ordinaire et de Fisher ; estimation `dowhy` ; Newcomb ; opérationnalisation de la CCDT d'Edgington et condition d'adéquation ; cas d'Egan ; intervention sur une procédure ; problème « 2TDT-1CDT » de Dai |

## Ce que le carnet démontre

Le carnet ne se contente pas d'opposer des slogans philosophiques : chaque règle est calculée sur **le même modèle**, avec des sorties numériques reproductibles.

1. **Association et intervention ne sont pas interchangeables.** Les mondes ordinaire et de Fisher ont les mêmes associations tabac–cancer, mais des effets interventionnels différents. `dowhy`, muni du graphe et d'un ajustement backdoor, distingue les deux échantillons.
2. **Newcomb sépare EDT et CDT.** Le contenu de la boîte opaque est lié à l'acte sans en être causé : EDT privilégie une boîte, CDT deux boîtes à toutes les fiabilités testées du prédicteur.
3. **La CCDT est testée, pas seulement paraphrasée.** L'implémentation reproduit les quatre valeurs du cas du tabagisme publiées par Mohajeri. Sur les modèles explicitement adéquats étudiés, elle coïncide avec EDT ; Newcomb sert de témoin négatif lorsque la conséquence ne contient aucune composante causée par l'acte.
4. **Une procédure n'est pas un acte isolé.** Dans le dilemme du prisonnier entre deux instances corrélées, conditionner sur son acte, intervenir sur cet acte et intervenir sur la procédure commune donnent trois réponses distinctes.
5. **Le résultat de population de Dai est conditionnel.** Sans reconnaissance des agents CDT, ceux-ci obtiennent un gain supérieur dans la simulation. Le carnet mesure aussi la frontière où la coopération conditionnelle inverse cet avantage, plutôt que de conclure que « CDT gagne toujours ».

## Place dans l'arc

Les arcs [DecInfer](../DecInfer/README.md) et [DecPyMC](../DecPyMC/README.md) montrent comment maximiser une utilité espérée une fois le modèle de décision posé. [Causal-Bridges](../Causal-Bridges/README.md) montre comment identifier et estimer un effet causal. Cette sous-série traite le chaînon intermédiaire : **le choix du conditionnement ou de l'intervention qui définit la valeur d'un acte**.

Elle prolonge également la piste bibliographique de l'Epic [#14468](https://github.com/jsboige/CoursIA/issues/14468) : les affirmations reprises des publications sont distinguées des paramétrisations pédagogiques et des résultats calculés dans le carnet.

## Exercices

Les trois exercices du carnet sont des stubs exécutables, sans erreur volontaire :

1. **Chirurgie causale** — supprimer l'arête causale tabac–cancer dans le monde ordinaire et comparer les recommandations EDT/CDT avant et après.
2. **Description des conséquences** — tester plusieurs granularités de conséquences dans Newcomb et observer la condition d'adéquation de la CCDT.
3. **Évolution de population** — faire varier la part d'agents CDT au fil des générations selon leurs gains relatifs, puis examiner l'effet de la reconnaissance.

## Limites

- La coïncidence CCDT–EDT est vérifiée pour l'opérationnalisation et la famille de modèles du carnet ; le carnet ne prétend pas fournir une preuve universelle.
- La « corrélation logique » de l'exemple UDT est représentée par une procédure commune dans un modèle causal explicite, sans prétendre formaliser toute la théorie philosophique.
- Le succès reproductif d'un type d'agent dans une population ne constitue pas, à lui seul, un critère normatif de rationalité.

## Références

- Dai, W. (2023). *Timeless Decision Theory and Functional Decision Theory*, problème 4 « 2TDT-1CDT ».
- Mohajeri, M. (preprint 2023 ; publié 2024). *Conditional causal decision theory reduces to evidential decision theory*, Analytic Philosophy 65, 93-106.
- Egan, A. (2007). *Some Counterexamples to Causal Decision Theory*.
- Pearl, J. (2009). *Causality: Models, Reasoning, and Inference* (2ᵉ éd.).

Les références bibliographiques détaillées et la portée exacte de chaque attribution figurent dans le carnet. Les publications restent archivées hors dépôt conformément à la politique de bibliographie du projet.
