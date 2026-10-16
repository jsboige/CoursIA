# Parcours — IA, société et responsabilité

> Item 2 du front vivant de l'EPIC [Réimaginer les parcours d'apprentissage](https://github.com/jsboige/CoursIA/issues/13844) (tri du 26/09). Parcours narratif composé **exclusivement à partir de carnets existants sur `main`** — chaque étape renvoie au carnat réel, avec son fait saillant mesuré dans sa propre sortie. Modèle de structure : le parcours IA hybride (item 1, PR #20849) et « Parcours alternatifs » du [README GameTheory](../../MyIA.AI.Notebooks/GameTheory/README.md).

## La thèse du parcours

Un système d'IA n'est pas seulement une machine à prédire : c'est un **acteur social**. Il note des personnes (2.5c), décide à leur place (2.12, 2.13), doit rendre compte de ses décisions (2.14), touche des données personnelles (2.15), agrège des préférences (choix social), participe à des délibérations (argumentation) — et il peut être surveillé, ou trahi (oversight). Ce parcours traverse le dépôt en cinq actes pour répondre à une seule question : **que signifie rendre compte d'un système qui décide ?**

## Profil

- **Pour qui** : étudiant ou praticien qui veut dépasser « le modèle est performant » et interroger ce qu'il fait *aux personnes* ; profil audit/gouvernance autant que recherche.
- **Prérequis** : socle ML du cours 02 (2.1 Workflow, 2.3 régression logistique) pour les actes 1-2 ; **aucun** prérequis ML pour les actes 3-4 (choix social et argumentation sont autours, pur Python stdlib) ; l'acte 5 suppose le vocabulaire LLM de la série GenAI.
- **Format** : 16 étapes en 5 actes. Chaque carnet est exécutable et committé avec ses sorties ; les durées ne sont citées que lorsqu'elles sont publiées par la série d'origine.

## Acte 1 — Le modèle peut-il être juste ?

Ce que le modèle fait à des groupes de personnes, mesuré sur ses propres sorties.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 1 | [2.5c-Equite-Sous-Groupes](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb) | — | L'incompatibilité des trois métriques d'équité sous prévalences différentes (Chouldechova) : **96,4 % d'accuracy globale coexiste avec deux groupes à [0,977–0,995] et [0,922–0,957]** ; le post-traitement par seuils par groupe (Hardt) comme compromis documenté |
| 2 | [2.12-Donnees-Desequilibrees](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.12-Donnees-Desequilibrees.ipynb) | — | **La métrique qui ment** : sur une classe à ~3 % (fraude, défaut), la ROC flatte et seule la courbe Precision-Recall rend l'arbitrage visible ; le seuil honnête minimise le **coût attendu**, pas l'accuracy |
| 3 | [2.13-Analyse-Erreurs](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.13-Analyse-Erreurs.ipynb) | — | **La poche invisible** : 67,6 % d'erreur sur ~5 % de la population, cachée dans un score global correct (82,2 %) — le geste du praticien face aux tranches délaissées |
| 4 | [2.14-Explicabilite-SHAP-LIME-Contrefactuels](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.14-Explicabilite-SHAP-LIME-Contrefactuels.ipynb) | — | Répondre de ses décisions : SHAP, LIME et le contrefactuel (« si ce champ avait différé, la décision aurait changé ») comme matériaux d'audit |

**Fil de l'acte** : la performance globale masque l'injustice locale (1-3) ; l'explicabilité est le début de la redevabilité (4).

## Acte 2 — La donnée comme responsabilité

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 5 | [2.15-Donnee-Comme-Responsabilite](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.15-Donnee-Comme-Responsabilite-Python.ipynb) | — | **L'attaque d'inférence d'appartenance menée pour de vrai** : la forêt qui mémorise laisse fuir ses données (avantage d'attaque +0,439, AUC 0,719) quand la régression régularisée retombe à +0,057 ; puis confidentialité différentielle — mécanisme de Laplace, DP-SGD écrit à la main, confrontation au SOTA diffprivlib — et datasheet/model card (Gebru 2018, Mitchell 2019) |

**Fil de l'acte** : la protection se mesure, elle ne se déclare pas — la première protection est la généralisation elle-même.

## Acte 3 — Décider à plusieurs : le choix social

L'agrégation de préférences est le cœur politique de tout système qui « tranche ». Théorèmes d'impossibilité, puis mécanismes concrets — pur Python, sans prérequis ML.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 6 | [SC-01 : Théorème d'Arrow](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/01-Arrow-Impossibility-Theorem.ipynb) | 45 min | **Aucune règle d'agrégation à ≥ 3 options n'est simultanément non-dictatoriale, unanime et indépendante aux alternatives non pertinentes** — preuve formelle et simulation |
| 7 | [SC-05 : Gibbard-Satterthwaite](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/05-Gibbard-Satterthwaite.ipynb) | 30 min | **Toute règle de vote non triviale est manipulable** — la manipulation comme témoin structurel, pas comme accident |
| 8 | [SC-03 : Méthodes de vote](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/03-Voting-Methods.ipynb) | 35 min | Condorcet, Borda, Copeland : **la même société élit des gagnants différents selon la règle** — le paradoxe devient un levier de conception |
| 9 | [SC-06 : Möbius et pouvoir](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/06-Mobius-Aggregation-Pouvoir-Manipulation.ipynb) | 40 min | **Poids ≠ pouvoir** : dividendes de Harsanyi sur le treillis des coalitions, indice de pouvoir mesuré, manipulation pondérée |

**Fil de l'acte** : il n'existe pas d'agrégation neutre — choisir une règle de vote est un choix politique, et cela se démontre.

## Acte 4 — Argumenter, délibérer, détecter la manipulation

Du débat informel à la sémantique formelle : comment une position survit-elle à la confrontation ?

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 10 | [Argumentation-01 : Modèle de Toulmin](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-01-Toulmin-Model-Python.ipynb) | 30 min | Les 6 composants d'un argument (claim/data/warrant/backing/qualifier/rebuttal), audit de complétude, **pont computationnel vers Dung** : les rebuttals deviennent des attaques |
| 11 | [Argumentation-02 : Détection de sophismes](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-02-Fallacies-Detection-Python.ipynb) | — | Les sophismes détectés par règles — le versant symbolique |
| 12 | [FallacyDetection-01 : Taxonomie](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/01_taxonomy_intro.ipynb) | — | Le versant GenAI du même problème : taxonomies académiques vs taxonomy Argumentum, ce que le NLP sait (et ne sait pas) reconnaître |
| 13 | [Argumentation-03 : Sémantiques de Dung](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-03-Dung-AF-Semantics-Python.ipynb) | 35 min | Grounded, preferred, stable **reconstruites de zéro** sur un cas où les trois divergent : quel claim survit au débat dépend de la sémantique choisie |
| 14 | [Gouvernance Multi-Agents](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Gouvernance_Multi_Agents.ipynb) | 35 min | **Agréger des positions d'agents** : scrutins sur les mêmes préférences, justice de Gini, bruit byzantin vs choix social formel — la jonction des actes 3 et 4 |

**Fil de l'acte** : la délibération a une mécanique — structure (Toulmin), pathologies (sophismes), survie (Dung), agrégation (gouvernance).

## Acte 5 — Surveiller ce qu'on déploie : l'oversight

Le déploiement n'est pas la fin de la responsabilité. La série [GenAI/Security/Oversight](../../MyIA.AI.Notebooks/GenAI/Security/Oversight/) (issue [#16754](https://github.com/jsboige/CoursIA/issues/16754)) mesure ce que « surveiller un système » veut dire.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 15 | [Backdoor-Code-From-Scratch](../../MyIA.AI.Notebooks/GenAI/Security/Oversight/Backdoor-Code-From-Scratch.ipynb) | — | **La porte dérobée construite pour être comprise** : un déclencheur caché dans le code, et ce qu'il faut pour le détecter |
| 16 | [Oversight-Scaling-Laws-Statistics](../../MyIA.AI.Notebooks/GenAI/Security/Oversight/Oversight-Scaling-Laws-Statistics.ipynb) et [Wargames](../../MyIA.AI.Notebooks/GenAI/Security/Oversight/Oversight-Scaling-Laws-Wargames.ipynb) | — | **Les statistiques d'oversight** : la couverture de surveillance suit-elle une loi d'échelle ? Wargames : l'adversaire réagit à la surveillance — mesurer, pas supposer |

**Fil de l'acte** : surveiller est une discipline quantitative — l'oversight se démontre par des mesures, pas par des intentions.

## Prolongements (hors parcours)

- [2.5d-Derive-Distribution-Deploiement](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5d-Derive-Distribution-Deploiement.ipynb) — la responsabilité continue en production : trois dérives construites, trois détecteurs, deux corrections.
- [SC-01b : Choix social formel en Lean](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/01b-Lean-SocialChoice-Formal.ipynb) (80 min) — Arrow, Sen, électeur médian certifiés.
- [Argumentation-03b : AF à valeurs](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-03b-Value-Based-AF-Python.ipynb) et [03c : ranking](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-03c-Ranking-Semantics-Python.ipynb) (35 min chacun) — l'audience et la force changent le verdict.
- [FallacyDetection 02-05](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/) — paysage des datasets, écart de couverture taxonomique, matrice N×M, construction de dataset équilibré.
- [Argumentation-05 : vérification formelle avec Tweety](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-05-Formal-Verification-Python.ipynb) (45 min) — le solveur réel JVM, mode fail-loud.

## Pourquoi ce parcours existe

Le tri du 26/09 (analyse externe, coordination ai-01) constatait que « IA, société et responsabilité » n'était « suivi par aucun parcours de bout en bout » alors que **tous les ingrédients existent** — l'issue #17984 (confidentialité différentielle, fiches données/modèle) a depuis été livrée dans [2.15](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.15-Donnee-Comme-Responsabilite-Python.ipynb), fermant le dernier trou mesuré. Ce parcours ne crée aucun contenu : il **ordonne** l'existant en un chemin d'apprenant avec une thèse.

*Item 2 du front vivant de [#13844](https://github.com/jsboige/CoursIA/issues/13844). La ligne de ce parcours dans la table de `PARCOURS.md` est ajoutée dans une PR distincte, après merge de la PR #20849 qui porte la ligne du parcours IA hybride (paths claimés séparément pour éviter la collision).*
