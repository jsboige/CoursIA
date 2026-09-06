# DataScienceWithAgents - Data Science Python avec Agents IA

[← ML (série parente)](../README.md) | [ML.NET (C#) →](../ML.Net/README.md) | [Track2-GoogleADK (Google ADK) →](Track2-GoogleADK/README.md)

Formation complète en Data Science Python avec intégration d'agents IA. Combine les fondamentaux NumPy/Pandas avec deux tracks complémentaires : LangChain (3 jours) et Google ADK (4 jours).

Au-delà des bibliothèques classiques, cette formation explore un changement de paradigme : passer de *l'écriture* de code data science à *l'orchestration* d'**agents LLM** qui le produisent et l'exécutent. Après les fondations NumPy/Pandas, le track **LangChain** apprend à construire des agents capables d'interroger un DataFrame, de nettoyer un jeu de données ou de scorer des candidatures ; le track **Google ADK** monte en puissance avec des systèmes multi-agents (boucles planner-coder, frameworks DS-STAR / MLE-STAR) jusqu'à concourir sur des compétitions Kaggle. L'enjeu pédagogique n'est pas seulement technique : il s'agit de comprendre *quand* un agent autonome accélère réellement le travail d'analyse, et *comment* l'encadrer (outils, validation, garde-fous).

## Pourquoi cette série

Le Data Science traditionnel suit un workflow manuel : charger, nettoyer, transformer, modéliser, évaluer. Cette série introduit un **changement de paradigme** : orchestrer des agents LLM qui automatisent ce workflow. L'objectif n'est pas de remplacer le data scientist, mais de comprendre *quand* un agent accélère réellement le travail et *comment* l'encadrer.

La formation couvre deux stacks complémentaires :

| Aspect | Track LangChain (Days 1-3) | Track Google ADK (Days 4-7) |
|--------|---------------------------|----------------------------|
| **Approche** | Agent unique avec tools | Systèmes multi-agents |
| **Framework** | LangChain + OpenAI | Google ADK + LiteLLM |
| **Complexité** | Chains, outils simples | Boucles planner-coder, DS-STAR |
| **Application** | RFP, CV screening, data wrangling | Kaggle, BigQuery, déploiement |
| **Providers** | OpenAI uniquement | Multi-provider (Gemini, vLLM, OpenAI) |

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 57 (7 LangChain + 14 ADK + 2 fondations Python + 21 fondations ML + 10 deep learning + 3 vision) |
| Kernel | Python 3.11+ |
| Durée totale | ~7 jours |

## Public cible

- Analystes de données souhaitant intégrer l'IA
- Data scientists intéressés par les agents
- Développeurs Python intermédiaires

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un agent LLM avec LangChain (tools, chains, memory) et l'appliquer à des tâches data science concrètes
2. **Évaluer** quand un agent autonome accélère le travail d'analyse vs une approche manuelle
3. **Orchestrer** des systèmes multi-agents avec Google ADK (planner-coder, DS-STAR, MLE-STAR)
4. **Configurer** un pipeline multi-provider (Gemini, OpenAI, vLLM local) via LiteLLM
5. **Déployer** un agent data science en production (BigQuery, BQML, GCP)

## Quel parcours choisir

### Parcours analyste data science (~3 jours)

Labs 1-7 en séquence. Acquérir les bases Pandas, puis construire des agents LangChain pour automatiser l'analyse de données.

1. Lab 1 -> révision Pandas/Matplotlib/Scikit-Learn
2. Labs 2-3 -> agents documentaires (RFP, CV)
3. Labs 4-7 -> data wrangling + agents d'analyse

### Parcours ingénieur ML agentique (~4 jours)

Labs 8-17 en séquence. Monter en complexité avec les frameworks Google ADK et les systèmes multi-agents.

1. Labs 8-9 -> architecture ADK, premier agent
2. Labs 10-12 -> DS-STAR (data science autonome)
3. Labs 13-15 -> MLE-STAR (Kaggle, optimisation)
4. Labs 16-17 -> production (BigQuery, projet final)

### Parcours complet (~7 jours)

Tous les labs en séquence, des fondations NumPy/Pandas jusqu'au déploiement GCP.

### Parcours rapide (~1 jour)

Labs 1 + 6 + 8. Découvrir le pipeline data science, construire un premier agent LangChain, puis un premier agent ADK. Les trois labs les plus représentatifs pour une première prise en main.

## Structure

```
DataScienceWithAgents/
├── 01-PythonForDataScience/    # Fondations Python (2 notebooks)
│   └── notebooks/
│       ├── 1.2-NumPy.ipynb
│       └── 1.3-Pandas.ipynb
│
├── 02-ML-Cours/                # Fondations ML canoniques (21 notebooks)
│   ├── 2.1-Workflow-ML.ipynb
│   ├── 2.2-Descente-de-gradient.ipynb
│   ├── 2.3-Regression-lineaire-logistique.ipynb
│   ├── 2.3b-Naive-Bayes-Generatif.ipynb
│   ├── 2.3c-Regression-Grande-Dimension.ipynb
│   ├── 2.3d-Modele-Gaussien-LDA-QDA.ipynb
│   ├── 2.4-Arbres-Forets-Ensembles.ipynb
│   ├── 2.5-Biais-Variance-CV-ROC.ipynb
│   ├── 2.5b-Calibration-Probabilites.ipynb
│   ├── 2.5c-Equite-Sous-Groupes.ipynb
│   ├── 2.6-Clustering-KMeans-PCA.ipynb
│   ├── 2.7-Modeles-Non-Parametriques.ipynb
│   ├── 2.8-Theorie-PAC.ipynb
│   ├── 2.8b-Theorie-PAC-Lean.ipynb
│   ├── 2.8c-Borne-Temoin-Concentration.ipynb
│   ├── 2.8d-Lean-Novikoff-Convergence.ipynb
│   ├── 2.9-Grokking-Generalisation.ipynb
│   ├── 2.10-Optimisation-Hyperparametres.ipynb
│   ├── 2.11-Regularisation-Sparse-LASSO.ipynb
│   ├── 2.12-Donnees-Desequilibrees.ipynb
│   └── 2.13-Analyse-Erreurs.ipynb
│
├── 03-DeepLearning/            # Deep learning from scratch (10 notebooks)
│   ├── 3.0-Theorie-Information.ipynb
│   ├── 3.1-Retropropagation.ipynb
│   ├── 3.2-Optimisateurs.ipynb
│   ├── 3.3-Regularisation.ipynb
│   ├── 3.4-Attention-Transformer-From-Scratch.ipynb
│   ├── 3.5-Phenomenes-de-Generalisation.ipynb
│   ├── 3.6-Modeles-Generatifs.ipynb
│   ├── 3.6b-Modeles-Generatifs-PyTorch.ipynb
│   ├── 3.7-Distillation-Maitre-Eleve.ipynb
│   └── 3.8-Representations-Contrastives.ipynb
│
│
├── 04-Vision/                # Vision par ordinateur : du neurone convolutif au transfer learning (3 notebooks)
│   ├── 4.1-Conv-NumPy-Torch-Allclose.ipynb
│   ├── 4.2-ConvNet-Profonde-Residuelles.ipynb
│   └── 4.3-TransferLearning-ResNet.ipynb
│
├── Track1-LangChain/ # Track LangChain (7 labs)
│   ├── Day1-Foundations/Labs/              # Revision
│   ├── Day2-Document-Agents/Labs/              # Agents RFP et CV
│   └── Day3-Data-Agents/Labs/              # Data + Agents
│
└── Track2-GoogleADK/         # Track Google ADK (14 labs)
    ├── Day4-Foundations/       # Introduction ADK
    ├── Day5-DS-Star/           # Data Science autonome
    ├── Day6-MLE-Star/          # ML Engineering
    └── Day7-Production/        # Integration GCP
```

## Fondations (01-PythonForDataScience)

| Notebook | Contenu | Durée |
|----------|---------|-------|
| [1.2-NumPy](01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | Arrays, opérations, vectorisation | 45 min |
| [1.3-Pandas](01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | DataFrames, filtrage, groupby | 60 min |

## Fondations ML (02-ML-Cours)

Le socle machine learning canonique avec scikit-learn, posé à la main entre les fondations NumPy/Pandas et les labs agentic — là où scikit-learn n'apparaissait jusqu'ici que comme une séquence magique non expliquée. Vingt-et-un notebooks (workflow, descente de gradient, régression linéaire/logistique complétée par le pont génératif Naive Bayes et la régression en grande dimension PCR/PLS/Ridge, arbres et ensembles, biais-variance/CV/ROC, calibration des probabilités, équité par sous-groupes, clustering/ACP, SVM à noyau/k-NN, théorie PAC/dimension VC et ses trois compagnons formel/concentration/Perceptron, un épilogue 2.9 grokking, puis trois chapitres de praticien — optimisation d'hyperparamètres, régularisation sparse LASSO/ElasticNet, classes déséquilibrées, et analyse d'erreurs), chacun rendant visible un concept-phare et ancrant les articles fondateurs.

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [2.1-Workflow-ML](02-ML-Cours/2.1-Workflow-ML.ipynb) | split → fit → predict → évaluer | surapprentissage rendu visible |
| [2.2-Descente-de-gradient](02-ML-Cours/2.2-Descente-de-gradient.ipynb) | ouvrir la boîte noire de `fit()` | 3 learning rates (lent / bon / divergeant) |
| [2.3-Regression-lineaire-logistique](02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb) | OLS vs MLE | droite vs sigmoïde |
| [2.3b-Naive-Bayes-Generatif](02-ML-Cours/2.3b-Naive-Bayes-Generatif.ipynb) | *Pont génératif* — classifieur naïf de Bayes (Bernoulli, multinomial, Gaussien), hypothèse d'indépendance conditionnelle | **L'indépendance qui décide** : la frontière est inherited du modèle conjoint, pas apprise |
| [2.3c-Regression-Grande-Dimension](02-ML-Cours/2.3c-Regression-Grande-Dimension.ipynb) | p >> n : Ridge (L2), PCR (ACP) et PLS (supervisée) | **Var ≠ valeur prédictive** : la PLS trouve en 5 composantes ce que la PCR paie à 44 |
| [2.3d-Modele-Gaussien-LDA-QDA](02-ML-Cours/2.3d-Modele-Gaussien-LDA-QDA.ipynb) | Analyse discriminante linéaire vs quadratique | **L'hypothèse de covariance décide la frontière** : partagée → droite (LDA), propre → conique (QDA) |
| [2.4-Arbres-Forets-Ensembles](02-ML-Cours/2.4-Arbres-Forets-Ensembles.ipynb) | DecisionTree, RandomForest, GradientBoosting | réduction de variance |
| [2.5-Biais-Variance-CV-ROC](02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb) | biais-variance, validation croisée, ROC/AUC | coût du seuil de décision |
| [2.5b-Calibration-Probabilites](02-ML-Cours/2.5b-Calibration-Probabilites.ipynb) | calibration des probabilités : reliability diagram, ECE | pourquoi 0.87 n'est pas 87 % de chances |
| [2.5c-Equite-Sous-Groupes](02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb) | équité par sous-groupe : parité démographique, equalized odds, post-traitement par seuils (Hardt) | **L'accuracy globale ne suffit pas** : 96,4 % global coexiste avec des écarts de groupe [0,92–1,00] |
| [2.6-Clustering-KMeans-PCA](02-ML-Cours/2.6-Clustering-KMeans-PCA.ipynb) | non supervisé : KMeans + ACP | structure retrouvée sans étiquettes |
| [2.7-Modeles-Non-Parametriques](02-ML-Cours/2.7-Modeles-Non-Parametriques.ipynb) | SVM à noyau et k plus proches voisins | kernel trick (linéaire vs RBF) |
| [2.8-Theorie-PAC](02-ML-Cours/2.8-Theorie-PAC.ipynb) | théorie PAC : sample complexity, dimension VC | la borne PAC prédit l'empirique |
| [2.8b-Theorie-PAC-Lean](02-ML-Cours/2.8b-Theorie-PAC-Lean.ipynb) | *Compagnon Lean* (kernel `lean4-wsl`) — la même borne PAC, démontrée | ce que 2.8 constate, le lake le prouve |
| [2.8c-Borne-Temoin-Concentration](02-ML-Cours/2.8c-Borne-Temoin-Concentration.ipynb) | *Carte transversale + illustrations Python* — Sections 1--3 (reconstruction de la borne, témoin extrémal, Hoeffding bilatérale) sous kernel `coursia-ml-training` | qui porte quoi, et la mesure numérique Python exécutée |
| [2.8d-Lean-Novikoff-Convergence](02-ML-Cours/2.8d-Lean-Novikoff-Convergence.ipynb) | *Compagnon Lean* (kernel `lean4-wsl`) — la moitié Perceptron du lake : Novikoff `n·γ² ≤ R²`, ses deux lemmes, son témoin de saturation | **Le théorème interrogé en direct** : `#check` + `#print axioms` depuis le lake, dynamique rejouée sur entiers |
| [2.9-Grokking-Generalisation](02-ML-Cours/2.9-Grokking-Generalisation.ipynb) | *Épilogue* — grokking : la généralisation qui arrive en retard (premier réseau de neurones) | **L'horloge cachée** : embeddings rangés en cercle après le grok (ACP + Fourier) |
| [2.10-Optimisation-Hyperparametres](02-ML-Cours/2.10-Optimisation-Hyperparametres.ipynb) | méthodologie du réglage : grille, hasard, bayésien (TPE) — et quand s'arrêter | le critère d'arrêt économise la moitié des essais |
| [2.11-Regularisation-Sparse-LASSO](02-ML-Cours/2.11-Regularisation-Sparse-LASSO.ipynb) | *Régularisation sparse* — LASSO (L1, polyèdre) vs Ridge (L2, boule), coord descent, sélection de λ, ElasticNet sur features corrélées | **la géométrie décide** : polyèdre L1 → sparsity, boule L2 → shrink ; sur ρ > 0.7, ElasticNet stabilise |
| [2.12-Donnees-Desequilibrees](02-ML-Cours/2.12-Donnees-Desequilibrees.ipynb) | *Classes déséquilibrées* — la métrique qui ment (accuracy vs PR), rééchantillonnage, seuillage par coût | **La courbe PR dit la vérité** : sur ~3 % de positifs, la ROC flatte — seule l'average precision rend l'arbitrage visible |
| [2.13-Analyse-Erreurs](02-ML-Cours/2.13-Analyse-Erreurs.ipynb) | le geste du praticien : diagnostiquer un modèle entraîné (tranches, worst-k) | la poche invisible : 67.6% d'erreur sous un score global correct |

Documentation complète : [02-ML-Cours/README.md](02-ML-Cours/README.md)

## Deep Learning (03-DeepLearning)

Le prolongement direct du socle : là où [2.2](02-ML-Cours/2.2-Descente-de-gradient.ipynb) ouvre `fit()` sur une droite et [2.9](02-ML-Cours/2.9-Grokking-Generalisation.ipynb) entraîne un réseau PyTorch en boîte noire, cette série écrit la mécanique intermédiaire **à la main** — chaque mécanisme implémenté en NumPy pur, vérifié (gradient numérique, parité pas-à-pas avec PyTorch), puis relié à l'API `torch` que consomment les séries RL/PostTraining.

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [3.0-Theorie-Information](03-DeepLearning/3.0-Theorie-Information.ipynb) | Entropie, cross-entropy et KL from scratch sur texte français, MSE vs CE sur classifieur, température softmax, pont DPO/GRPO | **La loss qui fait apprendre** : pourquoi la CE et pas la MSE ; KL comme mesure de décalage entre distributions |
| [3.1-Retropropagation](03-DeepLearning/3.1-Retropropagation.ipynb) | Le MLP et la rétropropagation à la main (NumPy pur, sans autograd) | **Le gradient vérifié** (différence finie 1,3e-11 ; parité exacte avec PyTorch ; init nulle = gradient nul) |
| [3.2-Optimisateurs](03-DeepLearning/3.2-Optimisateurs.ipynb) | Momentum, Adagrad, RMSProp, Adam et schedules, écrits puis validés pas à pas contre `torch.optim` | **La parité exacte** (5 mises à jour identiques à ≤2,2e-16 ; Beale 5 trajectoires ; MLP 3 graines ; schedules : coût en déterministe, gain en bruité) |
| [3.3-Regularisation](03-DeepLearning/3.3-Regularisation.ipynb) | Dropout, weight decay et early stopping écrits à la main sur un MLP construit pour surapprendre (17 000 paramètres, 100 points, 12 étiquettes fausses) | **Corriger la variance sans changer le modèle** : trois remèdes appliqués au même surapprentissage fabriqué |
| [3.4-Attention-Transformer-From-Scratch](03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb) | De l'attention mono-tête lisible sur l'inversion de séquence au mini-GPT de 1,25 M entraîné dans le notebook | **L'attention jusqu'au bout, sur CPU** : attention + masque causal + multi-têtes + bloc pré-norme, mini-GPT char-level (117 s, *Le Horla*) |
| [3.5-Phenomenes-de-Generalisation](03-DeepLearning/3.5-Phenomenes-de-Generalisation.ipynb) | Grokking et double descente reproduits en NumPy pur (MLP à embeddings + Adam à la main), confrontés à la borne PAC du 2.8 | **Le phénomène sans la boîte noire** : mémorisation → transition abrupte, et le W de la double descente (pic au seuil M ≈ n, 20 graines) |
| [3.6-Modeles-Generatifs](03-DeepLearning/3.6-Modeles-Generatifs.ipynb) | VAE, GAN et diffusion (DDPM) écrits en NumPy pur, même cible (huit modes sur un cercle), même budget, face à une baseline GMM | **Trois objectifs, trois échecs** : VAE couvre mais moyenne, GAN s'effondre, diffusion raffine au prix de 100 passes |
| [3.6b-Modeles-Generatifs-PyTorch](03-DeepLearning/3.6b-Modeles-Generatifs-PyTorch.ipynb) | *Versant framework* du 3.6 : VAE, GAN et DDPM entraînés sur cible 2D à 4 modes (PyTorch CPU) | **Le compromis qualité/diversité** : 4 mécanismes sur mêmes métriques, verdict nuancé, pas de « gagnant » unique |
| [3.7-Distillation-Maitre-Eleve](03-DeepLearning/3.7-Distillation-Maitre-Eleve.ipynb) | Distillation teacher/student : maître entraîné distille son savoir vers un élève ~9× plus petit | **Le facteur T² vérifié** : la KL brute chute en ~1/T², la KL scalée reste constante ; verdict INCONCLUSIVE au seuil strict |
| [3.8-Representations-Contrastives](03-DeepLearning/3.8-Representations-Contrastives.ipynb) | Pré-entraînement contrastif moderne : vues continues, encodeur MLP et loss InfoNCE from scratch, pont vers skip-gram | **Apprendre des représentations sans étiquettes** : deux vues attirent leurs embeddings, les autres repoussent |

Documentation complète : [03-DeepLearning/README.md](03-DeepLearning/README.md)


## Vision par ordinateur (04-Vision)

[`03-DeepLearning`](#deep-learning-03-deeplearning) a ouvert la rétropropagation sur des **vecteurs** tabulaires (MLP, gradient vérifié, parité NumPy ↔ torch). Le passage à l'image demande une primitive nouvelle : le neurone **convolutif**, qui partage ses poids spatialement. Cette série reprend la **même discipline** (from scratch PUIS framework, parité epsilon machine) et l'applique à la convolution, l'empilement profond, et au skip-connection qui rend les réseaux entraînables.

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [4.1-Conv-NumPy-Torch-Allclose](04-Vision/4.1-Conv-NumPy-Torch-Allclose.ipynb) | Conv2d NumPy pur (single + multi-canal), gradient vérifié par différence finie, parité epsilon machine avec `torch.nn.Conv2d`, pooling et invariance par translation | **La convolution n'est pas magique** : un produit scalaire local, partagé spatialement, parité NumPy/torch à epsilon machine |
| [4.2-ConvNet-Profonde-Residuelles](04-Vision/4.2-ConvNet-Profonde-Residuelles.ipynb) | 20 conv2d empilées nues (effondrement du gradient), skip naïf (gradient réparé mais passe avant qui dérive), bloc pré-norme (les deux réparés), même protocole transposé à 20 blocs d'attention, puis accuracy CIFAR-10 sur 3 graines | **Le skip-connection n'est pas un détail architectural** : c'est le mécanisme qui rend les réseaux profonds entraînables |
| [4.3-TransferLearning-ResNet](04-Vision/4.3-TransferLearning-ResNet.ipynb) | ResNet18 pré-entraîné ImageNet, tête greffée (5 130 params entraînables sur 11,18 M), gelé vs fine-tuné sur EuroSAT (Sentinel-2, 10 classes, 3 graines appariées + test de permutation des signes) | **Le feature extractor pré-entraîné est réutilisable — et le prix de ne pas l'adapter se mesure** : gelé ~89 % ; fine-tuné +6,2 pts appariés, mais seulement à taux différencié décroissant (à taux constants, l'optimiseur finit sous le gelé) |

Documentation complète : [04-Vision/README.md](04-Vision/README.md)

## Workshop 3 Jours (Track1-LangChain)

### Day 1 - Révision Python

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 1 | [Lab1-PythonForDataScience](Track1-LangChain/Day1-Foundations/Labs/Lab1-PythonForDataScience.ipynb) | Pandas, Matplotlib, Scikit-Learn |

### Day 2 - Agents Documentaires

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 2 | [Lab2-RFP-Analysis](Track1-LangChain/Day2-Document-Agents/Labs/Lab2-RFP-Analysis/Lab2-RFP-Analysis.ipynb) | Parser des appels d'offres avec LLM |
| 3 | [Lab3-CV-Screening](Track1-LangChain/Day2-Document-Agents/Labs/Lab3-CV-Screening/Lab3-CV-Screening.ipynb) | Scoring CV avec agents IA |

### Day 3 - Data + Agents

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 4 | [Lab4-DataWrangling](Track1-LangChain/Day3-Data-Agents/Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb) | Nettoyage et transformation |
| 5 | [Lab5-Viz-ML](Track1-LangChain/Day3-Data-Agents/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | Visualisation et intro ML |
| 6 | [Lab6-First-Agent](Track1-LangChain/Day3-Data-Agents/Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | Construction d'un agent simple |
| 7 | [Lab7-Data-Analysis-Agent](Track1-LangChain/Day3-Data-Agents/Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | Agent pour DataFrames |

## Track Track2-GoogleADK (Days 4-7)

Track avancé intégrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

### Day 4 - ADK Foundations (Labs 8-9)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 8 | [ADK-Introduction](Track2-GoogleADK/Day4-Foundations/Lab8-ADK-Introduction.ipynb) | Architecture ADK, configuration providers |
| 9 | [First-ADK-Agent](Track2-GoogleADK/Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | Premier agent pour Data Science |

### Day 5 - DS-STAR (Labs 10-12 + extensions 12b-12d, 18)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 10 | [File-Analyzer](Track2-GoogleADK/Day5-DS-Star/Lab10-File-Analyzer.ipynb) | Analyse de fichiers hétérogènes |
| 11 | [Planner-Coder-Loop](Track2-GoogleADK/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | Boucle itérative multi-agents |
| 12 | [DS-Star-Workshop](Track2-GoogleADK/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | Application complète |
| 12b | [Sequential-Orchestration](Track2-GoogleADK/Day5-DS-Star/Lab12b-Sequential-Orchestration.ipynb) | Contrat C4 : désignation séquentielle, l'orchestrateur explicite au-dessus d'ADK |
| 12c | [Agent-Handoff](Track2-GoogleADK/Day5-DS-Star/Lab12c-Agent-Handoff.ipynb) | Contrat C5 : handoff inter-agents natif câblé et observable |
| 12d | [Token-Usage](Track2-GoogleADK/Day5-DS-Star/Lab12d-Token-Usage.ipynb) | Contrat C6 : traçabilité de la consommation LLM |
| 18 | [Session-Persistence](Track2-GoogleADK/Day5-DS-Star/Lab18-Session-Persistence.ipynb) | Persistance d'état de session : une conversation qui se souvient |

### Day 6 - MLE-STAR (Labs 13-15)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 13 | [Web-Search-SOTA](Track2-GoogleADK/Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb) | Recherche de modèles SOTA |
| 14 | [Ablation-Refinement](Track2-GoogleADK/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb) | Optimisation ciblée |
| 15 | [Kaggle-Challenge](Track2-GoogleADK/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb) | Compétition Kaggle |

### Day 7 - Production (Labs 16-17)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 16 | [Data-Science-Agent](Track2-GoogleADK/Day7-Production/Lab16-Data-Science-Agent.ipynb) | Agent BigQuery/BQML |
| 17 | [Final-Project](Track2-GoogleADK/Day7-Production/Lab17-Final-Project.ipynb) | Projet intégré |

### Technologies Track2-GoogleADK

| Catégorie | Technologies |
|-----------|--------------|
| **Abstraction** | LiteLLM (multi-provider) |
| **Google ADK** | google-adk, google-generativeai |
| **Providers** | Gemini 3.1, vLLM, OpenAI, OpenRouter |
| **Cloud (Day 7)** | BigQuery, Vertex AI, BQML |

Documentation complète : [Track2-GoogleADK/README.md](Track2-GoogleADK/README.md)

## Technologies

| Catégorie | Technologies |
|-----------|--------------|
| **Data Science** | NumPy, Pandas, Matplotlib, Seaborn, Pillow, PyTorch (parité 04-Vision) |
| **Machine Learning** | Scikit-Learn |
| **Agents IA** | LangChain, OpenAI GPT |
| **Orchestration** | python-dotenv |

## Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/Mac

# Labs 1 et 4-5 (Data Science de base)
pip install pandas numpy matplotlib seaborn scikit-learn ipywidgets

# Labs 2-3 et 6-7 (Agents LangChain)
pip install langchain langchain-openai langchain-experimental python-dotenv
```

### Configuration API (Labs 2-3, 6-7)

```bash
# Créer un fichier .env à la racine du projet
OPENAI_API_KEY=sk-...
```

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Agent** | LLM + Outils + Prompt + Exécuteur |
| **Tool** | Fonction appelable par l'agent |
| **Chain** | Séquence d'opérations LLM |
| **Memory** | Contexte conversationnel |

## FAQ / Troubleshooting

### `langchain` ou `langchain-openai` échoue à l'import

Vérifier que le bon environnement est activé :

```bash
# vérifier l'environnement
which python  # Linux/Mac
where python  # Windows
# doit pointer vers votre venv, pas le système

# ré-installer si nécessaire
pip install langchain langchain-openai langchain-experimental
```

Si l'erreur persiste, vérifier la version Python (3.10+ requis) : `python --version`.

### Erreur "OPENAI_API_KEY not found" dans les Labs 2-3 et 6-7

Ces labs nécessitent une clé API OpenAI. Créer un fichier `.env` à la racine du projet :

```bash
# À la racine du repo ou à côté des notebooks
echo 'OPENAI_API_KEY=sk-...' > .env
```

Le package `python-dotenv` charge automatiquement ce fichier. Ne JAMAIS committer le fichier `.env` (il est dans `.gitignore`).

### Les agents ADK ne se connectent pas au provider (Labs 8+)

Vérifier la configuration dans le fichier `.env` d'Track2-GoogleADK :

```bash
# Provider recommandé (clé gratuite)
ACTIVE_PROVIDER=gemini
GEMINI_API_KEY=AIza...

# Ou provider local (pas de clé requise)
ACTIVE_PROVIDER=vllm
VLLM_BASE_URL=http://localhost:8000/v1
```

Si vous utilisez Gemini, obtenir une clé gratuite sur [aistudio.google.com](https://aistudio.google.com).

### `ModuleNotFoundError` pour un package dans un lab

Chaque lab a des dépendances spécifiques. Installer les packages au fur et à mesure :

```bash
# Labs 1, 4-5 (data science classique)
pip install pandas numpy matplotlib seaborn scikit-learn ipywidgets

# Labs 2-3, 6-7 (agents LangChain)
pip install langchain langchain-openai langchain-experimental python-dotenv

# Labs 8-17 (ADK)
pip install -r Track2-GoogleADK/requirements.txt
```

### Comment passer de LangChain a Google ADK ?

Les concepts se correspondent :

| Concept LangChain | Équivalent ADK |
|-------------------|----------------|
| `LLMChain` | ADK Agent avec instruction |
| `Tool` | ADK FunctionTool |
| `AgentExecutor` | ADK Runner |
| `ConversationBufferMemory` | ADK Session |
| `SequentialChain` | Boucle Planner-Coder |

Le passage se fait naturellement au Lab 8 qui reprend les mêmes concepts avec l'API ADK.

### Le kernel Jupyter n'affiche pas les outputs des agents

Certains agents produisent des outputs longs. Vérifier :

1. La cellule n'est pas en timeout (augmenter le timeout du kernel)
2. Le provider répond (tester avec un appel simple : `client.chat.completions.create(...)`)
3. Les prints intermédiaires sont flushés : `print(..., flush=True)`

## Ressources

- [Pandas Documentation](https://pandas.pydata.org/docs/)
- [LangChain Documentation](https://python.langchain.com/)
- [OpenAI Cookbook](https://cookbook.openai.com/)

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette série vous a fait traverser un **changement de posture** en data science : passer de *l'écriture* du code d'analyse à *l'orchestration* d'agents LLM qui le produisent et l'exécutent. L'arc pédagogique :

- **Les fondations, volontairement manuelles** — NumPy (vectorisation) et Pandas (DataFrame, groupby, nettoyage) d'abord pratiqués à la main. Cette base n'est pas un préalable accessoire : c'est le référent qui rend *jugeable* le travail de l'agent. On ne peut évaluer ce qu'un agent produit sur un DataFrame que si l'on sait soi-même le manipuler — d'où la règle des 80/20 (CrowdFlower, 2016) qui ouvre le Lab 4 : la préparation reste le cœur du métier, l'agent l'accélère sans l'effacer.
- **Le track LangChain — l'agent unique outillé (Days 1-3)** — on assemble les quatre composants d'un agent (LLM + outils + prompt + orchestrateur), puis on l'applique à des tâches documentaires (parsing d'appel d'offre, scoring de CV) et d'analyse (wrangling, classification, agent DataFrame). Deux paradigmes canoniques structurent cette track : **LCEL** (composition par tube `prompt | llm`) pour les chaînes, et **ReAct** (boucle Pensée→Action→Observation) couplée au **tool-calling** pour le premier agent ; le `create_pandas_dataframe_agent` concrétise **CodeAct** (l'agent écrit et exécute lui-même son Python). L'enjeu n'est pas la magie du LLM mais la *qualité du prompt* et du *schéma de sortie* (JSON structuré).
- **Le track Google ADK — les systèmes multi-agents (Days 4-7)** — on monte en abstraction : du single-agent on passe à des *systèmes* (boucles planner-coder-verifier), puis aux architectures SOTA (DS-STAR pour la data science, MLE-STAR pour l'ingénierie ML), jusqu'à concourir sur Kaggle (MLE-bench) et déployer en production (BigQuery, Vertex AI, BQML). La question bascule : ce n'est plus « comment coder cette analyse ? » mais « comment concevoir un *système d'agents* qui l'exécute, la valide et la raffine ? ».
- **La finesse** — la série ne vend pas l'agent autonome comme une solution universelle. Chaque lab pose la question du *cadre* : quels outils exposer, comment valider la sortie, quand l'agent accélère réellement *vs* quand il hallucine ou dérive. Le survey sur l'hallucination (Lab 17) et la méthodologie d'ablation (Lab 14) ancrent cette lucidité.

La thèse est honnête : les agents LLM ne remplacent pas le data scientist, ils *reconfigurent* son métier — de l'exécution vers l'orchestration, la spécification et la validation. Le savoir-faire Pandas/scikit-learn reste le socle ; ce qui change, c'est la *granularité* à laquelle on pilote l'analyse.

### Prochaines étapes

- **Approfondir le ML sous-jacent** : la série [ML](../README.md) (et son pendant C# [ML.Net](../ML.Net/README.md)) reprend les algorithmes (LightGBM, SSA, évaluation PFI/ROC) sous l'angle de l'implémentation — utile pour comprendre ce que l'agent exécute quand il génère du code scikit-learn.
- **Démarrer par les fondations visuelles** : la sous-série [`04-Vision`](04-Vision/README.md) prolonge [03-DeepLearning](03-DeepLearning/README.md) sur les images (Conv2d from scratch + ConvNet profonde + résiduelles, parité NumPy/torch à epsilon machine, puis transfer learning ResNet gelé vs fine-tuné). Prérequis utile avant d'orchestrer un agent sur des données image.
- **Aller vers l'évaluation et la robustesse** : les Labs 13-15 (Web-Search-SOTA, Ablation-Refinement, Kaggle-Challenge) introduisent l'évaluation rigoureuse des agents ML (MLE-bench, métriques cross-compétition) ; le prolongement naturel est la **robustesse multi-seed** et la **walk-forward validation**, traitées dans le pipeline [QuantConnect](../../QuantConnect/README.md).
- **Franchir le cap production** : le Day 7 (BigQuery, BQML, Vertex AI) ouvre sur le déploiement réel. Le pont vers [GenAI](../../GenAI/README.md) relie ces agents data aux pipelines de génération (image, audio, texte) et aux architectures Qwen/Lumina auto-hébergées.
- Pour la pratique : reprenez le Lab 7 (agent DataFrame) et posez-lui une question qu'il *ne peut pas* répondre avec les seules colonnes présentes — comment réagit-il ? Confrontez cette limite au Lab 11 (boucle planner-coder) : qu'apporte vraiment le multi-agent ? C'est la tension vivante de la série : la puissance de l'agent *vs* la nécessité de l'encadrer.

### Le fil rouge

Le data science agentique propose un changement de regard : ne plus demander « comment coder cette analyse ? » mais **« comment la spécifier assez clairement pour qu'un agent LLM la code, l'exécute et la valide à ma place ? »**. La série vous a donné les fondations (NumPy/Pandas), l'agent unique outillé (LangChain, ReAct, tool-calling, CodeAct) et les systèmes multi-agents (ADK, DS-STAR/MLE-STAR, production GCP) — en gardant à l'esprit que la valeur d'un agent se mesure moins à ce qu'il *produit* qu'à la *qualité du cadre* (outils, prompts, validation) dans lequel il opère.

---

## Licence

Voir la licence du repository principal.
