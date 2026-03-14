# Sujets Projet 2 - ECE Ing4 Finance IA 2026

**Date**: 13 mars 2026
**Deadline**: Fin mars/début avril 2026 (~3 semaines)
**Groupes**: 3 personnes

---

## Instructions aux étudiants

Ce document présente une liste de **~20-25 sujets** pour le Projet 2. Chaque sujet doit :

1. **S'inspirer des notebooks du cours** comme point de départ
2. **Aller au-delà des notebooks** - pas de simple copie
3. **Viser une ambition élevée** - vous pouvez utiliser l'IA générative
4. **Produire un livrable fonctionnel** avec code, documentation et présentation

**Sujets déjà traités en Projet 1 (à éviter ou transformer significativement)** :
- Wordle AI Solver, Graph Coloring, XAI Finance, Démineur IA, Mots Croisés
- Planning Infirmiers, Calendrier Sportif, Fraude Financière, Fair Credit Scoring
- Market Making, Wealth Planner, Genetic Trading, TWAP/VWAP Optimization, Robo-Advisor

---

## Catégorie 1 : IA Probabiliste (5 sujets)

### 1.1 - Système de Recommandation Bayésien pour Actifs Financiers

**Domaine** : Probas
**Ref. notebooks** : Infer-101 (Infer.NET)
**Déjà traité** : Non

**Description** : Construire un système de recommandation bayésien qui suggère des actifs financiers aux investisseurs en se basant sur leur profil de risque et les performances historiques. Le système doit mettre à jour ses croyances en ligne avec les nouvelles données de marché.

**Objectifs gradues** :
- **Minimum** : Modèle bayésien simple avec Infer.NET, profil de risque statique, recommandation basée sur rendement moyen
- **Bon** : Inférence en ligne avec mises à jour dynamiques, incorporation de mesures de risque (VaR, CVaR), visualisation des distributions
- **Excellent** : Modèle de mélange gaussien pour clustering d'actifs, apprentissage des préférences utilisateur, backtesting historique, interface utilisateur

**Pourquoi ce sujet** : Applique directement la programmation probabiliste à un cas d'usage financier réel

---

### 1.2 - Allocation d'Actifs sous Incertitude avec Processus Gaussiens

**Domaine** : Probas + ML
**Ref. notebooks** : Infer-101, ML.NET basics
**Déjà traité** : Non

**Description** : Utiliser des processus gaussiens pour modéliser l'incertitude sur les rendements futurs et optimiser l'allocation d'actifs en conséquence. Le système doit quantifier l'incertitude et l'intégrer dans la décision d'investissement.

**Objectifs gradus** :
- **Minimum** : Processus gaussien univarié pour modéliser un actif, optimisation portefeuille simple (Sharpe ratio)
- **Bon** : GP multivarié pour corrélations, optimisation sous contraintes (budget, exposition), visualisation des bandes de confiance
- **Excellent** : GP pour plusieurs actifs avec noyaux adaptatifs, optimisation robuste (CVaR), comparaison avec méthodes classiques (Markowitz)

**Pourquoi ce sujet** : Combine probabilités bayésiennes et finance quantitative, très pertinent pour l'incertitude de marché

---

### 1.3 - Détection d'anomalies séquentielles pour Transactions Frauduleuses

**Domaine** : Probas + ML
**Ref. notebooks** : Infer-101 (apprentissage en ligne)
**Déjà traité** : ECE 2026 Projet1 (Fraude financière avec ILP) → **Transformer significativement**

**Description** : Système de détection d'anomalies en temps réel pour transactions bancaires utilisant l'apprentissage probabiliste séquentiel. Contrairement au Projet 1 (approche ILP statique), ce projet se concentre sur la détection en streaming avec mise à jour continue.

**Objectifs gradus** :
- **Minimum** : Modèle de probabilité anormale basée sur montants/fréquences, alertes seuils fixes
- **Bon** : Modèle bayésien séquentiel avec mise à jour en ligne, incorporation du contexte utilisateur, visualisation temps réel
- **Excellent** : Modèle de mélange dynamique, apprentissage de patterns normaux/anormaux par utilisateur, évaluation sur données réelles (synthétisées), FaRR/FDR metrics

**Pourquoi ce sujet** : Différenciation claire avec Projet 1 (streaming vs batch), très applicatif en finance

---

### 1.4 - Prédiction de Défaut d'Entreprise avec Modèles Probabilistes

**Domaine** : Probas
**Ref. notebooks** : Infer-101 (modèles mixtes)
**Déjà traité** : Non

**Description** : Modèle probabiliste pour prédire la probabilité de défaut d'entreprises cotées en combinant données financières et macroéconomiques. Le modèle doit fournir des prédictions avec intervalles de confiance.

**Objectifs gradus** :
- **Minimum** : Régression logistique bayésienne avec Infer.NET, prédictions ponctuelles
- **Bon** : Modèle hiérarchique pour secteurs d'activité, incorporation de variables macro, calibration des probabilités
- **Excellent** : Modèle de survie bayésien (temps jusqu'au défaut), comparaison avec approches fréquentistes, backtesting sur données historiques

**Pourquoi ce sujet** : Application directe au risque de crédit, fondement bancaire

---

### 1.5 - Modélisation de Volatilité Stochastique avec MCMC

**Domaine** : Probas
**Ref. notebooks** : Pyro_RSA_Hyperbole (Pyro)
**Déjà traité** : Non

**Description** : Implémenter un modèle de volatilité stochastique (Heston ou SABR) en utilisant la programmation probabiliste (Pyro) et l'inférence MCMC. Le modèle estime la volatilité latente d'un actif à partir des prix observés.

**Objectifs gradus** :
- **Minimum** : Modèle Heston simple avec Pyro, inférence MCMC basique, estimation sur données synthétiques
- **Bon** : Modèle SABR (Stochastic Alpha Beta Rho), diagnostics de convergence MCMC, comparaison formule fermée vs MCMC
- **Excellent** : Calibration sur données de marché d'options, vol surface fitting, pricing d'options exotiques, visualisation des chaines MCMC

**Pourquoi ce sujet** : Connecte programmation probabiliste et finance quantitative avancée

---

## Catégorie 2 : Théorie des Jeux (5 sujets)

### 2.1 - Algorithmes de Auction Design pour Publicité Programmatique

**Domaine** : GameTheory
**Ref. notebooks** : GT-16 (Mechanism Design), GT-15 (Cooperative Games)
**Déjà traité** : Non

**Description** : Concevoir et implémenter un mécanisme d'enchère pour la publicité en ligne (VCG, GSP ou variantes). Le système doit simuler des annonceurs stratégiques et analyser les propriétés du mécanisme (réalité, efficience, revenu).

**Objectifs gradus** :
- **Minimum** : Enchère au second prix (Vickrey) pour 1 slot, simulation annonceurs avec valeurs privées
- **Bon** : Enchère GSP (Generalized Second Price) pour plusieurs slots, équilibre de Nash des stratégies d'enchère
- **Excellent** : Comparaison VCG vs GSP, analyse incitations à tricher, optimisation du revenu de l'enchérisseur, extension au budgeting

**Pourquoi ce sujet** : Application de mechanism design à un marché réel (publicité), connecte GT et économie numérique

---

### 2.2 - Jeux d'Investissement sur Graphes (Network Games)

**Domaine** : GameTheory
**Ref. notebooks** : GT-4 (Nash Equilibrium), GT-6 (Evolution/Trust)
**Déjà traité** : Non

**Description** : Modéliser des décisions d'investissement dans un réseau où les rendements dépendent des investissements des voisins (effets de réseau). Analyser les équilibres de Nash et la dynamique d'apprentissage.

**Objectifs gradus** :
- **Minimum** : Graphe simple, jeu de contribution binaire, calcul d'un équilibre de Nash
- **Bon** : Graphes plus complexes (scale-free, small-world), dynamique d'apprentissage (fictitious play), visualisation graphique
- **Excellent** : Effets d'information incomplète, analyse de stabilité, comparaison avec graphes réels (réseaux d'investisseurs), optimale network design

**Pourquoi ce sujet** : Combine théorie des jeux et structure de réseau, applications en finance sociale/crowdfunding

---

### 2.3 - Stratégies de Négociation Automatique avec Information Incomplète

**Domaine** : GameTheory
**Ref. notebooks** : GT-13 (CFR - Imperfect Info)
**Déjà traité** : Non

**Description** : Implémenter un agent de négociation automatique utilisant des algorithmes de résolution de jeux à information imparfaite (CFR ou variantes). Application à un scénario de négociation financière (achat/vente d'actif).

**Objectifs gradus** :
- **Minimum** : Jeu de négociation simplifié (offre alternée), implémentation CFR basique
- **Bon** : Jeu avec plus d'états, incorporation de signaux privés, analyse de la stratégie d'équilibre
- **Excellent** : Négociation multi-issues (prix + quantité + délai), apprentissage adversarial, évaluation contre humains (interface simple)

**Pourquoi ce sujet** : Application directe de CFR (poker AI) à un cas d'usage business

---

### 2.4 - Formation de Coalitions pour Plateformes de Trading

**Domaine** : GameTheory
**Ref. notebooks** : GT-15 (Cooperative Games), GT-16 (Mechanism Design)
**Déjà traité** : Non

**Description** : Modéliser la formation de coalitions entre traders sur une plateforme d'échange pour réduire les frais ou accéder à de meilleures liquidités. Analyser la stabilité des coalitions (core, Shapley value).

**Objectifs gradus** :
- **Minimum** : Jeu de coalition simple (frais de transaction réductibles), calcul de la valeur de Shapley
- **Bon** : Algorithme de formation de coalitions (merge-and-split), analyse de stabilité, visualisation des coalitions
- **Excellent** : Extension au marché avec ordres limités, mécanisme d'incitation, simulation dynamique, comparaison avec plateformes réelles

**Pourquoi ce sujet** : Connecte jeux coopératifs et microstructure de marché, très financier

---

### 2.5 - Dynamique Évolutionniste de Stratégies de Trading

**Domaine** : GameTheory
**Ref. notebooks** : GT-6 (Evolutionary Games), GT-17 (Multi-Agent RL)
**Déjà traité** : Non

**Description** : Simuler une population de stratégies de trading qui évoluent par sélection naturelle. Certaines stratégies se propagent, d'autres disparaissent. Analyser la dynamique et les équilibres évolutivement stables.

**Objectifs gradus** :
- **Minimum** : Population de 2-3 stratégies simples (momentum, mean-reversion, buy-and-hold), dynamique de réplication
- **Bon** : Plusieurs stratégies avec paramètres évolutifs, paysage de fitness complexe, visualisation de la dynamique
- **Excellent** : Coévolution de stratégies, invasion mutante, ESS (Evolutionarily Stable Strategies), backtesting sur données réelles

**Pourquoi ce sujet** : Combine théorie des jeux évolutionniste et finance comportementale

---

## Catégorie 3 : Machine Learning & Finance (6 sujets)

### 3.1 - Sentiment Analysis Multi-source pour Prédiction de Marché

**Domaine** : ML
**Ref. notebooks** : Lab3 (CV Screening), Lab13 (Web Search SOTA)
**Déjà traité** : Non

**Description** : Système d'analyse de sentiment combinant plusieurs sources (news, tweets, rapports financiers) pour prédire les mouvements de marché. Utilisation de LLMs pour l'analyse et agrégation des signaux.

**Objectifs gradus** :
- **Minimum** : Analyse de sentiment sur un type de source (news headlines), classification binaire (hausse/baisse)
- **Bon** : Multi-source avec agrégation pondérée, incorporation de temporalité, visualisation des signaux
- **Excellent** : RAG (Retrieval Augmented Generation) pour analyse contextuelle, architecture multi-LLM, backtesting avec transaction costs, comparaison baseline buy-and-hold

**Pourquoi ce sujet** : Combine NLP moderne et trading, très tendance

---

### 3.2 - Classification de Documents Financiers avec Zero-shot Learning

**Domaine** : ML
**Ref. notebooks** : Lab2 (RFP Analysis), Lab13 (Web Search)
**Déjà traité** : Non

**Description** : Système de classification automatique de documents financiers (rapports annuels, prospectus, ESG) utilisant le zero-shot learning avec LLMs. Le système doit classer des documents sans entraînement supervisé spécifique.

**Objectifs gradus** :
- **Minimum** : Classification binaire simple avec un LLM (OpenAI/OpenRouter), prompt engineering basique
- **Bon** : Multi-classe, évaluation sur dataset réel, comparaison avec approche supervisée, few-shot prompting
- **Excellent** : Classification hiérarchique, incorporation de schémas XBRL/FRL, évaluation métrologique (precision/recall/F1), interface de validation humaine

**Pourquoi ce sujet** : Application NLP avec exigence financière (ESG est très demandé)

---

### 3.3 - Système de RAG pour Questions Financières Complexes

**Domaine** : ML
**Ref. notebooks** : Lab13 (Web Search SOTA), Lab7 (Data Analysis Agent)
**Déjà traité** : Non

**Description** : Système RAG (Retrieval Augmented Generation) permettant de poser des questions complexes sur des données/rapports financiers et obtenir des réponses avec citations. Le système doit gérer des documents hétérogènes (PDF, tables, news).

**Objectifs gradus** :
- **Minimum** : RAG basique avec vector store (Chroma), embedding simple, LLM pour génération de réponses
- **Bon** : Chunking intelligent pour tables, multi-retrieval (dense + sparse), évaluation des réponses (RAGAS)
- **Excellent** : RAG agentic (requêtes complexes décomposées), time-aware retrieval (données temporelles), citations vérifiables, interface chat

**Pourquoi ce sujet** : Architecture RAG est très demandée en entreprise 2025-2026

---

### 3.4 - Détection de Changement de Régime de Marché avec Deep Learning

**Domaine** : ML + Probas
**Ref. notebooks** : ML.NET basics, Infer-101
**Déjà traité** : Non

**Description** : Système de détection automatique de changements de régime de marché (bull/bear, volatility regimes) utilisant des techniques de deep learning (variational autoencoders, hidden Markov models).

**Objectifs gradus** :
- **Minimum** : Détection basée sur thresholds statistiques simples, visualisation des régimes
- **Bon** : VAE pour apprendre des features latentes, HMM pour modéliser les transitions, évaluation sur données historiques
- **Excellent** : Modèle hybride VAE-HMM, prédiction de transitions, backtesting de stratégie adaptative, comparaison avec approches classiques (Markov switching)

**Pourquoi ce sujet** : Combine deep learning et finance quantitative, très applicable

---

### 3.5 - Optimisation Hyperparamètres avec Bayesian Optimization

**Domaine** : ML + Probas
**Ref. notebooks** : ML.NET (AutoML), Infer-101 (Gaussian Processes)
**Déjà traité** : Non

**Description** : Implémenter un système d'optimisation d'hyperparamètres utilisant l'optimisation bayésienne (Gaussian Processes + acquisition functions). Application à l'optimisation de stratégies de trading ou de modèles ML.

**Objectifs gradus** :
- **Minimum** : Gaussian Process pour modéliser la fonction objectif, acquisition function basique (EI)
- **Bon** : Optimisation multi-objectif (Sharpe ratio + drawdown), visualisation du processus d'optimisation
- **Excellent** : Optimisation parallèle, contraintes (budget, temps), comparaison avec autres méthodes (grid search, random search, hyperband)

**Pourquoi ce sujet** : Compétence très demandée en MLOps, applicable partout

---

### 3.6 - Classification de Risque ESG avec LLMs Multi-label

**Domaine** : ML
**Ref. notebooks** : Lab3 (CV Screening), Lab13 (Web Search)
**Déjà traité** : Non

**Description** : Système de classification multi-label de documents financiers selon les critères ESG (Environnemental, Social, Gouvernance). Utilisation de LLMs pour l'extraction et la classification.

**Objectifs gradus** :
- **Minimum** : Classification binaire par critère ESG avec un LLM, prompt basique
- **Bon** : Classification multi-label (plusieurs critères par document), évaluation multi-label (precision@k, recall@k)
- **Excellent** : Extraction de mentions ESG (quote-level), agrégation au niveau entreprise, benchmark contre annotations humaines, dashboard de suivi ESG

**Pourquoi ce sujet** : ESG est un enjeu majeur en finance 2025-2026

---

## Catégorie 4 : Confidentialité & Sécurité (3 sujets)

### 4.1 - Federated Learning pour Prédiction de Défaut Collaborative

**Domaine** : ML
**Ref. notebooks** : ML.NET (training)
**Déjà traité** : Non

**Description** : Système de Federated Learning permettant à plusieurs banques de collaborer pour entraîner un modèle de prédiction de défaut sans partager leurs données clients. Le système doit simuler plusieurs clients et un serveur d'agrégation.

**Objectifs gradus** :
- **Minimum** : Federated averaging simple, 2-3 clients avec données synthétiques, modèle linéaire
- **Bon** : Plus de clients, données hétérogènes (non-IID), differential privacy pour l'agrégation
- **Excellent** : Communication-efficient (compression), personalisation locale, attaque par inversion (évaluation privacy), comparaison avec centralisé

**Pourquoi ce sujet** : Federated Learning est critique en finance pour la confidentialité

---

### 4.2 - Chiffrement Homomorphe pour Agrégation de Données Financières

**Domaine** : Cryptographie + ML
**Ref. notebooks** : Aucun direct (recherche nécessaire)
**Déjà traité** : Non

**Description** : Prototype utilisant le chiffrement homomorphe pour permettre l'agrégation de données financières sensibles (ex: positions de risque) sans les déchiffrer. Le système doit permettre des calculs sur les données chiffrées.

**Objectifs gradus** :
- **Minimum** : Somme de nombres chiffrés avec une librairie FHE (Microsoft SEAL, TenSEAL), démonstration concept
- **Bon** : Opérations plus complexes (moyenne, variance) sur données chiffrées, benchmark performance
- **Excellent** : Agrégation de vecteurs de features, ML sur données chiffrées (classification simple), analyse trade-off précision/performance

**Pourquoi ce sujet** : Technologie émergente critique pour la privacy en finance

---

### 4.3 - Système de Détection de Data Poisoning Adversarial

**Domaine** : ML + Sécurité
**Ref. notebooks** : ML.NET (training)
**Déjà traité** : Non

**Description** : Système détectant les tentatives de data poisoning dans des modèles ML financiers. Un attaquant malveillant injecte des données corrompues pour biaiser le modèle. Le système doit identifier ces données.

**Objectifs gradus** :
- **Minimum** : Simulation de poison attack simple (label flipping), détection basée sur statistiques
- **Bon** : Plusieurs types d'attaques (clean-label, backdoor), détection avec influence functions, évaluation robustesse
- **Excellent** : Détection en ligne (streaming), défense proactive (data sanitization), évaluation sur cas d'usage financier (fraude, crédit)

**Pourquoi ce sujet** : Sécurité ML est un enjeu critique 2025-2026

---

## Catégorie 5 : Sujets Avancés / Recherche (6 sujets)

### 5.1 - Conformal Prediction pour Intervalles de Confiance Garantis

**Domaine** : Probas + ML
**Ref. notebooks** : Infer-101, ML.NET
**Déjà traité** : Non

**Description** : Implémenter la Conformal Prediction pour garantir des intervalles de confiance avec couverture valide (distribution-free). Application à la prédiction de rendements ou de défaut.

**Objectifs gradus** :
- **Minimum** : Conformal prediction basique (split conformal), régression avec intervalles
- **Bon** : Adaptive conformal (lokation-specific), évaluation de la couverture, visualisation des intervalles
- **Excellent** : Conformal pour time series (ACI), comparaison avec méthodes bayésiennes, application multi-output

**Pourquoi ce sujet** : Méthode rigoriste pour l'incertitude, très en vogue en recherche

---

### 5.2 - World Models pour Trading (DreamerV3-inspired)

**Domaine** : GameTheory (GT-17) + ML
**Ref. notebooks** : GT-17 (Multi-Agent RL)
**Déjà traité** : Non

**Description** : Système de trading utilisant un "world model" qui apprend une dynamique de marché simulée, puis planifie dans ce monde simulé. Inspiration DreamerV3 mais adapté aux marchés financiers.

**Objectifs gradus** :
- **Minimum** : World model simple (MLP latent dynamics), planification basique (MPC), environnement de marché simulé
- **Bon** : Architecture complète Dreamer (world model + actor-critic), apprentissage de la dynamics, évaluation dans simulation
- **Excellent** : Adaptation à données réelles (transfer), analyse de la qualité du monde appris, comparaison avec RL direct

**Pourquoi ce sujet** : Architecture state-of-the-art en RL 2024-2025

---

### 5.3 - Causal Discovery pour Relations de Causalité en Finance

**Domaine** : Probas (causalité) + ML
**Ref. notebooks** : Pyro_RSA_Hyperbole (inférence causale mentionnée)
**Déjà traité** : Non

**Description** : Système découverte automatique de relations causales entre variables financières (taux, inflation, PIB, prix actifs) utilisant des algorithmes de causal discovery (PC, GES, NOTEARS).

**Objectifs gradus** :
- **Minimum** : Algorithme PC simple pour variables gaussiennes, graph causal sur données synthétiques
- **Bon** : Plusieurs algorithmes (PC, GES), évaluation de la structure (SHD), données macroéconomiques réelles
- **Excellent** : Causal discovery avec variables latentes, intervention analysis (what-if), interprétation économique des graphes

**Pourquoi ce sujet** : Inférence causale est la frontière de la recherche en ML appliqué

---

### 5.4 - Système Multi-Agent pour Simulation de Marché

**Domaine** : GameTheory (GT-17) + ML
**Ref. notebooks** : GT-17 (Multi-Agent RL)
**Déjà traité** : Non

**Description** : Simuler un marché financier avec plusieurs types d'agents (market makers, arbitrageurs, noise traders) utilisant MARL (Multi-Agent Reinforcement Learning). Analyser la dynamique de marché émergente.

**Objectifs gradus** :
- **Minimum** : 2 types d'agents, environnement de marché simplifié (order book), apprentissage indépendant
- **Bon** : 3-4 types d'agents avec stratégies différentes, apprentissage centralisé (MAPPO ou QMIX), analyse de la dynamique
- **Excellent** : Agents avec information asymétrique, formation de prix endogène, validation contre stylized facts (volatility clustering, etc.)

**Pourquoi ce sujet** : MARL + microstructure de marché = recherche active

---

### 5.5 - Neurosymbolic AI pour Explicabilité de Décisions de Crédit

**Domaine** : ML + Symbolic AI
**Ref. notebooks** : Lab3 (CV Screening), XAI mentionné
**Déjà traité** : ECE 2026 Projet1 (XAI Finance) → **Transformer significativement**

**Description** : Système hybride neurosymbolique combinant un réseau de neurones (pour la prédiction) et une couche symbolique (pour l'explication générative). Le système explique ses décisions de crédit en langage naturel.

**Objectifs gradus** :
- **Minimum** : Neural network + règles symboliques simples post-hoc, explications basiques
- **Bon** : Intégration neurone-symbole pendant l'entraînement (neural theorem prover), explications contrefactuelles
- **Excellent** : Architecture neurosymbolique complète (DeepProbLog ou similaire), explications génératives avec LLM, évaluation humaine-in-the-loop

**Pourquoi ce sujet** : Différenciation avec Projet 1 (neurosymbolic vs post-hoc XAI), frontier research

---

### 5.6 - LLMs pour Generation de Scenarios Macroéconomiques

**Domaine** : ML (LLMs) + Finance
**Ref. notebooks** : Lab13 (Web Search SOTA)
**Déjà traité** : Non

**Description** : Système utilisant des LLMs pour générer des scénarios macroéconomiques cohérents (inflation, croissance, taux) afin de tester la robustesse de portefeuilles. Les scénarios doivent être réalistes et couvrir les extrêmes.

**Objectifs gradus** :
- **Minimum** : Génération de scénarios simples avec un LLM (prompting), validation de cohérence manuelle
- **Bon** : Pipeline de génération structurée (JSON), contraintes de cohérence (corrélations), génération de stress scenarios
- **Excellent** : Fine-tuning d'un LLM pour scénarios financiers, évaluation de la couverture des risques, intégration avec moteur de risque, interface pour risk managers

**Pourquoi ce sujet** : Combine LLMs et risk management, très applicatif

---

## Annexe : Méthodologie de Travail Suggérée

### Semaine 1 : Fondation
- **Jour 1-2** : Étude des notebooks de référence, compréhension des concepts
- **Jour 3-4** : Recherche bibliographique (papers, articles), état de l'art
- **Jour 5** : Spécification détaillée (objectifs, livrables, planning)

### Semaine 2 : Développement
- **Jour 1-3** : Implémentation du niveau Minimum (MVP fonctionnel)
- **Jour 4-5** : Extension vers le niveau Bon, tests préliminaires

### Semaine 3 : Finalisation
- **Jour 1-2** : Atteinte du niveau Excellent (si possible), optimisation
- **Jour 3** : Documentation, README, tests
- **Jour 4-5** : Préparation présentation, slides, démo

---

## Critères d'Évaluation

| Critère | Poids | Description |
|---------|-------|-------------|
| **Ambition & Originalité** | 20% | Niveau d'ambition du sujet, originalité par rapport aux notebooks |
| **Qualité Technique** | 25% | Architecture du code, robustesse, performance |
| **Utilisation des concepts du cours** | 20% | Pertinence de l'utilisation de Probas/GT/ML |
| **Fonctionnalité & Résultats** | 20% | Le système fonctionne-t-il ? Résultats observables |
| **Documentation & Communication** | 15% | README, code commenté, qualité de la présentation |

---

## Tendances IA & Finance 2025-2026

Pour vous aider dans vos choix, voici les tendances majeures qui devraient dominer le paysage IA/Finance en 2025-2026 :

### 1. Agents IA et Multi-Agent Systems (MAS)

**Tendance**: Explosion des systèmes multi-agents autonomes qui collaborent pour résoudre des tâches complexes.

**Applications finance**:
- **Trading collaboratif** : Plusieurs agents spécialisés (analyse fondamentale, technique, sentiment) qui débattent et votent
- **Recherche automatisée** : Agents qui recherchent, filtrent et synthétisent l'information financière en temps réel
- **Risk management** : Systèmes multi-agents pour la détection de risques cross-asset

**Technologies clés** : LangGraph, AutoGen, Microsoft AutoGen, CrewAI

**Sujets connexes** : 2.3 (Négociation), 3.3 (RAG), 5.4 (Multi-Agent Market)

---

### 2. RAG (Retrieval Augmented Generation) Avancé

**Tendance** : Le RAG devient la architecture dominante pour les applications IA nécessitant des connaissances spécifiques (domain-specific RAG).

**Applications finance** :
- **Assistant analyste** : RAG sur rapports annuels, news, données macro pour répondre à des questions complexes
- **Compliance automatisée** : RAG sur réglementations (SFDR, Basel III) pour vérifier la conformité
- **Knowledge management** : Systèmes RAG pour capitaliser et partager l'knowledge interne

**Technologies clés** : Vector databases (Pinecone, Weaviate, Chroma), LangChain, LlamaIndex

**Sujets connexes** : 3.3 (RAG Financier), 3.6 (ESG Classification)

---

### 3. Neurosymbolic AI

**Tendance** : Fusion entre réseaux de neurones (perception, pattern recognition) et AI symbolique (raisonnement, règles, explicabilité).

**Applications finance** :
- **XAI robuste** : Systèmes de décision qui expliquent leurs raisonnements en langage naturel + règles formelles
- **Compliance vérifiable** : Systèmes dont les décisions peuvent être formellement vérifiées
- **Hybrid prediction** : Networks pour patterns + règles pour contraintes réglementaires

**Technologies clés** : DeepProbLog, Neural Theorem Provers, Differentiable Logic

**Sujets connexes** : 5.5 (Neurosymbolic Credit), 4.3 (Data Poisoning)

---

### 4. Causal Inference & Causal Discovery

**Tendance** : Passage de la corrélation à la causalité pour les décisions financières critiques.

**Applications finance** :
- **Stress testing causal** : Comprendre les chaînes de causalité dans les scénarios de crise
- **Portfolio construction** : Optimisation basée sur relations causales (pas de corrélations spurious)
- **Attribution de performance** : Comprendre les vraies causes des gains/pertes

**Technologies clés** : DoWhy, CausalML, NOTEARS, PC algorithm

**Sujets connexes** : 5.3 (Causal Discovery), 1.2 (Gaussian Processes)

---

### 5. Conformal Prediction & Uncertainty Quantification

**Tendance** : Méthodes distribution-free pour des intervalles de confiance garantis.

**Applications finance** :
- **Risk management** : Intervalle de confiance garanti pour VaR, CVaR
- **Model risk** : Quantification rigoureuse de l'incertitude des prédictions ML
- **Stress testing** : Scénarios garantis couvrir les extrêmes

**Technologies clés** : MAPIE, Conformalized Quantile Regression

**Sujets connexes** : 5.1 (Conformal Prediction), 1.2 (Gaussian Processes)

---

### 6. LLMs pour Code Generation & Agent Building

**Tendance** : Les LLMs deviennent des outils de production pour générer du code financier robuste.

**Applications finance** :
- **Code generation** : Génération de backtesting engines, risk models, data pipelines
- **Agent frameworks** : LLMs pour créer des agents financiers spécialisés
- **Debugging & testing** : LLMs pour reviewer et améliorer le code financier

**Technologies clés** : GPT-4, Claude 3.5/4, Codex, GitHub Copilot

**Sujets connexes** : Tous (les sujets peuvent bénéficier de l'assistance LLM)

---

### 7. Time-Series Foundation Models

**Tendance** : Modèles foundation pré-entraînés sur des billions de points de données temporelles.

**Applications finance** :
- **Prédiction marchés** : Foundation models pour forecasting multi-asset
- **Anomaly detection** : Modèles pré-entraînés pour détecter anomalies en streaming
- **Few-shot learning** : Adaptation rapide à nouveaux instruments/flux

**Technologies clés** : Chronos (Amazon), TimeGPT, Lag-Llama

**Sujets connexes** : 3.4 (Regime Detection), 1.2 (Gaussian Processes)

---

### 8. Differential Privacy & Federated Learning

**Tendance** : Confidentialité préservant la collaboration pour les données financières sensibles.

**Applications finance** :
- **Collaborative credit scoring** : Banques collaborent sans partager données clients
- **Fraud detection** : FL pour détecter fraude cross-institution
- **Regulatory compliance** : GDPR-compliant ML systems

**Technologies clés** : OpenDP, PySyft, Flower (FL)

**Sujets connexes** : 4.1 (Federated Learning), 4.2 (Homomorphic Encryption)

---

### 9. Generative AI pour Scenarios & Stress Testing

**Tendance** : LLMs pour générer des scénarios économiques réalistes et couvrir les extrêmes.

**Applications finance** :
- **Stress testing** : Génération de scénarios de crise cohérents (inflation, taux, défauts)
- **Monte Carlo augmenté** : Scénarios génératifs plus réalistes que purement statistiques
- **Risk management** : Couverture de black swans via génération de scénarios inédits

**Technologies clés** : GPT-4, Claude, finetuning pour finance

**Sujets connexes** : 5.6 (LLM Scenarios), 1.5 (Stochastic Volatility)

---

### 10. World Models & Model-Based RL

**Tendance** : Apprentissage d'un modèle de l'environnement pour planifier (DreamerV3-style).

**Applications finance** :
- **Market simulation** : World models pour simuler la dynamique de marché
- **Trading strategie** : Planification dans le monde simulé avant exécution réelle
- **What-if analysis** : Explorer contre-factuels pour décisions d'investissement

**Technologies clés** : DreamerV3, Model-Based RL, World Models

**Sujets connexes** : 5.2 (World Models for Trading), 5.4 (Multi-Agent Market)

---

### Conseils pour choisir votre sujet en 2025-2026

1. **Alignement avec votre parcours** : Probas → sujets cat.1, GT → cat.2, ML → cat.3-4
2. **Originalité** : Les sujets cat.5 (Recherche) sont les plus originaux mais plus risqués
3. **Emploiabilité** : RAG, Agents, Federated Learning sont très demandés en 2025-2026
4. **Ambition réaliste** : Visez le niveau "Bon" minimum, "Excellent" si équipe solide

---

## Remarques Finales

- **IA Générative** : Vous êtes encouragés à utiliser l'IA (ChatGPT, Claude, etc.) pour vous aider. L'ambition du projet doit refléter cette capacité.
- **Ressources** : Utilisez les notebooks comme base, mais ne les copiez pas. Le projet doit apporter une valeur ajoutée.
- **Questions** : N'hésitez pas à demander des clarifications sur les sujets.

**Bon courage à tous !**
