<!-- CATALOG-STATUS
series: QuantConnect-Python
pedagogical_count: 66
breakdown: Python=66
maturity: BETA=35, DRAFT=27, ALPHA=4
-->

# QuantConnect Python — le trading algorithmique sous LEAN

[↑ QuantConnect](../README.md) · [Entrée : 01 — configuration et premier backtest](QC-Py-01-Setup.ipynb) · [Stratégies Cloud](#sous-série--stratégies-cloud-qc-py-cloud-)

Comment une idée devient-elle un ordre, un ordre une position, une position un portefeuille — et un portefeuille une performance qui survit à ses frais ? Cette sous-série déroule le métier du trading algorithmique sur la plateforme QuantConnect LEAN : chercher dans un `QuantBook`, déplacer des données, choisir un univers, exécuter, mesurer, puis entraîner des modèles. L'exigence est la même du premier au dernier carnet : distinguer un résultat d'une illusion statistique.

Elle s'adresse aux étudiants et enseignants qui savent programmer en Python et connaissent les bases d'un actif financier (prix, rendement, position). Le parcours principal ne suppose aucune expérience de QuantConnect : le carnet 01 part d'un compte vide. Les carnets de modélisation (à partir de 18) supposent en plus un cours de machine learning ; ceux de calcul stochastique (06, 29) une familiarité avec les probabilités.

> Ces carnets sont des supports de cours à lire sur GitHub ou en local. Pour exécuter un backtest, copier le code dans un projet [QuantConnect Cloud](https://www.quantconnect.com/lab) ; les carnets marqués `[QC CLOUD]` en dépendent et ne s'exécutent pas hors plateforme.

## Comment lire ce README — découverte

Le parcours suit le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : les numéros nus donnent la progression, les lettres approfondissent un palier.

- **Vous découvrez** : suivez le parcours principal de 01 à 46. Chaque étape suppose la précédente ; les prérequis de sa ligne disent à partir de quoi elle se lit.
- **Vous creusez un palier** : ouvrez l'approfondissement correspondant — huit paliers lettrés (05b, 06b, 12b, 14b, 23b, 23c, 28b, 28c) traitent une question que l'étape mère ne fait qu'ouvrir. Ils ne la remplacent pas : le numéro nu reste l'étape du parcours.
- **Vous cherchez des prolongements** : les stratégies Cloud forment une sous-série à part, les cinq carnets de recherche (42 à 46) portent chacun une conclusion transférable, et « Pour aller plus loin » rassemble la méthode commune, l'état d'exécution honnête et les ressources.

Le fil du parcours : les fondations de la plateforme (01-04), les classes d'actifs et l'exécution (05-10), l'analyse et la stratégie (11-17), l'apprentissage automatique et profond (18-31), le renforcement (32-35), la mise en production (40-41), puis cinq expériences de recherche dont la valeur est la méthode de validation autant que le résultat (42-46).

## Parcours principal — lecture guidée et prérequis

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 01 | [Configuration et premier backtest](QC-Py-01-Setup.ipynb) | Créer un projet, lancer un backtest et situer les pièces de l'architecture LEAN : algorithme, données, moteur d'exécution. | Aucun prérequis. Compte QuantConnect gratuit. | La structure de l'algorithme en 02. |
| 02 | [Fondamentaux de la plateforme](QC-Py-02-Platform-Fundamentals.ipynb) | Suivre le cycle de vie d'un `QCAlgorithm` (`Initialize`, `OnData`), brancher les gestionnaires et les événements. | Après 01 ; programmation orientée objet. | Traçabilité des données en 03. |
| 03 | [Gestion des données](QC-Py-03-Data-Management.ipynb) | Interroger l'historique, chaîner des consolidators et faire cohabiter plusieurs échelles de temps. | Après 02 ; pandas. | Le travail dans le `QuantBook` en 04. |
| 04 | [Workflow de recherche](QC-Py-04-Research-Workflow.ipynb) | Explorer dans un `QuantBook`, confronter une stratégie simple au buy-and-hold de référence, puis transférer le code vers un algorithme. | Après 03 ; pandas et matplotlib. | [Aperçu](#aperçu--le-trading-quantitatif-en-images) figure 04. |
| 05 | [Sélection d'univers](QC-Py-05-Universe-Selection.ipynb) | Construire un univers dynamique et le filtrer sur des critères fondamentaux. | Après 04. | Critère fondamental détaillé en 05b. |
| 06 | [Trading d'options](QC-Py-06-Options-Trading.ipynb) | Lire une chaîne d'options, ses grecques, et couvrir une position. | Après 05 ; notion de payoff. | Valorisation reconstruite en 06b et en 29. |
| 07 | [Contrats à terme et devises](QC-Py-07-Futures-Forex.ipynb) | Manipuler contrats à terme et paires de devises, puis couvrir une exposition. | Après 06. | Change et portage en 16. |
| 08 | [Stratégies multi-actifs](QC-Py-08-Multi-Asset-Strategies.ipynb) | Allouer sur plusieurs classes d'actifs et observer la corrélation glisser sous stress. | Après 07. | [Aperçu](#aperçu--le-trading-quantitatif-en-images) figure 08. |
| 09 | [Types d'ordres](QC-Py-09-Order-Types.ipynb) | Choisir entre market, limit, stop, trailing et ordres combinés, et mesurer ce que chacun coûte. | Après 08. | Coûts d'exécution en 14b. |
| 10 | [Gestion du risque et du portefeuille](QC-Py-10-Risk-Portfolio-Management.ipynb) | Dimensionner une position, mesurer le drawdown, comparer stops fixe, ATR et suiveur, puis pondérer sans inverser la covariance (parité hiérarchique du risque). | Après 09 ; statistiques élémentaires. | [Aperçu](#aperçu--le-trading-quantitatif-en-images) figure 10. |
| 11 | [Indicateurs techniques](QC-Py-11-Technical-Indicators.ipynb) | Utiliser les indicateurs natifs et écrire les siens. | Après 10. | Fenêtres et paramètres en 15. |
| 12 | [Backtesting et analyse](QC-Py-12-Backtesting-Analysis.ipynb) | Lire un backtest autrement que par un Sharpe : dispersion, queues, bêta au benchmark. | Après 11. | Validité statistique en 12b ; [aperçu](#aperçu--le-trading-quantitatif-en-images) figure 12. |
| 13 | [Modèles alpha](QC-Py-13-Alpha-Models.ipynb) | Composer des signaux dans l'Alpha Framework et les combiner. | Après 12. | Recherche d'alphas en 42. |
| 14 | [Construction de portefeuille et exécution](QC-Py-14-Portfolio-Construction-Execution.ipynb) | Passer du poids cible à l'ordre exécuté. | Après 13. | Liquidité et coûts en 14b. |
| 15 | [Optimisation de paramètres](QC-Py-15-Parameter-Optimization.ipynb) | Optimiser une grille sans se raconter d'histoire : walk-forward et hors-échantillon. | Après 14. | Multiplication des tests en 12b. |
| 16 | [Données alternatives](QC-Py-16-Alternative-Data.ipynb) | Brancher des données alternatives, du sentiment et des fondamentaux. | Après 15. | Texte en signal en 17. |
| 17 | [Analyse de sentiment](QC-Py-17-Sentiment-Analysis.ipynb) | Transformer un texte en signal mesurable. | Après 16 ; notions de NLP. | Sentiment financier en Cloud-01. |
| 18 | [Ingénierie de features](QC-Py-18-ML-Features-Engineering.ipynb) | Fabriquer des features qui ne fuient pas le futur. | Après 17 ; bases de scikit-learn. | Fuite temporelle en 20. |
| 19 | [Classification supervisée](QC-Py-19-ML-Supervised-Classification.ipynb) | Classer, produire des signaux d'achat et de vente, valider en walk-forward. | Après 18. | [Aperçu](#aperçu--le-trading-quantitatif-en-images) figure 19. |
| 20 | [Régression et prédiction](QC-Py-20-ML-Regression-Prediction.ipynb) | Prédire une valeur et comparer linéaire, arbres et réseau sous multi-graines et Diebold-Mariano. | Après 19. | Doctrine de validation en 42. |
| 21 | [Optimisation de portefeuille par ML](QC-Py-21-Portfolio-Optimization-ML.ipynb) | Confier les poids à un modèle plutôt qu'à une formule. | Après 20. | Contraintes de risque en 35. |
| 22 | [Apprentissage profond — LSTM](QC-Py-22-Deep-Learning-LSTM.ipynb) | Faire apprendre une dynamique temporelle à un LSTM. | Après 21 ; PyTorch. | Entraînement complet en 30. |
| 23 | [Modèles à espace d'état](QC-Py-23-State-Space-Models.ipynb) | Remplacer l'attention par un état récurrent (S4, Mamba) sur des séries financières. | Après 22. | Variantes en 23b et 23c. |
| 24 | [Autoencodeurs et détection d'anomalies](QC-Py-24-Autoencoders-Anomaly.ipynb) | Détecter l'anomalie par défaut de reconstruction. | Après 23. | Régimes en 28. |
| 25 | [Apprentissage par renforcement — introduction](QC-Py-25-Reinforcement-Learning.ipynb) | Poser un environnement de trading et un premier agent. | Après 24. | DQN en 32, PPO en 33, SAC et A2C en 34. |
| 26 | [Signaux de trading par LLM](QC-Py-26-LLM-Trading-Signals.ipynb) | Interroger un modèle de langage et en tirer un signal utilisable — avec ses coûts et sa variance. | Après 25 ; clé API. | Agent multi-LLM en 44 ; étalon en 46. |
| 27 | [Mise en production](QC-Py-27-Production-Deployment.ipynb) | Déployer, surveiller, et savoir quand arrêter. | Après 26. | Paper trading en 40 et 41. |
| 28 | [Détection de régimes de marché](QC-Py-28-Market-Regime-Detection.ipynb) | Segmenter le marché en régimes et en tirer une allocation. | Après 27 ; séries temporelles. | Régimes macro en 28b, prétraitement des facteurs en 28c. |
| 29 | [Valorisation d'un dérivé](QC-Py-29-Derivatives-Valuation.ipynb) | Valoriser le même contrat par Black-Scholes, arbre binomial et Monte-Carlo : précision, convergence, flexibilité, coût, liquidité. | Après 28 ; calcul stochastique élémentaire. | Moteurs reconstruits à la main en 06b. |
| 30 | [Entraînement d'un LSTM](QC-Py-30-LSTM-Training.ipynb) | Entraîner un LSTM multi-actifs avec checkpoints et suivi des courbes. | Après 29 ; GPU. | Évaluation honnête en 12b. |
| 31 | [Entraînement d'un Transformer](QC-Py-31-Transformer-Training.ipynb) | Entraîner un encodeur Transformer multi-actifs. | Après 30 ; GPU. | Variantes spécialisées en 23b. |
| 32 | [Agent DQN](QC-Py-32-RL-DQN-Trading.ipynb) | Entraîner un agent par essais et erreurs : récompense, exploration, évaluation périodique. | Après 31 ; GPU. | [Aperçu](#aperçu--le-trading-quantitatif-en-images) figure 32. |
| 33 | [Agent PPO](QC-Py-33-RL-PPO-Trading.ipynb) | Passer au *clipped surrogate* de PPO et comparer au DQN. | Après 32. | Comparatif d'algorithmes en 34. |
| 34 | [SAC et A2C](QC-Py-34-RL-SAC-A2C-Trading.ipynb) | Comparer deux familles d'acteurs-critiques sur le même environnement. | Après 33. | Allocation par agent en 35. |
| 35 | [Construction de portefeuille par RL](QC-Py-35-RL-Portfolio-Construction.ipynb) | Faire décider l'allocation par l'agent, sous contrainte de risque. | Après 34. | Noyau de risque déterministe en 45. |
| 40 | [Paper trading — Binance](QC-Py-40-PaperTrading-Binance.ipynb) | Passer du backtest au paper trading sur un exchange crypto. | Après 35 ; comptes de courtage. | Contrôle de risque en 45. |
| 41 | [Paper trading — Interactive Brokers](QC-Py-41-PaperTrading-IBKR.ipynb) | Le même passage côté actions et contrats à terme. | Après 40. | Étalon de compétence en 46. |
| 42 | [Alpha mining par évolution](QC-Py-42-Alpha-Mining-Evolution.ipynb) | Faire évoluer des expressions alpha (arbres d'opérateurs) et confronter le moteur à une baseline de facteurs fixes, à budget égal. | Après 41 ; algorithmes évolutionnaires. | Conclusion transférable ci-dessous. |
| 43 | [Séries synthétiques par diffusion](QC-Py-43-Diffusion-Series-Synthetiques.ipynb) | Écrire un DDPM en `torch`, engendrer des fenêtres de rendements et juger le générateur contre les faits stylisés de la série réelle. | Après 42 ; PyTorch ; réseau. | Contrôle négatif bootstrap ci-dessous. |
| 44 | [Agent de trading multi-LLM](QC-Py-44-Agent-Trading-Multi-LLM.ipynb) | Réduire le cadre TradingAgents : deux analystes, un débat bull/bear borné, un PM qui tranche, une mémoire soldée — et mesurer ce que la délibération apporte. | Après 43 ; clé API ; semantic-kernel. | Rejeu depuis journal ci-dessous. |
| 45 | [Noyau de risque déterministe](QC-Py-45-Noyau-Risque-Deterministe.ipynb) | Ablations d'un noyau invariant de règles de risque, sans LLM, contre des témoins qui séparent son effet de la simple baisse d'exposition. | Après 44 ; réseau. | Détail des six variantes ci-dessous. |
| 46 | [Étalon externe FinanceBench](QC-Py-46-External-Etalon-FinanceBench.ipynb) | Juger l'organ LLM de la série contre un étalon indépendant, avec témoin négatif et comparaison cross-LLM. | Après 45 ; clé API ; dataset hors dépôt. | Protocole des trois bras ci-dessous. |

Les numéros 36 à 39 ne sont pas attribués : la numérotation conserve les trous historiques du fil plutôt que de les combler après coup.

## Approfondissements — Recherche

### Paliers lettrés

Huit carnets approfondissent une étape du parcours sans la remplacer. Leur numéro porte la lettre de l'étape qu'ils creusent.

| Palier | Notebook | Ce qu'il approfondit |
|---|---|---|
| 05b | [F-Score de Piotroski](QC-Py-05b-FScore-Piotroski.ipynb) | Le critère fondamental de 05, calculé sur données réelles : les neuf sous-scores, la convention de datation (article de 2000 contre données du jour), la critique de liquidité et une variance de petit univers mesurée. |
| 06b | [Valorisation de dérivés, from scratch](QC-Py-06b-Derivatives-Valuation-From-Scratch.ipynb) | Les trois moteurs de valorisation reconstruits à la main pour compléter 29 : put américain, option asiatique arithmétique, variables de contrôle. Jumeau C# : [QC-06b-Valorisation-Derives-CSharp](../CSharp/QC-06b-Valorisation-Derives-CSharp.ipynb). |
| 12b | [Validité du backtest](QC-Py-12b-Backtest-Validity.ipynb) | La question que 12 laisse ouverte : un Sharpe de 0,2 prouve-t-il quelque chose ? Erreur-type asymptotique (Lo, 2002), PSR et ses deux pièges de saisie, multiplication des tests et faux positifs. |
| 14b | [Liquidité et coûts d'exécution](QC-Py-14b-Liquidity-Execution-Costs.ipynb) | Ce que 14 suppose gratuit : proxys de liquidité (ADV, Amihud, Corwin-Schultz), loi racine, capacité d'une stratégie, stress COVID réel. |
| 23b | [PatchTST et iTransformer](QC-Py-23b-PatchTST-iTransformer.ipynb) | Les transformers spécialisés séries temporelles, à comparer aux modèles à espace d'état de 23 sur les mêmes données. |
| 23c | [TimesFM, modèle de fondation](QC-Py-23c-TimesFM-Foundation-Models.ipynb) | Le zéro-shot d'un modèle de fondation : univarié, multivarié, covariables et quantiles — ce qu'apporte un modèle pré-entraîné face à 22 et 23. |
| 28b | [Macro et cycles](QC-Py-28b-Macro-Cycle-Regimes.ipynb) | Le diagnostic de 28 étendu : indicateur composite borné, passage des indicateurs à un budget de risque, avec un run QC Cloud 2016-2026. |
| 28c | [Prétraitement des facteurs](QC-Py-28c-Factor-Preprocessing-Regime.ipynb) | Ce que la détection de régime suppose acquis : différenciation fractionnaire, standardisation et ACP, comparées à la classe majoritaire (port du livre 06/02). |

### Autour de 42 — ce qu'un moteur de recherche peut produire

Plutôt que de coder un facteur à la main, le carnet **fait évoluer des expressions alpha** avec `deap`, puis les confronte à une baseline de facteurs fixes. Un bras LLM propose des expressions dans la même grammaire, au même budget d'évaluations et avec la même fitness : c'est le pont entre la série [Search](../../Search/README.md) (algorithmes évolutionnaires), les carnets LLM et la série QuantConnect (validation financière).

La méthode de validation est l'objet du carnet autant que le résultat : walk-forward en 5 blocs, 4 graines, coûts de transaction de 10 points de base, Diebold-Mariano à critère directionnel. Le verdict hors échantillon **net de frais** est `BEATS` pour le bras évolution — le passage aux Sharpe nets renverse le verdict brut d'avant coûts — et `INCONCLUSIVE` pour le bras LLM, plus précis au quotidien mais quatre fois plus dispersé entre graines. Le bras évolution rejoue hors ligne ; le bras LLM fait de vrais appels d'API (clé requise, graine passée au modèle).

### Autour de 43 — un générateur se juge sur ce qu'il engendre

Le carnet écrit un **DDPM** en `torch` — pas une bibliothèque — qui apprend la distribution de fenêtres de rendements et en engendre de nouvelles. Ce qui compte n'est pas la perte d'entraînement mais la **fidélité aux faits stylisés** de la série réelle et l'utilité mesurée des données engendrées : contrôle négatif par bootstrap i.i.d., augmentation évaluée sur 5 blocs et 4 graines.

Le générateur bat le bootstrap sur le regroupement de volatilité (`acf_r2_1` à +0,206 contre −0,018) sans égaler le réel (+0,460) ; l'augmentation reste `INCONCLUSIF` (écart/σ de −0,44, Diebold-Mariano non significatif). Données prises sur yfinance (SPY, 2 515 rendements log quotidiens) : le carnet demande un accès réseau. Sa conclusion transférable est méthodologique — une perte de débruitage qui décroît ne dit rien de la qualité du générateur.

### Autour de 44 — ce que la délibération apporte

Réduction pédagogique du cadre **TradingAgents** (Xiao et al., arXiv:2412.20138) : deux analystes (momentum, risque) nourrissent un débat bull/bear borné à deux tours via `AgentGroupChat` (semantic-kernel, organe natif de la série SemanticKernel), un PM tranche LONG/FLAT/SHORT avec une prévision chiffrée, et une mémoire de décisions soldées journalise chaque décision puis la solde contre le rendement réalisé.

Le protocole compare le cadre complet à un appel single-shot sur les mêmes contextes : 4 graines, pertes appariées, Diebold-Mariano Newey-West, 10 points de base par côté, 288 appels inscrits dans un journal JSONL. Le rejeu strict refait la campagne sans aucun appel, à l'identique ; le rejeu mixte teste une consigne modifiée à coût nul. Verdict : `INCONCLUSIVE` (écart de −0,085 point de pourcentage, ratio de −0,45 σ, p = 0,45) — quatre exécutions du même code ont rendu des ratios de −0,45 à +2,41, et quatre graines ne mesurent pas cette variance.

### Autour de 45 — une règle de risque se juge par ablation

Le système **Steward** (Feng et al., arXiv:2610.30557) confie le choix des lignes à des agents LLM mais fait passer chaque ordre par un noyau invariant de règles fixes : stop à 2 ATR sous l'entrée, plafond de 40 % par groupe, exposition nette d'au plus 90 %, aucune vente à découvert, coupe-circuit après une séance à −3 %. Le carnet reproduit l'ablation du noyau **seul**, sans LLM, sur un univers d'ETF en quatre groupes, avec 5 points de base par côté.

Moteur journalier vectorisé (yfinance, 2015-2026), mêmes entrées avec et sans noyau, tirages aléatoires sur 50 graines, six variantes d'ablation et un verdict pré-enregistré à trois jambes contre deux témoins — dont une exposition de 90 % sans aucune autre règle. Le noyau réduit le drawdown maximal sur chacune des 50 graines sans coûter de rendement médian : verdict `BEATS`. La répartition entre règles s'inverse par rapport au papier : sur ces ETF, ce sont les stops qui font le travail et le coupe-circuit presque rien.

### Autour de 46 — un étalon externe, avec témoin négatif

L'organ LLM des carnets (`gpt-5.6-luna`) est jugé contre un **étalon indépendant** : la strate numérique intégrale de **FinanceBench**, 50 items sans échantillonnage, chargée hors dépôt (licence CC BY-NC 4.0 — ni le jeu de données ni les réponses brutes n'entrent dans le dépôt). Trois bras, 150 appels, même point d'accès que 26 et 44.

Le témoin négatif porte le sens de la mesure : le même modèle, question nue, s'effondre de 92,1 % à 25,0 % (46 réponses sur 50 sans nombre). L'étalon mesure donc la compétence du pipeline — rôle, contexte, format — et non la question seule. À protocole identique, `luna` (92,1 %) est deux fois plus efficace que `sonnet` (47,7 %) sur l'extraction numérique de 10-K. Tolérance relative de 1 %, déclarée et non implicite.

## Sous-série — stratégies Cloud (QC-Py-Cloud-*)

Quinze carnets exécutés sur QuantConnect Cloud, hors du parcours principal : ils documentent des stratégies complètes, souvent issues de projets étudiants anonymisés, dont le backtest vit sur la plateforme et non dans le carnet. Chacun indique dans son en-tête s'il est un document de backtest (markdown seul) ou un carnet exécutable.

| # | Notebook | Stratégie |
|---|---|---|
| 01 | [FinBERT — sentiment](QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | Sentiment financier par FinBERT |
| 02 | [Classification ML](QC-Py-Cloud-02-ML-Classification.ipynb) | Classification de texte et sentiment |
| 03 | [Parité de risque](QC-Py-Cloud-03-Risk-Parity.ipynb) | Risk parity |
| 03b | [Parité de risque composite](QC-Py-Cloud-03b-RiskParity-Composite.ipynb) | Risk parity composite |
| 04 | [Retour à la moyenne](QC-Py-Cloud-04-MeanReversion.ipynb) | Mean reversion |
| 05 | [Prévision par MLP](QC-Py-Cloud-05-MLP-Forecasting.ipynb) | Réseau de neurones simple |
| 06 | [PCA — arbitrage statistique](QC-Py-Cloud-06-PCA-StatArb.ipynb) | Statistical arbitrage par composantes principales |
| 07 | [CNN temporel](QC-Py-Cloud-07-TemporalCNN.ipynb) | Prédiction de direction (livre, ch. 6) |
| 08 | [Facteur de valeur](QC-Py-Cloud-08-ValueFactor-ZScore.ipynb) | Sélection multi-facteurs fondamentaux |
| 09 | [Option Wheel](QC-Py-Cloud-09-OptionWheel.ipynb) | Le paradoxe du taux de réussite élevé |
| 10 | [DQN](QC-Py-Cloud-10-RL-DQN-Trading.ipynb) | Renforcement profond (variante avancée) |
| 11 | [Changement de régime](QC-Py-Cloud-11-RegimeSwitching.ipynb) | Régime switching |
| 12 | [Rotation sectorielle](QC-Py-Cloud-12-SectorRotation-Momentum.ipynb) | Rotation sectorielle et momentum multi-actifs |
| 13 | [Ciblage de volatilité](QC-Py-Cloud-13-VolTargeting.ipynb) | Volatility targeting |
| 14 | [Dual Momentum](QC-Py-Cloud-14-DualMomentum.ipynb) | Dual momentum |

## État d'exécution — audit daté

Suite à l'audit du 5 mai 2026, voici l'état honnête de chaque carnet, mis à jour au 2 juillet 2026. Aucun output théâtral — une cellule qui imprime des métadonnées en se faisant passer pour une exécution — ne subsiste après le nettoyage de la PR `chore/qc-strip-fake-outputs`. Les comptes de cellules ne sont pas tenus ici : ils dérivent à chaque ré-exécution, et relèvent du catalogue généré (`COURSE_CATALOG.generated.*`).

**Légende** : **EXÉCUTÉ** = cellules avec des outputs réels issus d'une exécution kernel ; **NON EXÉCUTÉ** = code source réel jamais exécuté (préférable au théâtre) ; **doc cloud** = carnet markdown documentant un backtest réalisé sur la plateforme.

| Notebook | Statut | Détail |
|----------|--------|--------|
| QC-Py-01-Setup | NON EXÉCUTÉ | |
| QC-Py-02-Platform-Fundamentals | NON EXÉCUTÉ | |
| QC-Py-03-Data-Management | NON EXÉCUTÉ | |
| QC-Py-04-Research-Workflow | NON EXÉCUTÉ | |
| QC-Py-05-Universe-Selection | NON EXÉCUTÉ | |
| QC-Py-05b-FScore-Piotroski | EXÉCUTÉ | CPU local (yfinance/numpy/scipy), données réelles sur 14 titres |
| QC-Py-06-Options-Trading | NON EXÉCUTÉ | |
| QC-Py-06b-Derivatives-Valuation-From-Scratch | EXÉCUTÉ | CPU local (numpy/scipy) |
| QC-Py-07-Futures-Forex | NON EXÉCUTÉ | |
| QC-Py-08-Multi-Asset-Strategies | NON EXÉCUTÉ | |
| QC-Py-09-Order-Types | NON EXÉCUTÉ | |
| QC-Py-10-Risk-Portfolio-Management | NON EXÉCUTÉ | |
| QC-Py-11-Technical-Indicators | NON EXÉCUTÉ | |
| QC-Py-12-Backtesting-Analysis | NON EXÉCUTÉ | |
| QC-Py-12b-Backtest-Validity | EXÉCUTÉ | |
| QC-Py-13-Alpha-Models | NON EXÉCUTÉ | |
| QC-Py-14-Portfolio-Construction-Execution | NON EXÉCUTÉ | |
| QC-Py-14b-Liquidity-Execution-Costs | EXÉCUTÉ | CPU local (yfinance/pandas/numpy), figures committées |
| QC-Py-15-Parameter-Optimization | NON EXÉCUTÉ | |
| QC-Py-16-Alternative-Data | NON EXÉCUTÉ | |
| QC-Py-17-Sentiment-Analysis | NON EXÉCUTÉ | |
| QC-Py-18-ML-Features-Engineering | EXÉCUTÉ | |
| QC-Py-19-ML-Supervised-Classification | NON EXÉCUTÉ | |
| QC-Py-20-ML-Regression-Prediction | NON EXÉCUTÉ | |
| QC-Py-21-Portfolio-Optimization-ML | NON EXÉCUTÉ | |
| QC-Py-22-Deep-Learning-LSTM | NON EXÉCUTÉ | |
| QC-Py-23-State-Space-Models | EXÉCUTÉ | |
| QC-Py-23b-PatchTST-iTransformer | EXÉCUTÉ | |
| QC-Py-23c-TimesFM-Foundation-Models | EXÉCUTÉ | |
| QC-Py-24-Autoencoders-Anomaly | EXÉCUTÉ | |
| QC-Py-25-Reinforcement-Learning | EXÉCUTÉ | |
| QC-Py-26-LLM-Trading-Signals | NON EXÉCUTÉ | |
| QC-Py-27-Production-Deployment | NON EXÉCUTÉ | |
| QC-Py-28-Market-Regime-Detection | NON EXÉCUTÉ | |
| QC-Py-28b-Macro-Cycle-Regimes | EXÉCUTÉ | cellules locales + run QC Cloud 2016-2026 (diagnostic vers allocation) |
| QC-Py-28c-Factor-Preprocessing-Regime | EXÉCUTÉ | cellules locales sur série synthétique à régimes (port du livre 06/02, #18958) |
| QC-Py-29-Derivatives-Valuation | EXÉCUTÉ | Black-Scholes, arbre CRR et Monte-Carlo : convergence, grecques, scénario de liquidité |
| QC-Py-30-LSTM-Training | EXÉCUTÉ | |
| QC-Py-31-Transformer-Training | EXÉCUTÉ | |
| QC-Py-32-RL-DQN-Trading | EXÉCUTÉ | |
| QC-Py-40-PaperTrading-Binance | EXÉCUTÉ | |
| QC-Py-41-PaperTrading-IBKR | EXÉCUTÉ | |
| QC-Py-42-Alpha-Mining-Evolution | EXÉCUTÉ | panier crypto local (10 actifs, 2020-09 à 2025-03), verdicts nets de frais : évolution `BEATS`, bras LLM `INCONCLUSIVE` |
| QC-Py-Cloud-01-FinBERT-Sentiment | EXÉCUTÉ | |
| QC-Py-Cloud-02-ML-Classification | EXÉCUTÉ | |
| QC-Py-Cloud-12-SectorRotation-Momentum | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-14-DualMomentum | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-03-Risk-Parity | EXÉCUTÉ | |
| QC-Py-Cloud-03b-RiskParity-Composite | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-04-MeanReversion | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-05-MLP-Forecasting | EXÉCUTÉ | |
| QC-Py-Cloud-11-RegimeSwitching | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-13-VolTargeting | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-06-PCA-StatArb | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-07-TemporalCNN | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-08-ValueFactor-ZScore | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-09-OptionWheel | doc cloud | markdown seul — backtest sur QC Cloud |
| QC-Py-Cloud-10-RL-DQN-Trading | EXÉCUTÉ | |
| QC-Py-33-RL-PPO-Trading | EXÉCUTÉ | |
| QC-Py-34-RL-SAC-A2C-Trading | EXÉCUTÉ | |
| QC-Py-35-RL-Portfolio-Construction | EXÉCUTÉ | |
| QC-Py-Dataset-Workflow | NON EXÉCUTÉ | |
| QC-Py-43-Diffusion-Series-Synthetiques | EXÉCUTÉ | cellules locales sur SPY (yfinance, 2 515 rendements log) — diffusion contre bootstrap, augmentation `INCONCLUSIF` |
| QC-Py-44-Agent-Trading-Multi-LLM | EXÉCUTÉ | campagne de 288 appels LLM journalisés, rejeu strict et mixte, noyau de risque de 45 greffé — verdicts §C `INCONCLUSIVE` |
| QC-Py-45-Noyau-Risque-Deterministe | EXÉCUTÉ | ablation du noyau de Steward sur ETF (yfinance, 2015-2026), sans LLM — `BEATS` sur le drawdown |
| QC-Py-46-External-Etalon-FinanceBench | EXÉCUTÉ | FinanceBench (50 items numériques, strate intégrale), 3 bras × 50 items : `luna-plein` 92,1 %, `luna-naif` 25,0 %, `sonnet-plein` 47,7 %, tolérance 1 % |

**Politique** : un carnet NON EXÉCUTÉ qui porte du code réel vaut mieux qu'un carnet aux outputs théâtraux. Les motifs suivants sont détectés comme erreurs par [`scripts/validate_qc_notebooks.py`](../scripts/validate_qc_notebooks.py) : `print("Algorithme charge : {len(qc_code)} caracteres")` (métadonnée d'une chaîne), `print("Workflow de deploiement...")` (workflow imprimé comme texte), `print("Placeholder pour les resultats")` (résultats codés en dur), `print("Resultats sync depuis QC Cloud projet XXXX")` (sans récupération réelle). Un carnet NON EXÉCUTÉ doit être exécuté — kernel local pour les indépendants, QC Cloud pour ceux qui exigent un `QuantBook` — avant de pouvoir être marqué EXÉCUTÉ. Aucun raccourci n'est toléré.

## Classification des carnets

Les carnets de ce dossier sont classés par **modalité d'exécution** : quantbook QC Cloud, compagnon de recherche, recherche autonome locale, ou support de cours qui embarque une chaîne `QCAlgorithm`. Le dossier voisin [`projects/`](../projects/) utilise un 4-types **distinct**, par **robustesse** de la stratégie déployable. Les deux périmètres sont disjoints — ce dossier porte des supports de cours, `projects/` des stratégies backtestées — et le croisement ne se déduit pas : un carnet de recherche autonome n'est pas une stratégie de production, et un projet robuste n'a pas forcément de carnet pédagogique ici. La répartition courante et la classification détaillée vivent dans [docs/qc/qc-strategies-status.md](../../../docs/qc/qc-strategies-status.md) et dans le catalogue généré ; elles ne sont pas recopiées ici, où elles dériveraient.

## Aperçu — le trading quantitatif en images

Chaque figure est extraite des sorties réelles d'un carnet et replacée au plus près du concept qu'elle illustre. La provenance détaillée (cellule, poids, texte alternatif) est documentée dans [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

**[04 — Le workflow de recherche QuantBook.](QC-Py-04-Research-Workflow.ipynb)** Le `QuantBook` autorise l'exploration interactive avant l'algorithmation : on y confronte une stratégie simple (croisement de moyennes mobiles) au buy-and-hold de référence sur SPY. La courbe de capital révèle quand la stratégie bat le marché passivement et quand elle le suit — le premier geste de la recherche quantitative.

<p align="center"><a href="QC-Py-04-Research-Workflow.ipynb"><img src="assets/readme/quantpy04-research-buyhold.png" width="540" alt="Workflow de recherche QuantBook : deux sous-graphiques empilés produits sur SPY (juil. 2025 → mai 2026). Haut — prix SPY (noir) avec SMA 50 (bleu) et SMA 200 (rouge) superposées, range 580-760 $. Bas — comparaison des returns cumulatifs normalisés (axe Y = 0.95 → 1.25) : Buy & Hold (gris, pic ~+25 % atteint en 2026-04) vs SMA Crossover (vert, pic ~+15 % après une longue période plate 2025-07 → 2026-02 et un drawdown à 0.97 vers 2026-03). Démontre le crossover SMA 50/200 comme signal de tendance long terme."></a></p>

**[08 — Corrélations glissantes, ou la faillite du modèle statique.](QC-Py-08-Multi-Asset-Strategies.ipynb)** La corrélation moyenne entre deux actifs cache sa vérité : elle évolue dans le temps et s'effondre précisément lors des périodes de stress où la diversification était censée protéger le portefeuille. La corrélation glissante rend ce risque visible — pourquoi l'allocation statique est un leurre.

<p align="center"><a href="QC-Py-08-Multi-Asset-Strategies.ipynb"><img src="assets/readme/quantpy08-rolling-corr.png" width="540" alt="Stratégies multi-actifs SPY vs TLT : deux sous-graphiques empilés sur 4 ans (2020-01 → 2024-01). Haut — returns cumulés SPY (bleu marine, pic ~+110 %) vs TLT (orange, pic ~+70 %), avec un bandeau vertical rouge « Periode stress » couvrant ~3 mois en 2021-Q1 (zone COVID / choc taux, TLT dépasse brièvement SPY). Bas — corrélation glissante 60 jours (SPY-TLT) en violet, oscillant entre -0.8 (corrélation fortement négative) et -0.2, avec une ligne pointillée rouge horizontale « Moyenne : -0.45 ». Pendant le bandeau rouge, la corrélation plonge vers -0.82 (diversification actions/obligations temporairement KO sous stress)."></a></p>

**[10 — Le coût d'un stop-loss.](QC-Py-10-Risk-Portfolio-Management.ipynb)** Protéger une position a un prix. Les stops fixes coupent net, les stops trailing suivent la hausse mais se déclenchent sur le bruit, les stops volatilité s'adaptent au régime de marché. Sur un même prix simulé, les trois types laissent des traces différentes — choisir un stop, c'est choisir quel risque on accepte. La partie 4 se clôt sur le Hierarchical Risk Parity : pondérer un portefeuille multi-actifs sans jamais inverser la matrice de covariance, en trois étapes (clustering, quasi-diagonalisation, bisection récursive) — avec la leçon mesurée d'un univers crypto dominé par un seul actif, où la meilleure allocation hiérarchique reste sous le benchmark.

<p align="center"><a href="QC-Py-10-Risk-Portfolio-Management.ipynb"><img src="assets/readme/quantpy10-stoploss.png" width="540" alt="Gestion des risques stop-loss : deux sous-graphiques empilés sur ~75 jours (2023-01-01 → 2023-03-20). Haut — prix simulé (bleu) avec trois stops horizontaux : Fixed Stop 5 % = $97.01 (rouge tirets), ATR Stop 2× = $95.60 (orange tirets-points, plus bas que le fixed car plus conservateur), Support Stop SMA-2 % (vert tirets, mobile), plus le point d'entrée $102.12 (gros point bleu + ligne verticale pointillée). Bas — distance au stop en %, courbes ATR Stop (orange clair, varie 5-18 %) + Fixed Stop (rose pâle, fixe 5 %) + Support Stop (vert, varie 0-10 %). Démontre la comparaison stop-loss fixe vs adaptatif (ATR) vs trend-following (SMA) : l'ATR stop s'élargit quand la volatilité monte (protection anti-whipsaw), le SMA stop suit la tendance."></a></p>

**[12 — Le profil risque-rendement d'un backtest.](QC-Py-12-Backtesting-Analysis.ipynb)** La richesse d'un backtest ne tient pas dans un seul Sharpe : le scatter des rendements quotidiens de la stratégie contre son benchmark expose la dispersion, les queues et la fréquence des bons et mauvais jours. C'est la signature statistique complète du comportement de la stratégie.

**[12b — Un Sharpe de 0,2 prouve-t-il quoi que ce soit ?](QC-Py-12b-Backtest-Validity.ipynb)** Non, si le backtest couvre moins de dix ans : l'erreur-type asymptotique du Sharpe annualisé vaut environ `1/sqrt(N_années)` (Lo, 2002) — sur 7 ans, ±0,38. Un Sharpe mesuré à 0,2 est statistiquement indistinguable d'une stratégie sans aucun bord. Le carnet construit la lecture honnête d'un backtest : intervalle de confiance du Sharpe, PSR et ses deux pièges de saisie, multiplication des tests et faux positifs.

<p align="center"><a href="QC-Py-12-Backtesting-Analysis.ipynb"><img src="assets/readme/quantpy12-backtest-scatter.png" width="540" alt="Analyse de backtest : deux sous-graphiques côte-à-côte sur 2 ans (2022-01 → 2024-01). Gauche — scatter Strategy Returns (%) vs Benchmark Returns (%) avec droite de régression rouge en pointillés β = 0.44 (la stratégie amplifie modérément le benchmark), ~250 points bleus dispersés dans le quadrant [-3 %, +3 %]², axes croisés à (0, 0). Droite — equity curves comparées : Strategie (bleu marine) finit à 1.42, Benchmark (gris tirets) finit à 1.47, baseline noire horizontale à 1.00. La Strategie reste sous le Benchmark toute l'année 2022 (sous-performance), puis dépasse en 2023-07 → 2023-10 (pic ~1.50). Démontre la mesure du β (sensibilité au benchmark) et le profil risque/rendement : β=0.44 < 1 = stratégie défensive (moins volatile que le marché)."></a></p>

**[19 — La validation walk-forward, ou l'honnêteté temporelle.](QC-Py-19-ML-Supervised-Classification.ipynb)** Un modèle entraîné une fois puis testé sur tout l'échantillon triche avec le temps. La validation walk-forward décale une fenêtre d'entraînement puis re-teste, fold après fold, en mimant le retrain périodique qu'exige un trading réel. L'accuracy par fold révèle la robustesse — ou l'effondrement — hors échantillon.

<p align="center"><a href="QC-Py-19-ML-Supervised-Classification.ipynb"><img src="assets/readme/quantpy19-walkforward.png" width="540" alt="Validation walk-forward d'un classifieur supervisé : deux sous-graphiques empilés sur 14 mois (2023-03 → 2024-05). Haut — accuracy par fold (bar chart bleu, axe Y = 0.0 → 1.0, axe X = 1 → 14) avec des lignes horizontales de référence : Mean Accuracy = 0.874 (rouge pointillés, performance moyenne élevée) et Random Baseline = 0.5 (gris pointillés, baseline 50/50). Distribution hétérogène : folds 5/6/10/11 ≈ 1.0 (excellents), folds 7 ≈ 0.50 (le plus mauvais, à peine au-dessus du random), folds 3/9 ≈ 0.65 (sous-performances ponctuelles). Bas — accuracy cumulée au fil du temps (courbe bleue pleine, aire bleu clair sous la courbe), démarrant à 1.0 puis convergeant vers ~0.87 sur 14 mois malgré les folds médiocres. Démontre la stabilité OOS du modèle (accuracy cumulée reste > 0.85)."></a></p>

**[32 — L'agent qui apprend à trader.](QC-Py-32-RL-DQN-Trading.ipynb)** Le deep reinforcement learning entraîne un agent par essais et erreurs : chaque épisode ajuste sa politique pour maximiser la récompense cumulée. La courbe des récompenses par épisode montre la transition de l'exploration vers l'exploitation — le moment où l'agent cesse de tâtonner et commence à exploiter ce qu'il a appris.

<p align="center"><a href="QC-Py-32-RL-DQN-Trading.ipynb"><img src="assets/readme/quantpy32-dqn-training.png" width="560" alt="Entraînement DQN (Deep Q-Network) sur trading : quatre sous-graphiques en grille 2×2 sur 200 épisodes. Haut-gauche — reward par épisode (axe Y = -75 à +150), courbe bleue brute très volatile + moyenne mobile MA-10 rouge qui passe de -65 (épisodes 0-100) à ~+50 (épisodes 175-190) — convergence finale vers reward positif. Haut-droite — loss Huber (axe Y = 0.00 à 0.06), courbe brute + moyenne mobile MA-50 rouge en cloche centrée sur l'épisode 175 (explosion temporaire de la loss = transition de phase exploration → exploitation). Bas-gauche — Sharpe Ratio sur 10 évaluations (axe Y = -7 à +1), chute à -6.8 vers l'évaluation 3, remonte progressivement vers 0.05 à l'évaluation 9 ; ligne horizontale pointillée verte Target 0.7 en haut. Bas-droite — résumé textuel « Resume Meilleur Modele » : Meilleur Épisode = 40, Val Sharpe = 0.683, Val Return = +50.1 %, Epsilon final = 0.050, Buffer size = 100 000, Total steps = 1 113 615. Démontre l'apprentissage par renforcement profond appliqué au trading : convergence tardive (épisode 175+), drawdown intermédiaire sévère (Sharpe -6.8), compromis exploration/exploitation (epsilon final 0.05)."></a></p>

## Installation — pratique, tous niveaux

Ouvrir les carnets depuis un clone du dépôt : plusieurs lisent des modules voisins et les carnets de recherche écrivent leurs journaux hors dépôt. La procédure générale figure dans le [README QuantConnect](../README.md) ; les chemins de kernels par machine dans [kernels-runtime.md](../../../docs/reference/kernels-runtime.md).

- **Python** : noyau Python 3 avec `pandas`, `numpy`, `scipy`, `matplotlib`, `scikit-learn`. Les carnets de série temporelle (22-24, 30-31) et de renforcement (32-35) ajoutent `torch` et `stable-baselines3` ; les carnets 30 à 32 écrivent des checkpoints et demandent un GPU.
- **QuantConnect Cloud** : les carnets marqués `[QC CLOUD]` et la sous-série Cloud supposent un projet sur la plateforme ; le backtest n'est pas rejouable hors ligne.
- **Lean** : les variantes formelles et les vérifications associées utilisent les lakes de la série GameTheory et SymbolicAI ; voir leurs README respectifs.
- **Réseau** : les carnets 05b, 42, 43 et 45 lisent yfinance à l'exécution ; leurs sorties committées sont le résultat d'un vrai appel, et un environnement sans réseau ne les rejoue pas.
- **Modèles de langage** : 26, 44 et 46 appellent un service externe et demandent `OPENAI_API_KEY`, lue depuis `.secrets/master.env` hors dépôt. Le journal d'appels de 44 est écrit hors dépôt et permet le rejeu strict sans clé.

## Pour aller plus loin — recherche

### Le fil rouge : ce qui survit à un backtest aligné

Les carnets 12b, 15, 42 à 46 partagent une même doctrine, appliquée à des objets différents : une mesure ne vaut que par sa variance, son hors-échantillon et ses coûts. Un Sharpe se lit avec son erreur-type ; une stratégie se juge nette de frais ; une comparaison de modèles se tranche par une perte appariée et un test de Diebold-Mariano ; un générateur se juge sur les statistiques de ce qu'il engendre, pas sur sa perte ; un organ LLM se juge contre un étalon externe avec un témoin négatif.

Le corollaire est inconfortable et répété dans les carnets : plusieurs expériences de cette sous-série rendent `INCONCLUSIVE` ou `INCONCLUSIF`, et ces verdicts sont le résultat, pas un échec de la démonstration.

### Prolongements dans le dépôt

- **Stratégies déployables** : le dossier [`projects/`](../projects/README.md) porte les `main.py` backtestés ; le carnet pédagogique d'une étape y a souvent un projet correspondant.
- **Livre de référence** : *Hands-On AI Trading* (Jared Broad, 2025), dont les exemples sont rattachés aux carnets dans [BOOK_MAPPING.md](../BOOK_MAPPING.md).
- **Séries sœurs** : [Search](../../Search/README.md) pour les algorithmes évolutionnaires et métaheuristiques, [SymbolicAI](../../SymbolicAI/README.md) pour les organes formels et les graphes de connaissance, [GenAI](../../GenAI/README.md) pour les services de modèles.
- **Ordre de lecture du renforcement** : 25 (introduction) → 32 (DQN) → 33 (PPO) → 34 (SAC/A2C) → 35 (allocation).

### Utilitaires

| Carnet | Usage |
|---|---|
| [QC-Py-Dataset-Workflow](QC-Py-Dataset-Workflow.ipynb) | Télécharger, consolider et visualiser les jeux de données de marché par les scripts `scripts/datasets/` |

## Ressources — tous niveaux

- **Plateforme** : [documentation QuantConnect](https://www.quantconnect.com/docs) et [QuantConnect Lab](https://www.quantconnect.com/lab) pour exécuter les carnets `[QC CLOUD]`.
- **Livre** : [*Hands-On AI Trading*](https://www.hands-on-ai-trading.com/), Jared Broad.
- **Méthode de validation** : Lo (2002) sur l'erreur-type du Sharpe, Bailey et López de Prado (2012) sur le PSR — traités en 12b.
- **Sources des carnets de recherche** : TradingAgents (Xiao et al., arXiv:2412.20138) en 44 ; Steward (Feng et al., arXiv:2610.30557) en 45 ; FinanceBench en 46. Les copies archivées figurent au gisement partagé de bibliographie du dépôt, qui fait foi pour toute attribution.
- **Catalogue** : [COURSE_CATALOG.generated.md](../../../COURSE_CATALOG.generated.md) pour l'inventaire complet et les compteurs tenus par l'automatisation.

> **Rappel honnête** : le trading algorithmique est un domaine où l'overfitting est la règle. La discipline du walk-forward, du multi-graine et de l'out-of-sample strict — enseignée tout au long de cette sous-série — est ce qui sépare une stratégie robuste d'une illusion statistique.

---

**Navigation** : [README QuantConnect](../README.md) · [Livre de référence](https://www.hands-on-ai-trading.com/) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
