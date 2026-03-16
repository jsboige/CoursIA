<!-- Slide number: 1 -->
# Trading AlgorithmiqueI - Introduction
1
Jean-Sylvain Boige
jsboige@myia.org

Objectifs du Cours
Comprendre les fondamentaux du trading algorithmique.
Apprendre à utiliser Lean/QuantConnect.
Concevoir et implémenter un algorithme de trading.
Évaluer et optimiser une stratégie algorithmique.
Maîtriser le traitement de données et l’IA pour le trading.
IA 101

### Notes:

<!-- Slide number: 2 -->
# Plan du Cours
2
Introduction au trading
Marchés financiers et instruments
Analyse technique et fondamentale
Types d’ordre
Introduction au trading algorithmique
Backtesting et simulation
Gestion du risque
Types de stratégies
Initiation pratique à QuantConnect et Lean
Introduction à l’IA pour le trading
Préparation et transformation des données
Choix et mise en œuvre de modèles de machine learning

<!-- Slide number: 3 -->
# Qu’est-ce que le Trading Algorithmique ?
3
Définition:
Achat et vente d’actifs financiers pilotés par des algorithmes
Utilise des méthodes d’analyse technique, mais aussi des données fondamentales et extra-financières:
Revenus, indicateurs macroéconomiques, flux d’actualités, sentiment du marché etc.
Universalité:
Tout ce qui est numérisable peut être utilisé en trading quantitatif

<!-- Slide number: 4 -->
# Profil du Trader Algorithmique
4
Diplôme:
Pas nécessairement un diplôme avancé
Compétences:
Mathématiques, statistiques et code, compréhension des marchés financiers, curiosité et capacité d’apprentissage continu
Origines:
Milieux variés comme les sciences physiques, ingénierie, informatique etc.
Expérience:
Finance et programmation cruciales, avoir des économies pour les périodes sans gains

<!-- Slide number: 5 -->
# Avantages du Trading Algorithmique
5
Scalabilité:
Facilité à augmenter les volumes de trading
Temps:
Moins consacré aux opérations, plus à la recherche
Pas de Nécessité de Marketing:
Pas besoin de chercher activement des clients ou investisseurs
Élimination des biais émotionnels
dans la prise de décision
Diversification facilitée
Possibilité de gérer plusieurs stratégies de front

<!-- Slide number: 6 -->
# Types de Trading Algorithmique
6
HFT (High-Frequency Trading):
Opérations en millisecondes ou microsecondes.
Objectif: Exploiter de petites inefficacités du marché.
Technologie: Nécessite une infrastructure technologique de pointe.
MFT (Medium-Frequency Trading):
Opérations sur des secondes, minutes à quelques heures.
Objectif: Arbitrage, suivi de tendance, et autres stratégies.
Flexibilité: Moins exigeant technologiquement mais nécessite une analyse de données robuste.
LFT (Low-Frequency Trading):
Opérations sur des jours, semaines ou mois.
Objectif: Investissement basé sur des facteurs fondamentaux ou des indicateurs techniques.
Gestion du Risque: Focalisation sur la réduction du risque à long terme.
Chaque type…
A ses avantages et inconvénients,
Nécessite des compétences, des infrastructures et des ressources différentes,
Offre des opportunités de rendement variables.

<!-- Slide number: 7 -->
# Vue d’ensemble du Marché
7
Marchés Principaux:
Actions, Forex, Futures, Cryptomonnaies
Rôles des Participants :
Traders particuliers, institutionnels, market makers, arbitragistes
Rôles des Participants:
Fournisseurs de liquidité, preneurs de liquidité
Réglementations:
MiFID II en Europe, Dodd-Frank aux États-Unis
Importance des Données:
Tickers, Order Book, Volume, Time & Sales
Impact de la qualité et de la fréquence (temps réel vs résolution)

<!-- Slide number: 8 -->
# Instruments financiers
8
Actions:
Titres qui représentent une fraction de la propriété d’une entreprise.
Forex:
Échange de devises étrangères, souvent à des fins de spéculation ou de couverture.
Futures:
Contrats qui obligent à acheter ou vendre un actif à un prix fixé à une date future.
Cryptomonnaies:
Monnaies numériques qui utilisent la cryptographie pour sécuriser les transactions. Aspects réglementaires variables
Classes d’actifs:
Catégories d’investissement comme les actions, les obligations, les matières premières, etc., pour diversifier le risque.

<!-- Slide number: 9 -->
# Analyse Technique et Fondamentale
9

<!-- Slide number: 10 -->
# Infrastructure de Trading
10
Plateformes et Courtiers:
Interactive Brokers, MetaTrader, Robinhood
API de Trading: Interface de programmation permettant l’automatisation des ordres de trading.
FIX, REST APIs, WebSocket
Flux de Données:
Fournit des informations en temps réel ou différé sur les marchés.
Certaines plateformes offrent des flux combinés
Latence et Coûts:
Délais d’exécution: Temps entre la soumission et l’exécution d’un ordre.
Coûts de transaction: Frais associés à l’achat et à la vente d’actifs.
Exigence d’Infrastructure: Matériel et logiciel nécessaire pour le trading algorithmique
Serveurs co-localisés, GPUs pour ML

<!-- Slide number: 11 -->
# Les Ordres de Trading - Types d’Ordres
11
Les ordres sont cruciaux pour toute stratégie de trading. Ils varient en fonction de la rapidité d’exécution, du prix et des conditions.
Ordres au marché:
Exécution: Immédiate au meilleur prix.
Risque: Prix d’exécution incertain.
Impact: Peut affecter significativement le marché.
Ordres à cours limité:
Contrôle: Prix limite pour l’achat/vente.
Flexibilité: Utilisation agressive ou passive.
Risque: Exécution incertaine.
Ordres conditionnels et hybrides:
Complexité: Inclut des ordres cachés, routés.
Utilité: Pour des stratégies plus avancées.
Ordres stop :
Déclenchent un ordre au marché ou limite une fois qu’un prix prédéfini est atteint.
Le choix entre ces types d’ordres dépend du besoin d’immediateté et du contrôle du prix.
Ordres au marché sont rapides mais incertains en prix, tandis que les ordres à cours limité offrent plus de contrôle mais moins de certitude.
Impact du mode d’exécution (bourse centrale vs. Dark pools)

<!-- Slide number: 12 -->
# Ordres - Instructions Optionnelles
12
Les instructions optionnelles offrent plus de contrôle sur vos ordres.
Instructions de Durée: “Good ’til”
GTD: Actif jusqu’à une date donnée.
GTC: Actif jusqu’à annulation.
GAT: Actif à un moment donné.
Instructions d’Enchères:
On-open: Pour enchère d’ouverture.
On-close: Pour enchère de clôture.
Next-auction: Pour prochaine enchère valide.
Instructions de Remplissage:
IOC: Exécution ou annulation immédiate.
FOK: Fill-or-Kill: Exécution totale immédiate ou annulation.
AON: All-or-None: Exécution totale requise.
Minimum-Volume: Volume minimum requis.
Comprendre ces instructions améliore l’efficacité de trading. Elles permettent d’adapter vos ordres à différentes situations de marché.

<!-- Slide number: 13 -->
# Ordres - Instructions Spécifiques (1)
13
Ordres Must-Be-Filled (MBF)
Exécution Totale: Doivent être exécutés en totalité.
Interruption de volatilité: Déclenche une interruption si non exécuté.
Session de Trading Séparée: Session spéciale pour ces ordres.
Préférencement et Instructions Dirigées
Trading Bilatéral: Direction vers un courtier spécifique.
On parle d’internalisation
Controverse: Contournent les règles de priorité.
Amélioration de Prix: Mécanismes spéciaux pour améliorer le prix.
Instructions de Routage
Do-Not-Route: Exécution locale uniquement.
Directed-Routing: Routage vers un marché spécifique.

<!-- Slide number: 14 -->
# Ordres - Instructions Spécifiques (2)
14
Inter-Market Sweeps
Balayage: Balaye le carnet d’ordres sur un marché donné.
Instructions de Liaison
One-Cancels-Other (OCO): Deux ordres sont mutuellement exclusifs.
One-Triggers-Other (OTO): Un ordre déclenche un autre ordre.
Instructions Diverses
Anonymat: Certains marchés offrent l’anonymat.
Ventes à Découvert: Drapeau requis sur certains marchés.
Lots Impairs: Appariement de lots ronds avec lots impairs.

<!-- Slide number: 15 -->
# Types d’Ordres basés sur des Conditions
15
Ordres à seuil de déclenchement suiveur (Trailing Stop)
Verrouillage des prix: S’adapte au marché.
Flexibilité: Maximise les gains sans prédire le stop.
Ex: Stop de vente à -5% dont le seuil remonte avec le cours.
Ordres conditionnels / Si touché
Logique d’activation: Caché jusqu’à un niveau de prix.
Polyvalence: Basés sur le prix d’autres actifs.
Ordres sensibles au tick
Dépendance au tick: Exécuté si le dernier prix répond à des conditions.
Impact sur le marché: Minimisé pour un meilleur prix.

<!-- Slide number: 16 -->
# Types d’Ordres - Gestion de la Visibilité
16
Types d’ordres cachés
Ordres Iceberg:
Partie visible et cachée.
Fréquents sur les marchés à forte liquidité (actions, futures)
Priorité:
Plus basse que les ordres visibles.
Types d’ordres discrétionnaires
Ordres non tenus:
Trader décide de l’exécution.
Évolution:
Plus basées sur des règles.
Ordres ajustés (Pegged)
Prix dynamique:
Suivre la meilleure offre ou demande.

<!-- Slide number: 17 -->
# Types d’Ordres - Stratégies de Routage
17
Ordres acheminés (Routed)
Stratégies complexes: Routage vers différents lieux.
Smart Order Routing: Stratégies complexes.
Ex: Interactive Brokers SmartRounting
Permet d’éviter le slippage ou optimise l’exécution
Ordres Pass-Through
Deux ordres séquentiels: IOC initial puis un autre ordre.
Liquéfaction: Consomme la liquidité d’abord, puis route le reste.
Ordres de stratégie de routage
Instructions complexes: Exemples de NASDAQ (MOPP, DOTI, etc.).

<!-- Slide number: 18 -->
# Autres Types d’Ordres - Spécialisés
18
Ordres de croisement
Types variés: Committed, Uncommitted, etc.
Mécanismes variés: Différents réseaux de croisement.
Ordres non engagés
Similaires aux IOIs: Besoin de confirmation.
Protection: Tailles minimales, etc.
Ordres négociés
Mécanisme bilatéral: Environnement de négociation.
Anonymat: Entre investisseurs ou fournisseurs de liquidité.
Alertes Automatisées
Notification aux PLPs: Exemple de Millennium ATS.
Order-Contingent Order Types
Ordres Liés-Alternatifs: Liste d’ordres alternatifs.
Ordres Contingents: Ajustent prix et taille.
Implied Orders
Ordres Implicites: Ajustent prix et taille.
Importance: Liquidité supplémentaire en marché à terme.

<!-- Slide number: 19 -->
# Trouver une stratégie qui vous convient
19
Sources d’Idées:
Articles académiques, blogs, forums, médias.
Suivi des meilleures stratégies sur plateformes.
Modification de Stratégies: Ajustements pour rentabilité.
Échange d’idées: Blogs de trading pour partage.
Stratégies qui vous conviennent:
Temps disponible: Temps complet vs temps partiel.
Académiques vs. Publiques: Complexité vs simplicité.
Compétences en programmation: Élargit les options.
Votre Capital de Trading:
Ancien minimum conseillé de 50 000 $.
Nouveaux minima grâce aux cryptos et frais réduits.
Votre Objectif:
Revenu régulier vs gains en capital.

<!-- Slide number: 20 -->
# Comment évaluer une stratégie ?
20

<!-- Slide number: 21 -->
# Stratégies Plausibles et leurs Pièges
21
Drawdowns:
Perte de valeur, profondeur et durée à évaluer.
Slippage:
Écart de prix entre ordre et exécution.
Coûts de Transaction:
Impact sur les stratégies à haute fréquence.
Évolution du Marché:
Efficacité moindre qu’il y a 10 ans
les marchés sont plus efficients
Changements de Régime:
Données historiques parfois non pertinentes.
Overfitting:
Surajustement aux données historiques.
Frais de financements
Pour les positions à marge

<!-- Slide number: 22 -->
# Intelligence Artificielle et Sélection de Stocks
22
Scepticisme initial sur l’IA:
Tendance à surajuster les données.
Pratiques qui fonctionnent en IA:
Modèles simples, fondements économétriques. Mixture d’experts
Stratégies “Sous le Radar”:
Faible capacité
moins d’arbitrage par grands fonds.
Avancées récentes
« Guerre » des modèles
Théorie des jeux

<!-- Slide number: 23 -->
# Backtesting
23
Qu’est-ce que c’est ?:
Évaluation d’une stratégie d’investissement sur des données historiques.
Pourquoi c’est important:
Valider l’efficacité de la recherche originale et expérimenter avec des variations pour l’optimiser.
Sources de Données:
Recherche web pour des bases gratuites ou peu coûteuses.
Yahoo Finance, Alpha Vantage, Interactive Brokers, Binance
Pièges et Problèmes:
Données ajustées pour les splits et les dividendes: Risque de faux signaux.
Biais de survie: Surévaluation potentielle des performances.
Dans le cas ou le Machine Learning est utilisé
Le backtesting doit prendre en compte les biais de sélection de données:
Séparer convenablement les ensembles (training, validation, test) pour évaluer la généralisation.

<!-- Slide number: 24 -->
# Plateformes de Backtesting
24
Excel:
Toutes les données sont visibles, ce qui réduit le risque de “look-ahead bias”. Utilisé à la fois pour le backtesting et le trading en direct.
Inconvénients: Limité aux modèles simples d’investissement.
MATLAB:
Utilisé en institutionnel, excellent pour tester des stratégies sur de grands portefeuilles. Modules statistiques avancés.
Inconvénients: Coûteux et moins efficace pour exécuter les trades.
TradeStation et autres plateformes:
Exécution des trades possible directement depuis la plateforme. Données historiques intégrées.
Inconvénients: Langage propriétaire, vous attache à TradeStation comme courtier.
Évolution des Plateformes
Python & R: Ont pris le relais de MATLAB dans la plupart des cas.
Exemple: Zipline et autres frameworks open-source
C#: Alternative montante grâce aux efforts de Microsoft et Lean.
Lean / QuantConnect :
Solution open-core en Python et C#,
3 environnements (Lean, Lean-cli-QC)
Permettent backtesting, paper trading et live trading. Utilisée dans ce cours.
Lean gère nativement les ajustements le données (splits, dividendes) et fournit un frand catalogue de données alternatives et simplifie l’évaluation point-in-time

<!-- Slide number: 25 -->
# Mesures de Performance et Pièges
25
Mesures Standard:
Ratio de Sharpe:
Mesure le rendement ajusté au risque, souvent annualisé
High Watermark:
Rendement cumulé maximal à un moment donné.
Drawdown Maximum et Durée:
La plus grande baisse et le temps pour récupérer.
Ex: -50% sur 1 an
Pièges courants:
Look-ahead bias:
Utilisation de données futures dans le calcul
Data-Snooping Bias:
Overfitting basé sur les données historiques.
Coûts de Transaction:
Omission des coûts associés aux transactions.
Avec Machine Learning: Dérive des données (data drift)
La distribution des données évolue dans le temps, rendant les patterns historiques obsolètes

<!-- Slide number: 26 -->
# Précautions face aux pièges
26
Look-ahead:
Utilisation de données décalées, forward-testing (paper trading)
Data-Snooping Bias:
peu de paramètres, augmentation, division et adaptation des données de backtest
Modèles de trading sans paramètres:
pas de surajustement, fiabilité mais complexité computationnelle
Paper Trading:
Test sur des données réelles non vues, le plus fiable.
Analyse de sensibilité:
Variation des paramètres pour évaluer la stabilité de la performance.
Simplification du modèle: Élimination des conditions superflues.
Répartition du capital de trading
entre différentes stratégies pour diminuer la variance.
Coûts de Transaction
à intégrer dans le Backtest pour des résultats plus réalistes.
Dérive des données (data drift) et non stationnarité
Il est crucial de revalider régulièrement les modèles ou d’appliquer des techniques comme la différenciation fractionnaire

<!-- Slide number: 27 -->
# Affinement de la Stratégie
27
Le Problème: Rendements diminuent quand une stratégie est populaire.
Solutions:
Variations Mineures: Petites variations peuvent améliorer les rendements.
Exclusion de Stocks: Éviter certains types d’actions.
Changement de Timing: Ajuster les points d’entrée et de sortie.

<!-- Slide number: 28 -->
# Gestion du Risque
28
La gestion du risque permet de « préserver » le capital initial tout en optimisant la croissance sur le long terme.
Maximisation de la Croissance: Objectif de maximiser la croissance du capital à long terme.
Rendement Moyen: ( m )
Variance des Rendements: ( s^2 )
Éviter la Ruine: Éviter une chute catastrophique du capital à zéro.
Drawdown: Chute maximale du capital sur une période donnée.

<!-- Slide number: 29 -->
# Outils et Formules
29

<!-- Slide number: 30 -->
# Dérivation de la Formule de Kelly
30

<!-- Slide number: 31 -->
# Gestion du Risque
31
Gestion avec la Formule de Kelly
Réduction de la Taille du Portefeuille: Si les pertes augmentent, réduisez ( f ).
Contagion Financière: Le risque de propagation des pertes entre les fonds.
Événements Extrêmes (Black swans)
Limites de la Formule: Ne prend pas en compte les “fat tails”.
Gestion des Événements Imprévus: Utilisation de modèles de Value-at-Risk (VaR).
Utilisation de Stop Loss
Momentum vs Mean-Reverting: L’efficacité varie en fonction du régime du marché.
Fondamental vs Liquidité: Quand appliquer les stop loss.

<!-- Slide number: 32 -->
# Autres Types de Risques
32
Risque de Modèle:
Biais de survie, biais de lookahead, et erreurs de données.
Changements structurels du marché comme l’impact des nouvelles réglementations.
Risque Logiciel:
Bugs, latence et décalages de données.
Assurez-vous que le système de trading automatisé est bien testé et surveillé.
Risques Physiques:
Pannes de courant, défaillance du matériel, cyberattaques.
Solution de secours et plan de récupération en cas de catastrophe.

<!-- Slide number: 33 -->
# Préparation Psychologique
33
Émotions en Trading:
Overtrading en période de gains et aversion au risque en période de pertes.
Importance de suivre scrupuleusement le modèle.
Biais Comportementaux:
Effet de dotation, biais du statu quo, aversion à la perte, biais de représentativité.
Comment ces biais affectent la prise de décision en trading.
Désespoir et Avidité:
Importance de la gestion du stress et de la psychologie.
Mettre en place des garde-fous pour éviter la prise de décisions impulsives.
Conseils Pratiques:
Commencez petit pour tester votre discipline.
Avoir un tampon financier ou des sources de revenus alternatives pour réduire la pression financière et psychologique.
Nécessité parfois d’un support psychologique ou d’un coaching (cf. Athlètes)

<!-- Slide number: 34 -->
# Stratégies de Moyenne Réversion
34
Moyenne Réversion: Les prix des actions ont tendance à revenir vers une moyenne à long terme.
Recherche Académique: Proximité à une marche aléatoire, mais certaines conditions permettent la moyenne réversion.
Pièges en Backtesting:
Biais de Survie: Ignorer les actifs disparus peut fausser les résultats.
Erreurs de Base de Données: Incohérences dans les données financières.
Effets de la Concurrence:
Réduit les opportunités d’arbitrage, diminuant les rendements.

<!-- Slide number: 35 -->
# Stratégies fondamentales de Momentum
35
Momentum: Tendance d’un actif à continuer à se déplacer dans la même direction pendant une certaine période.
Diffusion Lente de l’Information: Crée des opportunités de momentum.
Comportement de Troupeau: Les investisseurs suivent les autres, amplifiant les tendances.
Horizons Temporels Imprévisibles: Imprédictibilité de la durée du momentum.
Effets de la Concurrence:
Accélère l’atteinte de l’équilibre des prix, rendant les stratégies de momentum moins efficaces à long terme.

<!-- Slide number: 36 -->
# Stratégies de Regime Switching
36
Concept & Types: Les Marchés varient entre différents régimes
(haussiers/baissiers, inflation/récession, volatilité).
La Prédiction de ces régimes est un défi.
Outils & Approches:
GARCH: modèle “autorégressif conditionnellement hétéroscédastique généralisé”:
utile pour mesurer la volatilité, moins pour le prix d’actions.
Modèles probabilistes: Modèles de Markov, de Kalman etc. Nécessite un modèle de variables hypothétiques ou variables latentes.
Très puissant mais complexe.
Data Mining: Utilise indicateurs techniques, données macro, “buzz” médiatique.
Application Pratique:
Machine Learning pour détection en temps réel, mais attention aux pièges
Comme le biais de “data snooping” et l’optimisation excessive.

<!-- Slide number: 37 -->
# Pondérations par le Volume et le Temps
37
VWAP - Volume Weighted Average Price
Objectif: Obtenir un prix moyen pondéré par le volume.
Utilisation: Fréquemment utilisé en trading institutionnel pour minimiser l’impact du marché.
Mécanisme: Calcule le rapport coût/volume à des intervalles réguliers et exécute des ordres en fonction.
TWAP - Time Weighted Average Price
Objectif: Obtenir un prix moyen pondéré par le temps.
Utilisation: Utilisé lorsque l’impact du volume sur le prix est moins pertinent.
Mécanisme: Divise un gros ordre en plus petits morceaux, exécutés à intervalles réguliers.
TWAP/VWAP sont très utilisés par les institutionnels
pour éviter un prix moyen trop déformé.

<!-- Slide number: 38 -->
# Stratégies Basées sur les Données
38
Modèles Factoriels
Exposition Factorielle:
Mesure la sensibilité d’un actif à différents facteurs du marché, comme les taux d’intérêt ou la volatilité du marché.
Rendement Factoriel & Spécifique:
Le rendement factoriel est celui qui peut être attribué à l’exposition à certains facteurs, tandis que le rendement spécifique est le rendement qui n’est pas expliqué par ces facteurs.
Utilisation:
Ces modèles sont couramment utilisés pour la construction de portefeuilles et pour comprendre les sources de rendement.
Sentiment Analysis
Objectif:
Exploiter les données textuelles pour prédire les mouvements du marché.
Technologie:
Utilise des techniques de NLP (Natural Language Processing) pour analyser des textes tels que les nouvelles, les tweets, etc.
Mécanisme:
Le sentiment du marché est extrait des données textuelles et utilisé pour générer des signaux de trading.
Utilisation Pratique:
Les hedge funds et les traders algorithmiques utilisent l’analyse du sentiment pour améliorer leurs stratégies.
Importance de la mise en place d’un pipeline de données
Collecte, nettoyage, feature engineering etc.

<!-- Slide number: 39 -->
# Métriques des modèles factoriels
39

<!-- Slide number: 40 -->
# Stratégies Basées sur les Données 2.0
40
Méthodes Modernes
Multi-Factoriels: Évolution des modèles 3F de Fama-French vers des modèles multi-factoriels.
Machine Learning en Trading
Machine Learning Paramétrique: Utilisation de réseaux neuronaux et de modèles séquentiels en deep learning comme LSTM.
Machine Learning Non-Paramétrique: Emploi de forêts aléatoires, k-NN, SVM pour capturer des relations non-linéaires.
Succès des techniques d’ensemble, Mixture of experts.
Avancées en ML et RL
Modèles Séquentiels: Utilisation de LSTM, de GRU, de Transformers en deep learning, ou encore de réseaux bayésiens dynamiques pour capturer des dépendances temporelles.
Reinforcement Learning (RL): Application à l’optimisation de stratégie en temps réel. Prise de décision avec ou sans modèle prédictif associé.
Analyse & Risques Modernes
Métriques Modernes: Transition du R² vers des mesures comme l’Information Ratio.
Optimisation Bayésienne: Utilisé pour la sélection de modèle et l’ajustement de paramètres.
Mise à Jour Continue: Adaptation aux changements de comportement du marché via techniques d’apprentissage en ligne.
Workflows sémantique
Avènement des LLMs (ChatGPT, Llama etc.)
Théorie des jeux
Stratégies adversériales, poursuite et prédation
Signalement (baleines etc.)
Flash crashs…

<!-- Slide number: 41 -->
# Stratégies de Sortie en Trading
41
Période de Détention Fixe: Utilisée par défaut dans divers modèles de trading.
Momentum: La période optimale peut être trouvée via un backtest, mais attention à l’évolution rapide de l’information.
Réversion à la Moyenne: Une méthode plus robuste pour déterminer la période optimale est disponible.
Prix ou Profit Cible: Utilisé pour définir un objectif de sortie.
Réversion à la Moyenne: Le prix moyen historique peut servir de prix cible.
Momentum: Moins fiable car basé sur une évaluation fondamentale incertaine.
Derniers Signaux d’Entrée: Utiliser le signal d’entrée le plus récent comme signal de sortie.
Momentum: Si le signal change, c’est presque comme un stop-loss.
Réversion à la Moyenne: Le signal reste généralement le même, donc pas de stop-loss recommandé.
Prix Stop: Rarement utilisé de manière efficace.
Momentum: Peut être justifié si le sens du momentum change.
Réversion à la Moyenne: Souvent contre-productif, sauf en cas de changement de régime dû à des nouvelles.

<!-- Slide number: 42 -->
# Stratégies de Sortie 2.0
42
Catégories Classiques:
Période de Détention Fixe: Adaptation via ML pour prédiction de la période optimale.
Prix ou Profit Cible: Intégration de données en temps réel pour ajuster les cibles.
Derniers Signaux d’Entrée & Prix Stop: Utilisation rare, mais avec opportunités pour optimisation par RL.
Avancées en ML et Analyse Temps Réel:
Deep Learning: Utilisation de CNN ou LSTM pour détection de patterns et ajustement de la stratégie de sortie.
Reinforcement Learning (RL): Apprentissage pour optimiser la sortie en fonction du rendement et du risque.
Gestion de Risques Avancée:
Options & Derivés: Utilisation pour couvrir les positions et ajuster les stratégies de sortie.
Analyse Sentimentale: Utilisation de NLP pour ajuster les stratégies en fonction du sentiment du marché.
Alertes et Ajustements en Temps Réel:
Web Scraping & API: Collecte en temps réel de données de marché pour ajuster les stratégies.
Optimisation Continue: Mise à jour en temps réel des paramètres via techniques d’apprentissage en ligne.

<!-- Slide number: 43 -->
# Arbitrage et Paires
43
Pairs Trading
Objectif: Capitaliser sur la relation entre deux actifs similaires.
Utilisation: Nécessite une analyse de co-intégration.
Mécanisme: Achète un actif et vend un actif similaire en anticipation d’une convergence des prix.
Statistical Arbitrage
Objectif: Exploiter les écarts de prix entre des actifs fortement corrélés.
Utilisation: Nécessite une modélisation statistique complexe.
Mécanisme: Utilise des modèles statistiques pour identifier les opportunités d’arbitrage.

<!-- Slide number: 44 -->
# Market Making et Optimal Trading
44
Market Making
Objectif: Acheter et vendre activement pour profiter de l’écart acheteur-vendeur.
Utilisation: Nécessite une très faible latence et de gros volumes.
Mécanisme: Fournit des liquidités en affichant constamment des offres d’achat et de vente.
Optimal Trading Strategies
Objectif: Minimiser les coûts de transaction et l’impact du marché.
Utilisation: Généralement utilisé par les fonds institutionnels et les traders à haute fréquence.
Mécanisme: Utilise des algorithmes pour optimiser le timing et le coût des ordres.

<!-- Slide number: 45 -->
# Stratégies de Trading à Haute Fréquence
45
Exploite de petites inefficacités sur le marché ou fournit une liquidité temporaire en échange d’une petite commission.
Ratio de Sharpe Élevé:
Loi des grands nombres stabilise le rendement.
Centaines de paris par jour minimisent les écarts de rendement.
Difficultés et Défis:
Coûts de transaction cruciaux pour les tests.
Exécution à haute vitesse pour maximiser profits/pertes.
Risque de liquidation rapide (slippage, anomalies de marché)

<!-- Slide number: 46 -->
# Stratégies de Trading à Haute Fréquence 2.0
46
Machine Learning et AI:
Utilisation de modèles de Deep Learning pour prédiction de micro-tendances.
Reinforcement Learning pour l’ajustement dynamique de stratégies.
Latence Ultra-Faible:
Utilisation de FPGA (Field-Programmable Gate Arrays) pour des ordres en microsecondes.
Co-location de serveurs près des bourses.
Risques et Réglementations:
Détection d’abus de marché par des algorithmes de surveillance.
Impact des régulations comme MiFID II sur la transparence.

<!-- Slide number: 47 -->
# Stratégies de Trading Saisonnier
47
Effet de Janvier:
Petites capitalisations bénéficient en janvier. Vendre en décembre pour raisons fiscales.
Stratégies Mensuelles:
Acheter/vendre selon la performance du mois précédent. Efficace jusqu’à 2002.
Stratégies Matières Premières:
Essence et gaz naturel. Fiable car basé sur besoins économiques. (ex. pétrole en été)
Précautions:
Biais de Data-Snooping. Vérifier la fiabilité et le sens économique.

<!-- Slide number: 48 -->
# Stratégies de Trading Saisonnier 2.0
48
Concepts Traditionnels:
Effet de Janvier: Machine learning pour identifier les meilleures opportunités en temps réel.
Stratégies Mensuelles: Utilisation d’algorithmes adaptatifs pour revalider l’efficacité.
Stratégies Matières Premières: Optimisation par RL pour des meilleures entrées et sorties.
Innovations en ML & Data Analytics:
Time Series Forecasting: LSTM et ARIMA pour prédire la saisonnalité.
Reinforcement Learning (RL): Maximisation des rendements en adaptant les stratégies saisonnières.
Random Forest & SVM: Classification pour détecter les meilleures périodes d’achat/vente.
Intelligence Contextuelle:
IoT & Big Data: Utilisation de données météorologiques et de flux logistiques pour optimiser les trades en matières premières.
Sentiment Analysis: Évaluer l’effet du sentiment saisonnier sur les marchés.
Gestion de Risques Avancée:
Simulation de Monte Carlo: Estimation des intervalles de confiance pour les stratégies.
Backtesting Adaptatif: Tests dynamiques pour ajuster aux changements du marché.

<!-- Slide number: 49 -->
# Portefeuille à Haut Levier vs Haut Bêta
49
Bêta:
Mesure de la sensibilité d’un actif par rapport au marché.
Haut Bêta: Plus volatil, plus de rendements mais plus de risques.
Faible Bêta: Moins de risques, meilleur ratio de Sharpe.
Levier:
Utilisation d’emprunts pour augmenter l’exposition aux actifs.
Effet Amplificateur: Augmente les gains mais aussi les pertes.
Risques de Queue Épaisse: Pertes imprévues dues à une distribution de rendements atypique.
Ratio de Sharpe:
Mesure le rendement ajusté au risque.
Croissance Composée: Proportionnelle au carré du ratio de Sharpe.
Allocation d’Actifs:
Répartition du portefeuille entre différentes classes d’actifs.
Optimisation 23-77: Entre actions à faible bêta et obligations pour un risque minimal.
Un faible bêta avec un levier modéré:
offre théoriquement une meilleure croissance composée à long terme (cf. formule de Kelly), mais avec des risques inhérents.

<!-- Slide number: 50 -->
# Portefeuille à Haut Levier vsHaut Bêta 2.0
50
Bêta Adaptatif:
Utilisation de l’apprentissage machine pour ajuster dynamiquement le bêta.
Prédictions de Volatilité: Utilisation de séries temporelles pour anticiper les changements de volatilité.
Levier avec Machine Learning:
Algorithmes pour décider du moment optimal pour appliquer un levier.
Risques de Catastrophe: Utilisation d’alertes algorithmiques pour réduire le levier en cas de signaux de crash.
Optimisation de Ratio de Sharpe avec IA:
Utilisation de réseaux de neurones pour maximiser le ratio de Sharpe.
Apprentissage par Renforcement: Pour une allocation d’actifs dynamique et optimisée.
Gestion du Risque 2.0:
Techniques modernes comme le “Value-at-Risk” (VaR) basé sur le deep learning.
Indicateurs de Sentiment du Marché: Via le traitement du langage naturel pour anticiper les changements de marché.
La version 2.0 intègre des techniques d’apprentissage machine et d’analyse de données pour une gestion plus proactive et adaptative du risque et du rendement.

<!-- Slide number: 51 -->
# Questions?
51
IA 101

### Notes:

<!-- Slide number: 52 -->
# Initiation à Lean
52
Documentation officielle
IA 101

### Notes:

<!-- Slide number: 53 -->
# Lean/QuantConnect
53
Qu’est-ce que c’est?:
Plateforme de trading algorithmique
Langages de Programmation:
C#, Python
Fonctionnalités Principales:
Notebooks d’analyse, Backtesting, optimisation, paper et live trading
Data Library:
Données historiques de plusieurs marchés
Communauté & Ressources:
Forums, tutoriels, documentation

<!-- Slide number: 54 -->
# Installation de l’environnement
54
3 environnements
QuantConnect: Plateforme dans le Cloud
Lean-Cli + vscode: Plateforme hybride QC + containers locaux
Lean: Plateforme Open-source locale
QuantConnect
Créer un compte
Organisations, Nœuds de ressources
Lean-cli
Terminal
IDEs locaux
Vs Code
Extensions: c# dev kit, polyglot, python, git extension pack Python extension pack, QuantConnect
Visual Studio Community / for Mac
Charge de développement Desktop (Windows) / .Net (Mac)
DotPeek (désassembleur)
Jetbrains Rider
Licence ?
CS 405

<!-- Slide number: 55 -->
# Mise en route Lean-cli / VScode
55
Installation pip
Pip install –upgrade lean
Lean –version
Sur QuantConnect
My Account – Request Token Information
Lean init
Choix de l’«Organisation»
Synchronisation
lean cloud pull
lean cloud push
CS 405

<!-- Slide number: 56 -->
# Mise en route Lean
56
Fork /Clone git de Lean
Dans le répertoire de votre choix
Dépôt personnalisé: https://github.com/myintelligenceagency/Lean
Ouvrir la solution
QuantConnect.Lean.sln
Affichage des projets, projet de démarrage par défaut
Générer la solution
Restauration des packages, compilation des projets
Exécuter le Launcher
Démarrage en debug
Fichier de config « Lean/Launcher/bin/debug/config.json »
Algorithme par défaut: BasicTemplateFrameworkAlgorithm
Place un point d’arrêt dans la fonction Initialize et relancer.
Désassemblage: DotPeek / serveur de symboles
Développement et debuggage en Python
https://github.com/MyIntelligenceAgency/Lean/blob/master/ESGF/Python.md
CS 405

<!-- Slide number: 57 -->
# Environnement d’algorithme
57
QCAlgorithm
Ticker vs Bar.
Evènements =>  pas de lookahead
+ Interfaces + Classes de base
+ Strategic Development Framework
Objets fondamentaux
Time
Symboles
Portfolio
Securities
Brokers
Indicateurs (e.g. EMA)
History
Membres locaux
Manipulés par les méthodes
Parfois hérités + “Parameters”
Possibilité de les initializer

CS 405

<!-- Slide number: 58 -->
# Evènements
58
Initialize
Setxxx, Addxxx, ajout de handlers (InsightsGenerated etc.)
Gestion des dates + Consolidateurs
Cash / AddEquities/AddForex etc. (+ résolution) vs SetUniverseSelection
SetBrokerageModel, SetPortfolioConstruction, SetDataNormalisationMode
OnData
 Slice => Ticks, TradeBars
=> dictionaire par symbole
Price => close (data, data.Bars, Securities[xx])
Decision
=> Portfolio.Invested, nextEntryTime
Ordres
MarketOrder (symbol, calcul)
SetHoldings
Journalisation: Log
Sortie: condition/entryprice – Liquidate
OnOrderEvent
Filled, Submitted etc.
Autres points d’entrée
OnSecuritiesChange, OnEndOfDay, OnBrokerageMessage, OnWarmupFinished etc.
Evenements planifiés (Schedule)
CS 405

<!-- Slide number: 59 -->
# Initialisation
59
Définition des dates de backtesting:
C#
this.SetStartDate(2013, 1, 5);
this.SetEndDate(DateTime.Now.Date.AddDays(-7));
Python
self.SetStartDate(2018, 4, 1)
 self.SetEndDate(datetime.now() - timedelta(7))
 Définition des monnaies et montants initiaux
C#
this.SetAccountCurrency("EUR");
this.SetCash("EUR", 10000);;
Python
self.SetAccountCurrency("BTC")
self.SetCash("EUR", 10000)
Choix du Broker et souscription à des sécurités
C#
this.SetBrokerageModel(BrokerageName.Bitstamp, AccountType.Cash);
var btcSecurity = this.AddCrypto("BTCUSD", Resolution.Daily)
Python
self.SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Cash)
self.spy = self.AddEquity("SPY", Resolution.Hour, Market.Oanda)
Ajout d’indicateurs
C#
this.Fast = EMA(_btcusd, FastPeriod);this.Slow = EMA(_btcusd, SlowPeriod);
Python
self.fast = self.EMA(symbol, 30, Resolution.Minute)
self.slow = self.EMA(symbol, 60, Resolution.Minute)

CS 405

<!-- Slide number: 60 -->
# Initialisation (2)
60
Warmup
C# (Timespan)
this.SetWarmUp(TimeSpan.FromDays(150));
Python (nb barres)
self.SetWarmUp(200)
Possibilité de Warmup automatique
AutomaticIndicatorWarmUp = True
self.Settings.AutomaticIndicatorWarmUp = True
Evènements planifiés
C#
Schedule.On(DateRules.EveryDay(), TimeRules.Every(TimeSpan.FromDays(1)), this.ExampleFunc);
Python
self.Schedule.On(self.DateRules.EveryDay(),            self.TimeRules.Every(timedelta(minutes=10)),              self.ExampleFunc)
Consolidation de barres
C#
this._consolidator = Consolidate(_symbol, TimeSpan.FromMinutes(10), ConsolidationHandler);
Python
self.consolidator = self.Consolidate(self.symbol, timedelta(minutes=10), self.consolidation_handler)
Créations de graphiques
C#
var stockPlot = new Chart(_ChartName);var assetPrice = new Series(_PriceSeriesName, SeriesType.Line, "$", Color.Blue);stockPlot.AddSeries(assetPrice);This.AddChart(stockPlot);(…)
 this.Plot(_ChartName, _PriceSeriesName, Securities[_btcusd].Price);
Python
stockPlot = Chart("Trade Plot")stockPlot.AddSeries(Series("Price", SeriesType.Line, 0))self.AddChart(stockPlot)(…)
self.Plot("Trade Plot", "Price", self.lastPrice)
CS 405

<!-- Slide number: 61 -->
# Evènements de données
61
Temps découpé en « slices »
Peuvent contenir des Ticks (ponctuel) ou TradeBars, QuoteBars (périodes)
Méthode principale
C#
public override void OnData(Slice slice){    var data = slice[_symbol];}
Python
def OnData(self, slice: Slice) -> None:    data = slice[self.symbol]
Alternative: « CurrentSlice »
Dans un évènement planifié (cf initialisation)
Fin de journée Python
def OnEndOfDay(self, symbol: Symbol) -> None:
Fin de journée C#
public override void OnEndOfDay(Symbol symbol)
CS 405

<!-- Slide number: 62 -->
# Journalisation et graphiques
62
Journalisation:
Méthodes Log ou Debug
Exemple crypto:
Debug($"Time: {data.Time.ToShortDateString()}, Price:  @{data.Bars[_btcusd].Close}$/Btc; Portfolio: {Portfolio.CashBook[Portfolio.CashBook.AccountCurrency].Amount}$, {Portfolio[_btcusd].Quantity}BTCs, Total Value: {Portfolio.TotalPortfolioValue}$, Total Fees: {Portfolio.TotalFees}$");
Logs enregistrés dans backtest: Eviter de les surcharger pour éviter la saturation
Export de graphiques:
méthode Plot (cf initialisation)
Utilisation de données historiques
Python
self.df= self.History(self.Symbol("SPY"), start_time, end_time, Resolution.Hour)
Plusieurs symbols:
self.dataframe = self.History([self.Symbol("IBM"), self.Symbol("AAPL")], start_time, end_time)

CS 405

<!-- Slide number: 63 -->
# Gestion explicite des ordres
63
Types: Market, Limit, StopMarket, StopLimit, MarketOnOpenOrder, MarketOnCloseOrder etc.
C#:
 var orderTicket = this.StopMarketOrder("IBM", 10, price / 0.1m);
Python:
marketOrderTicket = self.LimitOrder("SPY", 100, 21.67)
Type de retour: OrderTicket
Permet de suivre l’ordre (Status, QuatityFilled etc.)
Possibilité de faire des MAJ chez certains Brokers
classe UpdateOrderFields, méthode ticket.Update
Méthode OnOrderEvent
C#:
public override void OnOrderEvent(OrderEvent orderEvent)
Python
def OnOrderEvent(self, orderEvent: OrderEvent) -> None:
Annulation:
 méthode ticket.Cancel(“message”) ou request = ticket.CancelOrderRequest()
CS 405

<!-- Slide number: 64 -->
# Gestion des ordres par dimensionnement
64
Dimensionnement de position: ponderer la valeur des actifs du portefeuille
C# (version simple)
this.SetHoldings("IBM", 0.5);
Python (tous les paramètres)
self.SetHoldings(symbol, weight, liquidate_existing_holdings, tag, order_properties)
Possibilité de définir plusieurs cibles d’actifs simultanément:
self.SetHoldings([PortfolioTarget("SPY", 0.8), PortfolioTarget("IBM", 0.2)], True)
Calcul des quantités tenant compte des frais
var quantity = CalculateOrderQuantity("IBM", 0.4);
Existence d’un Buffer (slippage)
2,5% par défaut
Personalisation
Settings.FreePortfolioValuePercentage = 0.05m; //pourcentage
self.Settings.FreePortfolioValue = 10000 # Valeur absolue
Liquidation
C# (un actif)
Liquidate("AAPL", "Liquidated");
Python (toutes les positions)
order_ids = self.Liquidate()
CS 405

<!-- Slide number: 65 -->
# Notebooks de recherche
65
Research Environnement
Environnement d’exploration facilitant l’itération
Jupyter / Python
.Net Interactive / c#
Workflow:
Hypothèse / Edge  Research  Strategy  Backtests/Optimisation  Paper/Live trading
Kernel dédié
Exécution QC en ligne
Exécution sous container Docker / lean-cli
QuantBooks
Classe héritant de QCAlgorithm
Utilisation de données historisées / dataframes pour analyse
CS 405

<!-- Slide number: 66 -->
# Framework de haut niveau
66
Ensemble de modules de haut niveau
Universe Selection: Choix des instruments disponible
Alpha Creation: Construction de signaux (insights)
Portfolio construction: construction et maintenance du portefeuille (targets)
Risk management (minimization de risque)
Execution: (immediate ou optimisée)
Abstractions facilitant la gestion de portefeuille
Utilisable en combinaison avec des primitives de bas niveau
(Alpha, PortfolioConstruction, Risk, Execution) peuvent être utilisés individuellement ou combinés
Sélection d’univers
Un univers définit les actifs disponibles pour le portefeuille
Sélection manuelle
 AddUniverseSelection(new ManualUniverseSelectionModel(symbols));
Sélection paramétrique ou planifiée
Ex:  EmaCrossUniverseSelectionModel:
Sélectionne les actifs d’un ensemble en retournement haussier le plus fort
Combinaisons d’univers possible
Méthode OnSecurityChanged quand des actifs sont rajoutés ou enlevés
C#
 public override void OnSecuritiesChanged(SecurityChanges changes)
Python
 def OnSecuritiesChanged(self, algorithm: QCAlgorithm, changes: SecurityChanges) -> None:

CS 405

<!-- Slide number: 67 -->
# Alphas
67

Alphas
 Classes chargées de générer des signaux
= Insights (direction, amplitude et confiance)
e.g. A partir d’indicateurs
Ajout à l’initialisation
self.AddAlpha(RsiAlphaModel())
Alphas par défaut
ConstantAlphaModel, HistoricalReturnsAlphaModel, EmaCrossAlphaModel, MacdAlphaModel, RsiAlphaModel, BasePairsTradingAlphaModel, PearsonCorrelationPairsTradingAlphaModel etc.
Alpha personnalisé
Python: classe + initialisation + création d’insights
class MyAlphaModel(AlphaModel):def OnSecuritiesChanged(self, algorithm: QCAlgorithm, changes: SecurityChanges) -> None:def Update(self, algorithm: QCAlgorithm, data: Slice) -> List[Insight]:
C#
class MyAlphaModel : AlphaModelpublic override IEnumerable<Insight> Update(QCAlgorithm algorithm, Slice data)public override void OnSecuritiesChanged(QCAlgorithm algorithm, SecurityChanges changes)
CS 405

<!-- Slide number: 68 -->
# Insights
68
Définit les signaux retournés par la méthode Update des Alphas
Python
 insight = Insight.Price("IBM", timedelta(minutes = 20), InsightDirection.Up)
C#
var insight = Insight.Price("IBM", TimeSpan.FromMinutes(20), InsightDirection.Up);
Caractéristiques
Paramètres importants:
Direction, Period, Magnitude, Confidence, Weight
Possibilité de les regrouper
return Insight.Group([insight1, insight2,insight3])
Possibilité de les annuler
self.insight.Cancel(algorithm.UtcTime)
Si pas de référence utilisation de l’insight manager (filtrage par symbole, par direction etc.)
var insights = algorithm.Insights.GetInsights(insight => insight.Direction == InsightDirection.Up);
algorithm.Insights.Cancel(symbols)

CS 405

<!-- Slide number: 69 -->
# Construction de portefeuille
69
Modèle de construction de portefeuille
Créée des « targets » qui se traduisent par des ordres
Python
self.SetPortfolioConstruction(EqualWeightingPortfolioConstructionModel())
C#
SetPortfolioConstruction(new EqualWeightingPortfolioConstructionModel());
Modèles fournis par défaut
EqualWeightingPortfolioConstructionModel
Poids égal entre les actifs avec Insights
ConfidenceWeightedPortfolioConstructionModel
Pondération par la confiance de l’insight
 InsightWeightingPortfolioConstructionModel
Pondération par poids de l’insight
 SectorWeightingPortfolioConstructionModel
Pondération par secteur industriel
AccumulativeInsightPortfolioConstructionModel
Compte les insights par symbole et direction
MeanVarianceOptimizationPortfolioConstructionModel
Minimise la volatilité
 BlackLittermanOptimizationPortfolioConstructionModel
Utilise un optimiseur
MeanReversionPortfolioConstructionModel
Retour à la moyenne
RiskParityPortfolioConstructionModel
Minimisation du risque
Optimiseurs fournis
MaximumSharpeRatioPortfolioOptimizer
MinimumVariancePortfolioOptimizer
UnconstrainedMeanVariancePortfolioOptimizer
RiskParityPortfolioOptimizer
CS 405

<!-- Slide number: 70 -->
# Gestion du risque
70
Objectif: gestion du risque des cibles
Renvoyées par le gestionnaire de portefeuille
Idéalement, doit être intégré dès la conception, pas après optimisation
Sinon, souvent performances dégradées
Définition
C#
this.AddRiskManagement(new MaximumDrawdownPercentPerSecurity());
Python
self.AddRiskManagement(MaximumSectorExposureRiskManagementModel())
Modèles fournis par défaut:
MaximumDrawdownPercentPerSecurity
MaximumDrawdownPercentPortfolio
MaximumUnrealizedProfitPercentPerSecurity
MaximumSectorExposureRiskManagementModel
TrailingStopRiskManagementModel
CS 405

<!-- Slide number: 71 -->
# Modèles d’exécution
71
Détermine comment les ordres sont exécutés
Définition
C#
this.SetExecution(new ImmediateExecutionModel());
Python
 self.SetExecution(ImmediateExecutionModel())
Modèles fournis
ImmediateExecutionModel
 SpreadExecutionModel
Nécessite des QuoteBars
StandardDeviationExecutionModel
 VolumeWeightedAveragePriceExecutionModel
CS 405

<!-- Slide number: 72 -->
# Optimisation de paramètres (1)
72
Définition de paramètres d’algorithmes
Appel explicite
fast_period = self.GetParameter("ema-fast", 100)self.fast = self.EMA("SPY", fast_period)
var parameterValue = GetParameter("parameterName", defaultValue);
Exemple Python: ParameterizedAlgorithm.py
Utilisation d’attributs
[Parameter("ema-fast")]public int FastPeriod = 18;
Configuration dynamique
Fichier config.json
Interface en ligne dédié / UI similaire dans l’extension vscode
Lanceur d’Optimisation
Exécute une série de backtests
Dans l’objectif de trouver la meilleure combinaison des paramètres pour optimiser une mesure (e.g. ratio de Sharpe)
Environnement
QuanConnect : bouton et Formulaire de paramétrage
Utilisation de crédits dans le cloud
Lean-cli : Commande dédiée
Lean : QuantConnect.Optimizer.Launcher
Bon usage
Attention à la combinatoire
Produit cartésien de toutes les possibilités voire + pour Euler
Utilisation d’une version d’algo « rapide »
test manuel de sensibilité à la résolution
Attention au sur-apprentissage
Optimisation sur une période donnée, validation finale sur une période + récente

CS 405

<!-- Slide number: 73 -->
# Optimisation de paramètres (2)
73
Configuration
Designation de l’algo C# ou Python identique
"algorithm-type-name", etc.
A priori pas de debug, au besoin utiliser la journalisation
Désignation des paramètres à optimiser
parameters: name, min, max, step
2 stratégies d’exploration:
GridSearch: teste toutes les combinaisons
EulerSearch: teste toutes les combinaisons, puis raffine à partir de la meilleure
Paramèters supplémentaires pour la subdivision des steps initiaux:
min-step, default-segment-amount
Définition des objectifs
Paramètre optimization-criterion à optimiser
Paramètre target à maximiser ou minimiser (extremum)
Cf class PerformanceMetrics
Cible à atteindre target-value
Permet d’arrêter l’optimisation de façon prématurée
Ajout de contraintes
Paramètres target, operator, target-value
Permet de disqualifier certaines configurations (risque trop élevé)

CS 405

<!-- Slide number: 74 -->
# Machine Learning pour le Trading
74
Prédiction de Séries temporelles
Régression
Prédiction du prix
Evolution des architectures
RNN (LSTM)
Transformers
CNN
Diffusion
Classification
Prédiction de la tendance (trend haussier, baissier, neutre)
Détection d’anomalie
Retours sur le trading
Marché en constante évolution (modèles MAJ)
 Régression difficile / pas très adaptée
Modèles de classification boostés relativement efficaces

CS 405

<!-- Slide number: 75 -->
# Difficultés du ML dans le trading
75
Non stationnarité
Différent des Times séries classiques
Changements continuels dans les distributions de données
Pire que ça: adversarial
Le marché s’adapte, changement de régimes intentionnels
Nécessité de beaucoup de feedback, attention aux modèles statiques
Identification de régimes distincts
Durée des transitions assez lente / difficile à détecter
Détection d’anomalie difficile
Emprise du régime localisée / globale
Intensité des changements des régimes
Données inadéquates
Ratio signal / bruit mauvais
Granularité variable des données (e.g. rapports trimestriels)
Données insuffisantes / overfitting
Importance d’un pipeline de réentraînement continu

CS 405

<!-- Slide number: 76 -->
# ML en .Net
76
ML.Net https://github.com/dotnet/machinelearning
Classification
Regression
Deep-learning
ONNX
Tensorflow.Net https://medium.com/@mariusmuntean/operationalize-tensorflow-models-with-ml-net-8b7389628d70
TorchSharp https://github.com/dotnet/TorchSharp
Infer
Programmation probabiliste
https://dotnet.github.io/infer/default.html
https://www.mbmlbook.com/toc.html
AutoML
Choix du modèle et hyperparamétrisation
« experiments » sur différents trainers
TimeSeries
Exemples
https://github.com/dotnet/machinelearning-samples/tree/main
https://github.com/dotnet/csharp-notebooks/tree/main/machine-learning
TorchSharp https://github.com/dotnet/TorchSharp
Similaire à Pytorch (Bridge)
Base de Autodiff.Net
Accord http://accord-framework.net/
Complet mais obsolète/vieillissant
SVM toujours d’actualité
Autres algos pris en charge par ML.Net
CS 405

<!-- Slide number: 77 -->
# ML dans Lean/QC
77
Exemple Accord SVM
Exemple simpliste
Entraînement à la volée
A utiliser en combinaison avec d’autres indicateurs/signaux
Intégration MyIA.Backtesting
Nombreux paramètres
Entraînement en batch
Types de modèles
Accord SVM
Type de noyau + complexité
ML.Net AutoML
Classification, métrique d’optimisation
A venir: prédiction: modèle regressif
Intégration Lean dans une branche dédiée
Nouveaux exemples QC
https://www.quantconnect.com/docs/v2/writing-algorithms/machine-learning/key-concepts
CS 405

<!-- Slide number: 78 -->
# Questions?
78
IA 101

### Notes:

<!-- Slide number: 79 -->
# Merci
79
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: