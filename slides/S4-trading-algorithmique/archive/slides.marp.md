---
marp: true
theme: ia101
paginate: true
header: 'IA 101'
footer: 'S4 - Trading Algorithmique'
---

<!-- _class: title -->

# Trading Algorithmique

Intelligence Artificielle -- S4

**Trading automatise et IA pour les marches financiers**

- Comprendre les fondamentaux du trading algorithmique
- Apprendre a utiliser Lean/QuantConnect
- Concevoir et implementer un algorithme de trading
- Évaluer et optimiser une stratégie algorithmique
- Maitriser le traitement de données et l'IA pour le trading

---

# Plan du Cours - Partie 1: Fondamentaux

- Introduction au trading algorithmique
  - Definition, profil du trader algorithmique
  - Types de trading (HFT, MFT, LFT)
- Marches financiers et instruments
  - Actions, Forex, Futures, Cryptomonnaies
- Ordres de trading
  - Types d'ordres, instructions, gestion de la visibilite
- Trouver et évaluer une stratégie
  - Sources d'idees, metriques de performance

<!-- Architecture : Market Data → Algorithme → Broker → Marche -->

---

# Plan du Cours - Partie 2: Strategies et Pratique

- Strategies de trading
  - Moyenne reversion, Momentum, Regime switching
  - Arbitrage, Market making, High-frequency trading
  - Trading saisonnier, Portefeuille a haut levier
- Backtesting et gestion du risque
  - Plateformes, mesures de performance, pieges
  - Formule de Kelly, stop loss, risques
- Lean/QuantConnect
  - Installation, environnement, framework
  - Machine learning pour le trading

---

# Qu'est-ce que le Trading Algorithmique?

- **Definition**
  - Achat et vente d'actifs financiers pilotes par des algorithmes
  - Elimination des biais emotionnels dans la prise de decision
- **Methodes d'analyse**
  - Analyse technique (indicateurs, patterns graphiques)
  - Données fondamentales (revenus, indicateurs macroeconomiques)
  - Données extra-financieres (flux d'actualites, sentiment du marche)
- **Universalite**
  - Tout ce qui est numerisable peut etre utilise en trading quantitatif
  - Diversification facilitee sur plusieurs stratégies simultanees

<!-- Flux : market data → stratégie → signaux → ordres → execution -->

---

# Profil du Trader Algorithmique

- **Formation et diplome**
  - Pas necessairement un diplome avance
  - Origines variees: sciences physiques, ingenierie, informatique
- **Competences requises**
  - Mathematiques, statistiques et programmation
  - Comprehension des marches financiers
  - Curiosite et capacite d'apprentissage continu
- **Experience pratique**
  - Finance et programmation cruciales
  - Avoir des economies pour les périodes sans gains
  - Importance de la discipline et de la gestion du stress

---

# Avantages du Trading Algorithmique

- **Scalabilite**
  - Facilite a augmenter les volumes de trading
  - Possibilite de gerer plusieurs stratégies de front
- **Optimisation du temps**
  - Moins consacre aux operations manuelles
  - Plus de temps pour la recherche et l'optimisation
- **Elimination des biais**
  - Pas de biais emotionnels dans la prise de decision
  - Execution disciplinee selon le modèle
- **Pas de necessite de marketing**
  - Pas besoin de chercher activement des clients ou investisseurs
  - Focus sur la performance algorithmique

---

# Types de Trading Algorithmique (1/2)

- **HFT (High-Frequency Trading)**
  - Operations en millisecondes ou microsecondes
  - Objectif: Exploiter de petites inefficacites du marche
  - Technologie: Necessite une infrastructure technologique de pointe
- **MFT (Medium-Frequency Trading)**
  - Operations sur des secondes, minutes a quelques heures
  - Objectif: Arbitrage, suivi de tendance, et autres stratégies
  - Flexibilite: Moins exigeant technologiquement mais necessite une analyse de données robuste

---

# Types de Trading Algorithmique (2/2)

- **LFT (Low-Frequency Trading)**
  - Operations sur des jours, semaines ou mois
  - Objectif: Investissement base sur des facteurs fondamentaux ou des indicateurs techniques
  - Gestion du Risque: Focalisation sur la reduction du risque a long terme
- **Chaque type a ses specificites**
  - Avantages et inconvenients propres
  - Necessite des competences, des infrastructures et des ressources differentes
  - Offre des opportunites de rendement variables

<!-- Frequences : HFT (us) → intraday (min) → swing (jours) → position (mois) -->

---

<!-- _class: questions -->

# Questions?

---

# Vue d'ensemble du Marche

- **Marches Principaux**
  - Actions, Forex, Futures, Cryptomonnaies
- **Roles des Participants**
  - Traders particuliers, institutionnels, market makers, arbitragistes
  - Fournisseurs de liquidite, preneurs de liquidite
- **Reglementations**
  - MiFID II en Europe
  - Dodd-Frank aux Etats-Unis
- **Importance des Données**
  - Tickers, Order Book, Volume, Time & Sales
  - Impact de la qualite et de la frequence (temps reel vs resolution)

<!-- Participants : market makers, hedge funds, retail, institutionnels -->

---

# Instruments Financiers

![bg right:30%](images/candlestick_patterns.png)

- **Actions**
  - Titres qui representent une fraction de la propriété d'une entreprise
- **Forex**
  - Echange de devises etrangeres, souvent a des fins de speculation ou de couverture
- **Futures**
  - Contrats qui obligent a acheter ou vendre un actif a un prix fixe a une date future
- **Cryptomonnaies**
  - Monnaies numeriques qui utilisent la cryptographie pour securiser les transactions
  - Aspects reglementaires variables
- **Classes d'actifs**
  - Categories d'investissement (actions, obligations, matieres premieres)
  - Diversification du risque

---

# Analyse Technique et Fondamentale

![bg right:30%](images/candlestick_anatomy.png)

- **Analyse Technique**
  - Étude des graphiques de prix et de volume
  - Indicateurs: moyennes mobiles, RSI, MACD, Bollinger Bands
  - Patterns graphiques: chandeliers, tete-epaules, triangles
- **Analyse Fondamentale**
  - Évaluation de la valeur intrinseque d'un actif
  - Données financieres: revenus, benefices, ratios
  - Indicateurs macroeconomiques: taux d'intérêt, inflation, PIB
- **Combinaison des deux approches**
  - Analyse technique pour le timing d'entree/sortie
  - Analyse fondamentale pour la selection d'actifs

<!-- Indicateurs : SMA/EMA crossovers, RSI zones, Bollinger Bands -->

---

# Infrastructure de Trading

- **Plateformes et Courtiers**
  - Interactive Brokers, MetaTrader, Robinhood
- **API de Trading**
  - Interface de programmation permettant l'automatisation des ordres
  - FIX, REST APIs, WebSocket
- **Flux de Données**
  - Fournit des informations en temps reel ou differe sur les marches
  - Certaines plateformes offrent des flux combines
- **Latence et Couts**
  - Delais d'execution: Temps entre la soumission et l'execution d'un ordre
  - Couts de transaction: Frais associes a l'achat et a la vente d'actifs
- **Exigence d'Infrastructure**
  - Serveurs co-localises, GPUs pour ML

<!-- Infrastructure : datacenter, co-location, APIs broker -->

---

# Les Ordres de Trading - Types d'Ordres (1/2)

- **Les ordres sont cruciaux pour toute stratégie de trading**
- **Ordres au marche**
  - Execution: Immédiate au meilleur prix
  - Risque: Prix d'execution incertain
  - Impact: Peut affecter significativement le marche
- **Ordres a cours limite**
  - Controle: Prix limite pour l'achat/vente
  - Flexibilite: Utilisation aggressive ou passive
  - Risque: Execution incertaine

---

# Les Ordres de Trading - Types d'Ordres (2/2)

- **Ordres conditionnels et hybrides**
  - Complexite: Inclut des ordres caches, routes
  - Utilite: Pour des stratégies plus avancees
- **Ordres stop**
  - Declenchent un ordre au marche ou limite une fois qu'un prix predefini est atteint
- **Choix du type d'ordre**
  - Depend du besoin d'immediateté et du controle du prix
  - Ordres au marche sont rapides mais incertains en prix
  - Ordres a cours limite offrent plus de controle mais moins de certitude
- **Impact du mode d'execution**
  - Bourse centrale vs. Dark pools

<!-- Ordres : market, limit, stop, stop-limit, trailing stop -->

---

# Ordres - Instructions Optionnelles (1/2)

- **Les instructions optionnelles offrent plus de controle sur vos ordres**
- **Instructions de Duree: "Good 'til"**
  - GTD: Actif jusqu'a une date donnee
  - GTC: Actif jusqu'a annulation
  - GAT: Actif a un moment donne
- **Instructions d'Encheres**
  - On-open: Pour enchere d'ouverture
  - On-close: Pour enchere de cloture
  - Next-auction: Pour prochaine enchere valide

---

# Ordres - Instructions Optionnelles (2/2)

- **Instructions de Remplissage**
  - IOC: Execution ou annulation immediate
  - FOK: Fill-or-Kill: Execution totale immediate ou annulation
  - AON: All-or-None: Execution totale requise
  - Minimum-Volume: Volume minimum requis
- **Importance pour l'efficacite**
  - Comprendre ces instructions ameliore l'efficacite de trading
  - Permettent d'adapter vos ordres a differentes situations de marche

---

# Ordres - Instructions Specifiques (1/2)

- **Ordres Must-Be-Filled (MBF)**
  - Execution Totale: Doivent etre executes en totalite
  - Interruption de volatilite: Declenche une interruption si non execute
  - Session de Trading Separee: Session speciale pour ces ordres
- **Preferencement et Instructions Dirigees**
  - Trading Bilateral: Direction vers un courtier specifique
  - On parle d'internalisation
  - Controverse: Contournent les règles de priorite
  - Amelioration de Prix: Mecanismes speciaux pour ameliorer le prix

---

# Ordres - Instructions Specifiques (2/2)

- **Instructions de Routage**
  - Do-Not-Route: Execution locale uniquement
  - Directed-Routing: Routage vers un marche specifique
- **Inter-Market Sweeps**
  - Balayage: Balaye le carnet d'ordres sur un marche donne
- **Instructions de Liaison**
  - One-Cancels-Other (OCO): Deux ordres sont mutuellement exclusifs
  - One-Triggers-Other (OTO): Un ordre declenche un autre ordre
- **Instructions Diverses**
  - Anonymat: Certains marches offrent l'anonymat
  - Ventes a Decouvert: Drapeau requis sur certains marches
  - Lots Impairs: Appariement de lots ronds avec lots impairs

---

# Types d'Ordres bases sur des Conditions

- **Ordres a seuil de declenchement suiveur (Trailing Stop)**
  - Verrouillage des prix: S'adapte au marche
  - Flexibilite: Maximise les gains sans predire le stop
  - Ex: Stop de vente a -5% dont le seuil remonte avec le cours
- **Ordres conditionnels / Si touche**
  - Logique d'activation: Cache jusqu'a un niveau de prix
  - Polyvalence: Bases sur le prix d'autres actifs
- **Ordres sensibles au tick**
  - Dependance au tick: Execute si le dernier prix repond a des conditions
  - Impact sur le marche: Minimise pour un meilleur prix

---

# Types d'Ordres - Gestion de la Visibilite (1/2)

- **Types d'ordres caches**
  - Ordres Iceberg
  - Partie visible et cachee
  - Frequents sur les marches a forte liquidite (actions, futures)
  - Priorite: Plus basse que les ordres visibles
- **Types d'ordres discretionnaires**
  - Ordres non tenus
  - Trader decide de l'execution
  - Évolution: Plus basees sur des règles

---

# Types d'Ordres - Gestion de la Visibilite (2/2)

- **Ordres ajustes (Pegged)**
  - Prix dynamique: Suivre la meilleure offre ou demande
- **Ordres achemines (Routed)**
  - Strategies complexes: Routage vers differents lieux
  - Smart Order Routing: Strategies complexes
  - Ex: Interactive Brokers SmartRouting
  - Permet d'eviter le slippage ou optimise l'execution

---

# Autres Types d'Ordres - Specialises

- **Ordres de croisement**
  - Types varies: Committed, Uncommitted, etc.
  - Mecanismes varies: Differents réseaux de croisement
- **Ordres non engages**
  - Similaires aux IOIs: Besoin de confirmation
  - Protection: Tailles minimales, etc.
- **Ordres negocies**
  - Mecanisme bilateral: Environnement de negociation
  - Anonymat: Entre investisseurs ou fournisseurs de liquidite
- **Alertes Automatisees**
  - Notification aux PLPs: Exemple de Millennium ATS

---

# Order-Contingent et Implied Orders

- **Order-Contingent Order Types**
  - Ordres Lies-Alternatifs: Liste d'ordres alternatifs
  - Ordres Contingents: Ajustent prix et taille
- **Implied Orders**
  - Ordres Implicites: Ajustent prix et taille
  - Importance: Liquidite supplementaire en marche a terme

<!-- Flux d'ordres : signal → validation → sizing → execution → monitoring -->

---

<!-- _class: questions -->

# Questions?

---

# Trouver une Strategie qui vous Convient (1/2)

- **Sources d'Idees**
  - Articles academiques, blogs, forums, medias
  - Suivi des meilleures stratégies sur plateformes
- **Modification de Strategies**
  - Ajustements pour rentabilite
- **Echange d'idees**
  - Blogs de trading pour partage
- **Strategies qui vous conviennent**
  - Temps disponible: Temps complet vs temps partiel
  - Academiques vs. Publiques: Complexite vs simplicite
  - Competences en programmation: Elargit les options

---

# Trouver une Strategie qui vous Convient (2/2)

- **Votre Capital de Trading**
  - Ancien minimum conseille de 50 000 $
  - Nouveaux minima grace aux cryptos et frais reduits
- **Votre Objectif**
  - Revenu regulier vs gains en capital

---

# Comment Évaluer une Strategie?

- **Mesures Standard**
  - Ratio de Sharpe: Mesure le rendement ajuste au risque
  - High Watermark: Rendement cumule maximal a un moment donne
  - Drawdown Maximum et Duree: La plus grande baisse et le temps pour recuperer
- **Criteres de performance**
  - Rendement annualise
  - Volatilite des rendements
  - Ratio gain/perte moyen
  - Taux de reussite des trades

<!-- Metriques : equity curve, drawdowns, ratio de Sharpe (rendement/risque) -->

---

# Strategies Plausibles et leurs Pieges (1/2)

- **Drawdowns**
  - Perte de valeur, profondeur et duree a évaluer
- **Slippage**
  - Ecart de prix entre ordre et execution
- **Couts de Transaction**
  - Impact sur les stratégies a haute frequence
- **Évolution du Marche**
  - Efficacite moindre qu'il y a 10 ans
  - Les marches sont plus efficients

---

# Strategies Plausibles et leurs Pieges (2/2)

- **Changements de Regime**
  - Données historiques parfois non pertinentes
- **Overfitting**
  - Surajustement aux données historiques
- **Frais de financements**
  - Pour les positions a marge

<!-- Overfitting : performance train >> test = surapprentissage -->

---

# Intelligence Artificielle et Selection de Stocks

- **Scepticisme initial sur l'IA**
  - Tendance a surajuster les données
- **Pratiques qui fonctionnent en IA**
  - Modeles simples, fondements econometriques
  - Mixture d'experts
- **Strategies "Sous le Radar"**
  - Faible capacite
  - Moins d'arbitrage par grands fonds
- **Avancees recentes**
  - "Guerre" des modèles
  - Théorie des jeux

<!-- Mixture d'experts : modèles multiples → vote pondere → decision -->

---

<!-- _class: questions -->

# Questions?

---

# Backtesting (1/2)

- **Qu'est-ce que c'est?**
  - Évaluation d'une stratégie d'investissement sur des données historiques
- **Pourquoi c'est important**
  - Valider l'efficacite de la recherche originale
  - Experimenter avec des variations pour l'optimiser
- **Sources de Données**
  - Recherche web pour des bases gratuites ou peu couteuses
  - Yahoo Finance, Alpha Vantage, Interactive Brokers, Binance

---

# Backtesting (2/2)

- **Pieges et Problemes**
  - Données ajustees pour les splits et les dividendes: Risque de faux signaux
  - Biais de survie: Surevaluation potentielle des performances
- **Dans le cas ou le Machine Learning est utilise**
  - Le backtesting doit prendre en compte les biais de selection de données
  - Separer convenablement les ensembles (training, validation, test)
  - Évaluer la generalisation

<!-- Pipeline : données historiques → stratégie → simulation → évaluation -->

---

# Plateformes de Backtesting (1/2)

- **Excel**
  - Toutes les données sont visibles, ce qui reduit le risque de "look-ahead bias"
  - Utilise a la fois pour le backtesting et le trading en direct
  - Inconvenients: Limite aux modèles simples d'investissement
- **MATLAB**
  - Utilise en institutionnel, excellent pour tester des stratégies sur de grands portefeuilles
  - Modules statistiques avances
  - Inconvenients: Couteux et moins efficace pour executer les trades

---

# Plateformes de Backtesting (2/2)

- **TradeStation et autres plateformes**
  - Execution des trades possible directement depuis la plateforme
  - Données historiques integrees
  - Inconvenients: Langage proprietaire, vous attache a TradeStation comme courtier
- **Évolution des Plateformes**
  - Python & R: Ont pris le relais de MATLAB dans la plupart des cas
  - Exemple: Zipline et autres frameworks open-source
  - C#: Alternative montante grace aux efforts de Microsoft et Lean

---

# Lean / QuantConnect

- **Solution open-core en Python et C#**
  - 3 environnements (Lean, Lean-cli-QC)
  - Permettent backtesting, paper trading et live trading
  - Utilisee dans ce cours
- **Avantages**
  - Lean gere nativement les ajustements de données (splits, dividendes)
  - Fournit un grand catalogue de données alternatives
  - Simplifie l'évaluation point-in-time

<!-- QuantConnect : IDE cloud + Lean Engine open-source -->

---

# Mesures de Performance et Pieges (1/2)

![bg right:25%](images/efficient_frontier.png)

- **Mesures Standard**
  - Ratio de Sharpe: Mesure le rendement ajuste au risque, souvent annualise
  - High Watermark: Rendement cumule maximal a un moment donne
  - Drawdown Maximum et Duree: La plus grande baisse et le temps pour recuperer
- **Pieges courants**
  - Look-ahead bias: Utilisation de données futures dans le calcul
  - Data-Snooping Bias: Overfitting base sur les données historiques
  - Couts de Transaction: Omission des couts associes aux transactions

---

# Mesures de Performance et Pieges (2/2)

- **Avec Machine Learning**
  - Derive des données (data drift)
  - La distribution des données évolue dans le temps
  - Rend les patterns historiques obsoletes

<!-- Data drift : distributions qui changent entre train et production -->

---

# Precautions face aux Pieges (1/2)

- **Look-ahead**
  - Utilisation de données decalees
  - Forward-testing (paper trading)
- **Data-Snooping Bias**
  - Peu de parametres
  - Augmentation, division et adaptation des données de backtest
- **Modeles de trading sans parametres**
  - Pas de surajustement, fiabilite mais complexité computationnelle

---

# Precautions face aux Pieges (2/2)

- **Paper Trading**
  - Test sur des données reelles non vues, le plus fiable
- **Analyse de sensibilite**
  - Variation des parametres pour évaluer la stabilite de la performance
- **Simplification du modèle**
  - Elimination des conditions superflues
- **Repartition du capital de trading**
  - Entre differentes stratégies pour diminuer la variance
- **Couts de Transaction**
  - A integrer dans le Backtest pour des resultats plus realistes
- **Derive des données (data drift) et non stationnarite**
  - Revalider regulierement les modèles
  - Appliquer des techniques comme la differenciation fractionnaire

---

# Affinement de la Strategie

- **Le Probleme**
  - Rendements diminuent quand une stratégie est populaire
- **Solutions**
  - Variations Mineures: Petites variations peuvent ameliorer les rendements
  - Exclusion de Stocks: Eviter certains types d'actions
  - Changement de Timing: Ajuster les points d'entree et de sortie

---

<!-- _class: questions -->

# Questions?

---

# Gestion du Risque - Introduction

- **La gestion du risque permet de "preserver" le capital initial tout en optimisant la croissance sur le long terme**
- **Maximisation de la Croissance**
  - Objectif de maximiser la croissance du capital a long terme
  - Rendement Moyen: ( m )
  - Variance des Rendements: ( s^2 )
- **Eviter la Ruine**
  - Eviter une chute catastrophique du capital a zero
  - Drawdown: Chute maximale du capital sur une période donnee

---

# Outils et Formules

![bg right:30%](images/normal_distribution.png)

- **Formule de Kelly**
  - Determine la fraction optimale du capital a risquer par trade
  - f* = (p * b - q) / b
  - p = probabilité de gain, q = probabilité de perte (1-p)
  - b = ratio gain/perte moyen
- **Value-at-Risk (VaR)**
  - Estime la perte maximale potentielle sur une période
  - Avec un niveau de confiance donne
- **Conditional Value-at-Risk (CVaR)**
  - Estime la perte moyenne au-dela du VaR
  - Prend en compte les "fat tails"

---

# Gestion du Risque avec la Formule de Kelly

- **Gestion avec la Formule de Kelly**
  - Reduction de la Taille du Portefeuille: Si les pertes augmentent, reduisez f
- **Contagion Financiere**
  - Le risque de propagation des pertes entre les fonds
- **Evenements Extremes (Black swans)**
  - Limites de la Formule: Ne prend pas en compte les "fat tails"
  - Gestion des Evenements Imprevus: Utilisation de modèles de Value-at-Risk (VaR)
- **Utilisation de Stop Loss**
  - Momentum vs Mean-Reverting: L'efficacite varie en fonction du regime du marche
  - Fondamental vs Liquidite: Quand appliquer les stop loss

---

# Autres Types de Risques

- **Risque de Modele**
  - Biais de survie, biais de lookahead, et erreurs de données
  - Changements structurels du marche comme l'impact des nouvelles reglementations
- **Risque Logiciel**
  - Bugs, latence et decalages de données
  - Assurez-vous que le système de trading automatise est bien teste et surveille
- **Risques Physiques**
  - Pannes de courant, defaillance du materiel, cyberattaques
  - Solution de secours et plan de recuperation en cas de catastrophe

---

# Preparation Psychologique (1/2)

- **Emotions en Trading**
  - Overtrading en période de gains
  - Aversion au risque en période de pertes
  - Importance de suivre scrupuleusement le modèle
- **Biais Comportementaux**
  - Effet de dotation
  - Biais du statu quo
  - Aversion a la perte
  - Biais de representativite
  - Comment ces biais affectent la prise de decision en trading

---

# Preparation Psychologique (2/2)

- **Desespoir et Avidite**
  - Importance de la gestion du stress et de la psychologie
  - Mettre en place des garde-fous pour eviter la prise de decisions impulsives
- **Conseils Pratiques**
  - Commencez petit pour tester votre discipline
  - Avoir un tampon financier ou des sources de revenus alternatives
  - Reduire la pression financiere et psychologique
  - Necessite parfois d'un support psychologique ou d'un coaching (cf. Athletes)

---

<!-- _class: questions -->

# Questions?

---

# Strategies de Moyenne Reversion

![bg right:30%](images/bollinger_bands.png)

- **Moyenne Reversion**
  - Les prix des actions ont tendance a revenir vers une moyenne a long terme
- **Recherche Academique**
  - Proximite a une marche aleatoire
  - Mais certaines conditions permettent la moyenne reversion
- **Pieges en Backtesting**
  - Biais de Survie: Ignorer les actifs disparus peut fausser les resultats
  - Erreurs de Base de Données: Incoherences dans les données financieres
- **Effets de la Concurrence**
  - Reduit les opportunites d'arbitrage, diminuant les rendements

<!-- Mean reversion : achat sous bande basse, vente au-dessus de bande haute -->

---

# Strategies Fondamentales de Momentum

![bg right:30%](images/macd_chart.png)

- **Momentum**
  - Tendance d'un actif a continuer a se deplacer dans la meme direction pendant une certaine période
- **Diffusion Lente de l'Information**
  - Cree des opportunites de momentum
- **Comportement de Troupeau**
  - Les investisseurs suivent les autres, amplifiant les tendances
- **Horizons Temporels Imprevisibles**
  - Imprevisibilite de la duree du momentum
- **Effets de la Concurrence**
  - Accelere l'atteinte de l'équilibre des prix
  - Rend les stratégies de momentum moins efficaces a long terme

<!-- Crossover : EMA rapide croise EMA lente → signal achat/vente -->

---

# Strategies de Regime Switching (1/2)

- **Concept & Types**
  - Les Marches varient entre differents regimes
  - (haussiers/baissiers, inflation/recession, volatilite)
  - La Prediction de ces regimes est un defi
- **Outils & Approches - GARCH**
  - Modele "autoregressif conditionnellement heteroscedastique generalise"
  - Utile pour mesurer la volatilite, moins pour le prix d'actions

---

# Strategies de Regime Switching (2/2)

- **Modeles probabilistes**
  - Modeles de Markov, de Kalman etc.
  - Necessite un modèle de variables hypothetiques ou variables latentes
  - Tres puissant mais complexe
- **Data Mining**
  - Utilise indicateurs techniques, données macro, "buzz" mediatique
- **Application Pratique**
  - Machine Learning pour detection en temps reel
  - Attention aux pieges: biais de "data snooping" et optimisation excessive

<!-- HMM : etats caches (bull/bear) → observations (rendements) -->

---

# Ponderations par le Volume et le Temps

- **VWAP - Volume Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le volume
  - Utilisation: Frequemment utilise en trading institutionnel pour minimiser l'impact du marche
  - Mecanisme: Calcule le rapport cout/volume a des intervalles reguliers et execute des ordres en fonction
- **TWAP - Time Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le temps
  - Utilisation: Utilise lorsque l'impact du volume sur le prix est moins pertinent
  - Mecanisme: Divise un gros ordre en plus petits morceaux, executes a intervalles reguliers
- **TWAP/VWAP sont tres utilises par les institutionnels**
  - Pour eviter un prix moyen trop deforme

<!-- VWAP = pondere par volume, TWAP = pondere par temps -->

---

# Strategies Basees sur les Données - Modeles Factoriels

![bg right:25%](images/security_market_line.png)

- **Exposition Factorielle**
  - Mesure la sensibilite d'un actif a differents facteurs du marche
  - Taux d'intérêt, volatilite du marche
- **Rendement Factoriel & Specifique**
  - Le rendement factoriel est celui qui peut etre attribue a l'exposition a certains facteurs
  - Le rendement specifique est le rendement qui n'est pas explique par ces facteurs
- **Utilisation**
  - Ces modèles sont couramment utilises pour la construction de portefeuilles
  - Pour comprendre les sources de rendement

<!-- Correlations entre facteurs : momentum, value, size, quality -->

---

# Strategies Basees sur les Données - Sentiment Analysis

- **Objectif**
  - Exploiter les données textuelles pour predire les mouvements du marche
- **Technologie**
  - Utilise des techniques de NLP (Natural Language Processing)
  - Analyse des textes tels que les nouvelles, les tweets, etc.
- **Mecanisme**
  - Le sentiment du marche est extrait des données textuelles
  - Utilise pour générer des signaux de trading
- **Utilisation Pratique**
  - Les hedge funds et les traders algorithmiques utilisent l'analyse du sentiment
  - Pour ameliorer leurs stratégies
- **Importance de la mise en place d'un pipeline de données**
  - Collecte, nettoyage, feature engineering etc.

---

# Metriques des Modeles Factoriels

- **Metriques Standards**
  - R-squared: Proportion de variance expliquee
  - Alpha: Rendement ajuste au risque
  - Beta: Sensibilite au marche
  - Information Ratio: Rendement actif par unite de risque actif
- **Analyse de Performance**
  - Attribution de performance par facteur
  - Contribution au risque par facteur
  - Correlation entre facteurs

<!-- Attribution : alpha + beta*marche + facteurs + residuel -->

---

# Strategies Basees sur les Données 2.0 (1/2)

- **Methodes Modernes**
  - Multi-Factoriels: Évolution des modèles 3F de Fama-French vers des modèles multi-factoriels
- **Machine Learning en Trading**
  - Machine Learning Parametrique: Utilisation de réseaux neuronaux et de modèles sequentiels en deep learning comme LSTM
  - Machine Learning Non-Parametrique: Emploi de forets aleatoires, k-NN, SVM pour capturer des relations non-lineaires
  - Succes des techniques d'ensemble, Mixture of experts

---

# Strategies Basees sur les Données 2.0 (2/2)

- **Avancees en ML et RL**
  - Modeles Sequentiels: Utilisation de LSTM, de GRU, de Transformers en deep learning
  - Reseaux bayesiens dynamiques pour capturer des dependances temporelles
  - Reinforcement Learning (RL): Application a l'optimisation de stratégie en temps reel
  - Prise de decision avec ou sans modèle predictif associe
- **Analyse & Risques Modernes**
  - Metriques Modernes: Transition du R² vers des mesures comme l'Information Ratio
  - Optimisation Bayesienne: Utilisee pour la selection de modèle et l'ajustement de parametres
  - Mise a Jour Continue: Adaptation aux changements de comportement du marche via techniques d'apprentissage en ligne

---

# Workflows Semantique et Théorie des Jeux

- **Workflows semantique**
  - Avenement des LLMs (ChatGPT, Llama etc.)
  - Analyse de sentiment avancee
  - Génération de signaux a partir de données textuelles
- **Théorie des jeux**
  - Strategies adversariales, poursuite et predation
  - Signalement (baleines etc.)
  - Flash crashs et manipulation de marche
  - Modelisation des interactions entre traders

<!-- Game theory : interactions strategiques entre traders -->

---

<!-- _class: questions -->

# Questions?

---

# Strategies de Sortie en Trading (1/2)

![bg right:25%](images/payoff_put_option.png)

- **Periode de Detention Fixe**
  - Utilisee par defaut dans divers modèles de trading
  - Momentum: La période optimale peut etre trouvee via un backtest
  - Attention a l'évolution rapide de l'information
  - Reversion a la Moyenne: Une methode plus robuste pour determiner la période optimale est disponible
- **Prix ou Profit Cible**
  - Utilise pour definir un objectif de sortie
  - Reversion a la Moyenne: Le prix moyen historique peut servir de prix cible
  - Momentum: Moins fiable car base sur une évaluation fondamentale incertaine

---

# Strategies de Sortie en Trading (2/2)

- **Derniers Signaux d'Entree**
  - Utiliser le signal d'entree le plus recent comme signal de sortie
  - Momentum: Si le signal change, c'est presque comme un stop-loss
  - Reversion a la Moyenne: Le signal reste generalement le meme, donc pas de stop-loss recommande
- **Prix Stop**
  - Rarement utilise de maniere efficace
  - Momentum: Peut etre justifie si le sens du momentum change
  - Reversion a la Moyenne: Souvent contre-productif, sauf en cas de changement de regime du a des nouvelles

---

# Strategies de Sortie 2.0 (1/2)

- **Categories Classiques**
  - Periode de Detention Fixe: Adaptation via ML pour prediction de la période optimale
  - Prix ou Profit Cible: Integration de données en temps reel pour ajuster les cibles
  - Derniers Signaux d'Entree & Prix Stop: Utilisation rare, mais avec opportunites pour optimisation par RL
- **Avancees en ML et Analyse Temps Reel**
  - Deep Learning: Utilisation de CNN ou LSTM pour detection de patterns et ajustement de la stratégie de sortie
  - Reinforcement Learning (RL): Apprentissage pour optimiser la sortie en fonction du rendement et du risque

---

# Strategies de Sortie 2.0 (2/2)

- **Gestion de Risques Avancee**
  - Options & Derives: Utilisation pour couvrir les positions et ajuster les stratégies de sortie
  - Analyse Sentimentale: Utilisation de NLP pour ajuster les stratégies en fonction du sentiment du marche
- **Alertes et Ajustements en Temps Reel**
  - Web Scraping & API: Collecte en temps reel de données de marche pour ajuster les stratégies
  - Optimisation Continue: Mise a jour en temps reel des parametres via techniques d'apprentissage en ligne

---

# Arbitrage et Paires

- **Pairs Trading**
  - Objectif: Capitaliser sur la relation entre deux actifs similaires
  - Utilisation: Necessite une analyse de co-integration
  - Mecanisme: Achete un actif et vend un actif similaire en anticipation d'une convergence des prix
- **Statistical Arbitrage**
  - Objectif: Exploiter les ecarts de prix entre des actifs fortement correles
  - Utilisation: Necessite une modelisation statistique complexe
  - Mecanisme: Utilise des modèles statistiques pour identifier les opportunites d'arbitrage

![bg right:30%](images/ted_spread.png)

---

# Market Making et Optimal Trading

- **Market Making**
  - Objectif: Acheter et vendre activement pour profiter de l'ecart acheteur-vendeur
  - Utilisation: Necessite une tres faible latence et de gros volumes
  - Mecanisme: Fournit des liquidites en affichant constamment des offres d'achat et de vente
- **Optimal Trading Strategies**
  - Objectif: Minimiser les couts de transaction et l'impact du marche
  - Utilisation: Generalement utilise par les fonds institutionnels et les traders a haute frequence
  - Mecanisme: Utilise des algorithmes pour optimiser le timing et le cout des ordres

<!-- Market making : bid-ask spread, gestion d'inventaire, risque -->

---

# Strategies de Trading a Haute Frequence (1/2)

- **Exploite de petites inefficacites sur le marche ou fournit une liquidite temporaire en echange d'une petite commission**
- **Ratio de Sharpe Eleve**
  - Loi des grands nombres stabilise le rendement
  - Centaines de paris par jour minimisent les ecarts de rendement
- **Difficultes et Defis**
  - Couts de transaction cruciaux pour les tests
  - Execution a haute vitesse pour maximiser profits/pertes
  - Risque de liquidation rapide (slippage, anomalies de marche)

---

# Strategies de Trading a Haute Frequence (2/2)

- **Machine Learning et AI**
  - Utilisation de modèles de Deep Learning pour prediction de micro-tendances
  - Reinforcement Learning pour l'ajustement dynamique de stratégies
- **Latence Ultra-Faible**
  - Utilisation de FPGA (Field-Programmable Gate Arrays) pour des ordres en microsecondes
  - Co-location de serveurs pres des bourses
- **Risques et Reglementations**
  - Detection d'abus de marche par des algorithmes de surveillance
  - Impact des regulations comme MiFID II sur la transparence

<!-- HFT : FPGA, co-location, latence microseconde -->

---

# Strategies de Trading Saisonnier

- **Effet de Janvier**
  - Petites capitalisations beneficient en janvier
  - Vendre en decembre pour raisons fiscales
- **Strategies Mensuelles**
  - Acheter/vendre selon la performance du mois precedent
  - Efficace jusqu'a 2002
- **Strategies Matieres Premieres**
  - Essence et gaz naturel
  - Fiable car base sur besoins economiques (ex. petrole en ete)
- **Precautions**
  - Biais de Data-Snooping
  - Verifier la fiabilite et le sens economique

---

# Strategies de Trading Saisonnier 2.0 (1/2)

- **Concepts Traditionnels**
  - Effet de Janvier: Machine learning pour identifier les meilleures opportunites en temps reel
  - Strategies Mensuelles: Utilisation d'algorithmes adaptatifs pour revalider l'efficacite
  - Strategies Matieres Premieres: Optimisation par RL pour des meilleures entrees et sorties
- **Innovations en ML & Data Analytics**
  - Time Series Forecasting: LSTM et ARIMA pour predire la saisonnalite
  - Reinforcement Learning (RL): Maximisation des rendements en adaptant les stratégies saisonnieres
  - Random Forest & SVM: Classification pour detecter les meilleures périodes d'achat/vente

---

# Strategies de Trading Saisonnier 2.0 (2/2)

- **Intelligence Contextuelle**
  - IoT & Big Data: Utilisation de données meteorologiques et de flux logistiques pour optimiser les trades en matieres premieres
  - Sentiment Analysis: Évaluer l'effet du sentiment saisonnier sur les marches
- **Gestion de Risques Avancee**
  - Simulation de Monte Carlo: Estimation des intervalles de confiance pour les stratégies
  - Backtesting Adaptatif: Tests dynamiques pour ajuster aux changements du marche

---

# Portefeuille a Haut Levier vs Haut Beta (1/2)

![bg right:25%](images/capital_market_line.png)

- **Beta**
  - Mesure de la sensibilite d'un actif par rapport au marche
  - Haut Beta: Plus volatil, plus de rendements mais plus de risques
  - Faible Beta: Moins de risques, meilleur ratio de Sharpe
- **Levier**
  - Utilisation d'emprunts pour augmenter l'exposition aux actifs
  - Effet Amplificateur: Augmente les gains mais aussi les pertes
  - Risques de Queue Epaisse: Pertes imprevues dues a une distribution de rendements atypique

---

# Portefeuille a Haut Levier vs Haut Beta (2/2)

- **Ratio de Sharpe**
  - Mesure le rendement ajuste au risque
  - Croissance Composee: Proportionnelle au carre du ratio de Sharpe
- **Allocation d'Actifs**
  - Repartition du portefeuille entre differentes classes d'actifs
  - Optimisation 23-77: Entre actions a faible beta et obligations pour un risque minimal
- **Un faible beta avec un levier modere**
  - Offre theoriquement une meilleure croissance composee a long terme (cf. formule de Kelly)
  - Mais avec des risques inherents

<!-- Levier vs beta : amplification rendement ET risque -->

---

# Portefeuille a Haut Levier vs Haut Beta 2.0 (1/2)

- **Beta Adaptatif**
  - Utilisation de l'apprentissage machine pour ajuster dynamiquement le beta
  - Predictions de Volatilite: Utilisation de series temporelles pour anticiper les changements de volatilite
- **Levier avec Machine Learning**
  - Algorithmes pour decider du moment optimal pour appliquer un levier
  - Risques de Catastrophe: Utilisation d'alertes algorithmiques pour reduire le levier en cas de signaux de crash

---

# Portefeuille a Haut Levier vs Haut Beta 2.0 (2/2)

- **Optimisation de Ratio de Sharpe avec IA**
  - Utilisation de réseaux de neurones pour maximiser le ratio de Sharpe
  - Apprentissage par Renforcement: Pour une allocation d'actifs dynamique et optimisee
- **Gestion du Risque 2.0**
  - Techniques modernes comme le "Value-at-Risk" (VaR) base sur le deep learning
  - Indicateurs de Sentiment du Marche: Via le traitement du langage naturel pour anticiper les changements de marche
- **La version 2.0 integre des techniques d'apprentissage machine et d'analyse de données pour une gestion plus proactive et adaptative du risque et du rendement**

---

<!-- _class: questions -->

# Questions?

---

<!-- _class: title -->

# Initiation a Lean

Documentation officielle QuantConnect

---

# Lean/QuantConnect

- **Qu'est-ce que c'est?**
  - Plateforme de trading algorithmique
- **Langages de Programmation**
  - C#, Python
- **Fonctionnalites Principales**
  - Notebooks d'analyse, Backtesting, optimisation, paper et live trading
- **Data Library**
  - Données historiques de plusieurs marches
- **Communaute & Ressources**
  - Forums, tutoriels, documentation

<!-- QuantConnect IDE : editeur + resultats de backtest integres -->

---

# Installation de l'Environnement (1/2)

- **3 environnements**
  - QuantConnect: Plateforme dans le Cloud
  - Lean-Cli + vscode: Plateforme hybride QC + containers locaux
  - Lean: Plateforme Open-source locale
- **QuantConnect**
  - Creer un compte
  - Organisations, Noeuds de ressources
- **Lean-cli**
  - Terminal
  - IDEs locaux

---

# Installation de l'Environnement (2/2)

- **VS Code**
  - Extensions: C# dev kit, polyglot, python, git extension pack, Python extension pack, QuantConnect
- **Visual Studio Community / for Mac**
  - Charge de developpement Desktop (Windows) / .Net (Mac)
- **DotPeek (desassembleur)**
- **Jetbrains Rider**
  - Licence?

<!-- VS Code : extension QuantConnect pour developpement local -->

---

# Mise en Route Lean-cli / VScode

- **Installation pip**
  - `pip install --upgrade lean`
  - `lean --version`
- **Sur QuantConnect**
  - My Account – Request Token Information
- **Lean init**
  - Choix de l'"Organisation"
- **Synchronisation**
  - `lean cloud pull`
  - `lean cloud push`

<!-- lean-cli : lean backtest, lean live, lean research -->

---

# Mise en Route Lean (1/2)

- **Fork/Clone git de Lean**
  - Dans le repertoire de votre choix
  - Depot personnalise: https://github.com/myintelligenceagency/Lean
- **Ouvrir la solution**
  - QuantConnect.Lean.sln
  - Affichage des projets, projet de demarrage par defaut
- **Generer la solution**
  - Restauration des packages, compilation des projets

---

# Mise en Route Lean (2/2)

- **Executer le Launcher**
  - Demarrage en debug
  - Fichier de config `Lean/Launcher/bin/debug/config.json`
  - Algorithme par defaut: BasicTemplateFrameworkAlgorithm
  - Placer un point d'arret dans la fonction Initialize et relancer
- **Desassemblage**
  - DotPeek / serveur de symboles
- **Developpement et debuggage en Python**
  - https://github.com/MyIntelligenceAgency/Lean/blob/master/ESGF/Python.md

---

# Environnement d'Algorithme (1/2)

- **QCAlgorithm**
  - Ticker vs Bar
  - Evenements => pas de lookahead
  - + Interfaces + Classes de base
  - + Strategic Development Framework
- **Objets fondamentaux**
  - Time
  - Symboles
  - Portfolio
  - Securities
  - Brokers

---

# Environnement d'Algorithme (2/2)

- **Objets fondamentaux (suite)**
  - Indicateurs (e.g. EMA)
  - History
- **Membres locaux**
  - Manipules par les methodes
  - Parfois herites + "Parameters"
  - Possibilite de les initializer

<!-- QCAlgorithm : Initialize, OnData, Portfolio, Securities -->

---

# Evenements (1/2)

- **Initialize**
  - Setxxx, Addxxx, ajout de handlers (InsightsGenerated etc.)
  - Gestion des dates + Consolidateurs
  - Cash / AddEquities/AddForex etc. (+ resolution) vs SetUniverseSelection
  - SetBrokerageModel, SetPortfolioConstruction, SetDataNormalisationMode
- **OnData**
  - Slice => Ticks, TradeBars
  - => dictionaire par symbole
  - Price => close (data, data.Bars, Securities[xx])

---

# Evenements (2/2)

- **OnData (suite)**
  - Decision => Portfolio.Invested, nextEntryTime
  - Ordres: MarketOrder (symbol, calcul), SetHoldings
  - Journalisation: Log
  - Sortie: condition/entryprice – Liquidate
- **OnOrderEvent**
  - Filled, Submitted etc.
- **Autres points d'entree**
  - OnSecuritiesChange, OnEndOfDay, OnBrokerageMessage, OnWarmupFinished etc.
  - Evenements planifies (Schedule)

<!-- Cycle evenementiel : Initialize → [OnData, Schedule] → OnOrderEvent → OnEndOfDay -->

---

# Initialisation - Dates et Monnaies

- **Definition des dates de backtesting**
  - C#
    ```csharp
    this.SetStartDate(2013, 1, 5);
    this.SetEndDate(DateTime.Now.Date.AddDays(-7));
    ```
  - Python
    ```python
    self.SetStartDate(2018, 4, 1)
    self.SetEndDate(datetime.now() - timedelta(7))
    ```
- **Definition des monnaies et montants initiaux**
  - C#: `this.SetAccountCurrency("EUR"); this.SetCash("EUR", 10000);`
  - Python: `self.SetAccountCurrency("BTC"); self.SetCash("EUR", 10000)`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Initialisation - Broker et Securites

- **Choix du Broker et souscription a des securites**
  - C#
    ```csharp
    this.SetBrokerageModel(BrokerageName.Bitstamp, AccountType.Cash);
    var btcSecurity = this.AddCrypto("BTCUSD", Resolution.Daily);
    ```
  - Python
    ```python
    self.SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Cash)
    self.spy = self.AddEquity("SPY", Resolution.Hour, Market.Oanda)
    ```
- **Ajout d'indicateurs**
  - C#: `this.Fast = EMA(_btcusd, FastPeriod); this.Slow = EMA(_btcusd, SlowPeriod);`
  - Python: `self.fast = self.EMA(symbol, 30, Resolution.Minute); self.slow = self.EMA(symbol, 60, Resolution.Minute)`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Initialisation - Warmup

- **Warmup**
  - C# (Timespan)
    ```csharp
    this.SetWarmUp(TimeSpan.FromDays(150));
    ```
  - Python (nb barres)
    ```python
    self.SetWarmUp(200)
    ```
- **Possibilite de Warmup automatique**
  - `AutomaticIndicatorWarmUp = True`
  - `self.Settings.AutomaticIndicatorWarmUp = True`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Initialisation - Evenements Planifies

- **Evenements planifies**
  - C#
    ```csharp
    Schedule.On(DateRules.EveryDay(),
                TimeRules.Every(TimeSpan.FromDays(1)),
                this.ExampleFunc);
    ```
  - Python
    ```python
    self.Schedule.On(self.DateRules.EveryDay(),
                     self.TimeRules.Every(timedelta(minutes=10)),
                     self.ExampleFunc)
    ```

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Initialisation - Consolidation et Graphiques

- **Consolidation de barres**
  - C#: `this._consolidator = Consolidate(_symbol, TimeSpan.FromMinutes(10), ConsolidationHandler);`
  - Python: `self.consolidator = self.Consolidate(self.symbol, timedelta(minutes=10), self.consolidation_handler)`
- **Creations de graphiques**
  - C#
    ```csharp
    var stockPlot = new Chart(_ChartName);
    var assetPrice = new Series(_PriceSeriesName, SeriesType.Line, "$", Color.Blue);
    stockPlot.AddSeries(assetPrice);
    This.AddChart(stockPlot);
    ```
  - Python
    ```python
    stockPlot = Chart("Trade Plot")
    stockPlot.AddSeries(Series("Price", SeriesType.Line, 0))
    self.AddChart(stockPlot)
    ```

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Evenements de Données

- **Temps decoupe en "slices"**
  - Peuvent contenir des Ticks (ponctuel) ou TradeBars, QuoteBars (périodes)
- **Methode principale**
  - C#
    ```csharp
    public override void OnData(Slice slice)
    {
        var data = slice[_symbol];
    }
    ```
  - Python
    ```python
    def OnData(self, slice: Slice) -> None:
        data = slice[self.symbol]
    ```
- **Alternative: "CurrentSlice"**
  - Dans un evenement planifie

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Journalisation et Graphiques

- **Journalisation**
  - Methodes Log ou Debug
  - Exemple crypto:
    ```csharp
    Debug($"Time: {data.Time.ToShortDateString()}, Price: @{data.Bars[_btcusd].Close}$/Btc;
           Portfolio: {Portfolio.CashBook[Portfolio.CashBook.AccountCurrency].Amount}$,
           {Portfolio[_btcusd].Quantity}BTCs,
           Total Value: {Portfolio.TotalPortfolioValue}$,
           Total Fees: {Portfolio.TotalFees}$");
    ```
  - Logs enregistres dans backtest: Eviter de les surcharger pour eviter la saturation
- **Export de graphiques**
  - Methode Plot (cf initialisation)
- **Utilisation de données historiques**
  - Python: `self.df = self.History(self.Symbol("SPY"), start_time, end_time, Resolution.Hour)`
  - Plusieurs symbols: `self.dataframe = self.History([self.Symbol("IBM"), self.Symbol("AAPL")], start_time, end_time)`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->
<!-- Graphique backtest : equity curve, drawdown, benchmark overlay -->

---

# Gestion Explicite des Ordres (1/2)

- **Types**
  - Market, Limit, StopMarket, StopLimit, MarketOnOpenOrder, MarketOnCloseOrder etc.
- **Exemples**
  - C#: `var orderTicket = this.StopMarketOrder("IBM", 10, price / 0.1m);`
  - Python: `marketOrderTicket = self.LimitOrder("SPY", 100, 21.67)`
- **Type de retour: OrderTicket**
  - Permet de suivre l'ordre (Status, QuatityFilled etc.)
  - Possibilite de faire des MAJ chez certains Brokers
  - Classe UpdateOrderFields, methode ticket.Update

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Gestion Explicite des Ordres (2/2)

- **Methode OnOrderEvent**
  - C#: `public override void OnOrderEvent(OrderEvent orderEvent)`
  - Python: `def OnOrderEvent(self, orderEvent: OrderEvent) -> None:`
- **Annulation**
  - Methode ticket.Cancel("message") ou request = ticket.CancelOrderRequest()

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Gestion des Ordres par Dimensionnement (1/2)

- **Dimensionnement de position**
  - Ponderer la valeur des actifs du portefeuille
- **Exemples**
  - C# (version simple): `this.SetHoldings("IBM", 0.5);`
  - Python (tous les parametres): `self.SetHoldings(symbol, weight, liquidate_existing_holdings, tag, order_properties)`
- **Possibilite de definir plusieurs cibles d'actifs simultanement**
  - `self.SetHoldings([PortfolioTarget("SPY", 0.8), PortfolioTarget("IBM", 0.2)], True)`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Gestion des Ordres par Dimensionnement (2/2)

- **Calcul des quantites tenant compte des frais**
  - `var quantity = CalculateOrderQuantity("IBM", 0.4);`
- **Existence d'un Buffer (slippage)**
  - 2,5% par defaut
  - Personalisation:
    - `Settings.FreePortfolioValuePercentage = 0.05m;` (pourcentage)
    - `self.Settings.FreePortfolioValue = 10000` (Valeur absolue)
- **Liquidation**
  - C# (un actif): `Liquidate("AAPL", "Liquidated");`
  - Python (toutes les positions): `order_ids = self.Liquidate()`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Notebooks de Recherche

- **Research Environnement**
  - Environnement d'exploration facilitant l'iteration
  - Jupyter / Python
  - .Net Interactive / C#
- **Workflow**
  - Hypothese / Edge → Research → Strategy → Backtests/Optimisation → Paper/Live trading
- **Kernel dedie**
  - Execution QC en ligne
  - Execution sous container Docker / lean-cli
- **QuantBooks**
  - Classe heritant de QCAlgorithm
  - Utilisation de données historisees / dataframes pour analyse

<!-- QuantBook : notebook Jupyter pour exploration de données historiques -->
<!-- Workflow : Research (QuantBook) → Backtest (QCAlgorithm) → Paper Trading → Live -->

---

# Framework de Haut Niveau

- **Ensemble de modules de haut niveau**
  - Universe Selection: Choix des instruments disponible
  - Alpha Creation: Construction de signaux (insights)
  - Portfolio construction: construction et maintenance du portefeuille (targets)
  - Risk management (minimization de risque)
  - Execution (immediate ou optimisee)
- **Abstractions facilitant la gestion de portefeuille**
  - Utilisable en combinaison avec des primitives de bas niveau
  - (Alpha, PortfolioConstruction, Risk, Execution) peuvent etre utilises individuellement ou combines

<!-- Pipeline : Universe Selection → Alpha Model → Portfolio Construction → Risk Management → Execution -->

---

# Selection d'Univers

- **Un univers definit les actifs disponibles pour le portefeuille**
- **Selection manuelle**
  - `AddUniverseSelection(new ManualUniverseSelectionModel(symbols));`
- **Selection parametrique ou planifiee**
  - Ex: EmaCrossUniverseSelectionModel
  - Selectionne les actifs d'un ensemble en retournement haussier le plus fort
- **Combinaisons d'univers possible**
- **Methode OnSecurityChanged quand des actifs sont rajoutes ou enleves**
  - C#: `public override void OnSecuritiesChanged(SecurityChanges changes)`
  - Python: `def OnSecuritiesChanged(self, algorithm: QCAlgorithm, changes: SecurityChanges) -> None:`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Alphas (1/2)

- **Classes chargees de générer des signaux**
  - = Insights (direction, amplitude et confiance)
  - e.g. A partir d'indicateurs
- **Ajout a l'initialisation**
  - `self.AddAlpha(RsiAlphaModel())`
- **Alphas par defaut**
  - ConstantAlphaModel, HistoricalReturnsAlphaModel, EmaCrossAlphaModel, MacdAlphaModel, RsiAlphaModel
  - BasePairsTradingAlphaModel, PearsonCorrelationPairsTradingAlphaModel etc.

---

# Alphas (2/2)

- **Alpha personnalise**
  - Python: classe + initialisation + creation d'insights
    ```python
    class MyAlphaModel(AlphaModel):
        def OnSecuritiesChanged(self, algorithm: QCAlgorithm, changes: SecurityChanges) -> None:
            pass
        def Update(self, algorithm: QCAlgorithm, data: Slice) -> List[Insight]:
            pass
    ```
  - C#
    ```csharp
    class MyAlphaModel : AlphaModel
    {
        public override IEnumerable<Insight> Update(QCAlgorithm algorithm, Slice data)
        public override void OnSecuritiesChanged(QCAlgorithm algorithm, SecurityChanges changes)
    }
    ```

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Insights

- **Definit les signaux retournes par la methode Update des Alphas**
- **Exemples**
  - Python: `insight = Insight.Price("IBM", timedelta(minutes = 20), InsightDirection.Up)`
  - C#: `var insight = Insight.Price("IBM", TimeSpan.FromMinutes(20), InsightDirection.Up);`
- **Caractéristiques**
  - Parametres importants: Direction, Period, Magnitude, Confidence, Weight
  - Possibilite de les regrouper: `return Insight.Group([insight1, insight2, insight3])`
  - Possibilite de les annuler: `self.insight.Cancel(algorithm.UtcTime)`
- **Si pas de référence utilisation de l'insight manager**
  - Filtrage par symbole, par direction etc.
  - `var insights = algorithm.Insights.GetInsights(insight => insight.Direction == InsightDirection.Up);`
  - `algorithm.Insights.Cancel(symbols)`

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Construction de Portefeuille (1/2)

- **Modele de construction de portefeuille**
  - Creee des "targets" qui se traduisent par des ordres
- **Exemples**
  - Python: `self.SetPortfolioConstruction(EqualWeightingPortfolioConstructionModel())`
  - C#: `SetPortfolioConstruction(new EqualWeightingPortfolioConstructionModel());`
- **Modeles fournis par defaut**
  - EqualWeightingPortfolioConstructionModel: Poids egal entre les actifs avec Insights
  - ConfidenceWeightedPortfolioConstructionModel: Ponderation par la confiance de l'insight
  - InsightWeightingPortfolioConstructionModel: Ponderation par poids de l'insight

---

# Construction de Portefeuille (2/2)

- **Modeles fournis par defaut (suite)**
  - SectorWeightingPortfolioConstructionModel: Ponderation par secteur industriel
  - AccumulativeInsightPortfolioConstructionModel: Compte les insights par symbole et direction
  - MeanVarianceOptimizationPortfolioConstructionModel: Minimise la volatilite
  - BlackLittermanOptimizationPortfolioConstructionModel: Utilise un optimiseur
  - MeanReversionPortfolioConstructionModel: Retour a la moyenne
  - RiskParityPortfolioConstructionModel: Minimisation du risque
- **Optimiseurs fournis**
  - MaximumSharpeRatioPortfolioOptimizer, MinimumVariancePortfolioOptimizer
  - UnconstrainedMeanVariancePortfolioOptimizer, RiskParityPortfolioOptimizer

---

# Gestion du Risque

- **Objectif: gestion du risque des cibles**
  - Renvoyees par le gestionnaire de portefeuille
  - Idealement, doit etre integre des la conception, pas apres optimisation
  - Sinon, souvent performances degradees
- **Definition**
  - C#: `this.AddRiskManagement(new MaximumDrawdownPercentPerSecurity());`
  - Python: `self.AddRiskManagement(MaximumSectorExposureRiskManagementModel())`
- **Modeles fournis par defaut**
  - MaximumDrawdownPercentPerSecurity, MaximumDrawdownPercentPortfolio
  - MaximumUnrealizedProfitPercentPerSecurity
  - MaximumSectorExposureRiskManagementModel, TrailingStopRiskManagementModel

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Modeles d'Execution

- **Determine comment les ordres sont executes**
- **Definition**
  - C#: `this.SetExecution(new ImmediateExecutionModel());`
  - Python: `self.SetExecution(ImmediateExecutionModel())`
- **Modeles fournis**
  - ImmediateExecutionModel
  - SpreadExecutionModel (Necessite des QuoteBars)
  - StandardDeviationExecutionModel
  - VolumeWeightedAveragePriceExecutionModel

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->

---

# Optimisation de Parametres (1/2)

- **Definition de parametres d'algorithmes**
  - Appel explicite
    ```python
    fast_period = self.GetParameter("ema-fast", 100)
    self.fast = self.EMA("SPY", fast_period)
    ```
  - Exemple Python: ParameterizedAlgorithm.py
  - Utilisation d'attributs
    ```csharp
    [Parameter("ema-fast")]
    public int FastPeriod = 18;
    ```
- **Configuration dynamique**
  - Fichier config.json
  - Interface en ligne dediee / UI similaire dans l'extension vscode

<!-- Code : voir notebooks QuantConnect/ pour exemples executables -->
<!-- Interface optimisation : grille de parametres, bouton lancement, resultats tabulaires -->

---

# Optimisation de Parametres (2/2)

- **Lanceur d'Optimisation**
  - Execute une serie de backtests
  - Dans l'objectif de trouver la meilleure combinaison des parametres
  - Pour optimiser une mesure (e.g. ratio de Sharpe)
- **Environnement**
  - QuantConnect: bouton et Formulaire de parametrage (Utilisation de credits dans le cloud)
  - Lean-cli: Commande dediee
  - Lean: QuantConnect.Optimizer.Launcher
- **Bon usage**
  - Attention a la combinatoire (Produit cartesien de toutes les possibilites voire + pour Euler)
  - Utilisation d'une version d'algo "rapide" (test manuel de sensibilite a la resolution)
  - Attention au sur-apprentissage (Optimisation sur une période donnee, validation finale sur une période + recente)

<!-- Heatmap optimisation : axes = parametres, couleur = Sharpe ratio ou rendement -->

---

# Optimisation de Parametres - Configuration (1/2)

- **Configuration**
  - Designation de l'algo C# ou Python identique: "algorithm-type-name", etc.
  - A priori pas de debug, au besoin utiliser la journalisation
- **Designation des parametres a optimiser**
  - parameters: name, min, max, step
- **2 stratégies d'exploration**
  - GridSearch: teste toutes les combinaisons
  - EulerSearch: teste toutes les combinaisons, puis raffine a partir de la meilleure
  - Parametres supplementaires pour la subdivision des steps initiaux: min-step, default-segment-amount

---

# Optimisation de Parametres - Configuration (2/2)

- **Definition des objectifs**
  - Parametre optimization-criterion a optimiser
  - Parametre target a maximiser ou minimiser (extremum)
  - Cf class PerformanceMetrics
  - Cible a atteindre target-value (Permet d'arreter l'optimisation de facon prematuree)
- **Ajout de contraintes**
  - Parametres target, operator, target-value
  - Permet de disqualifier certaines configurations (risque trop eleve)

---

<!-- _class: questions -->

# Questions?

---

# Machine Learning pour le Trading (1/2)

![bg right:30%](images/lstm_cell.png)

- **Prediction de Series temporelles**
  - Regression: Prediction du prix
  - Classification: Prediction de la tendance (trend haussier, baissier, neutre)
  - Detection d'anomalie
- **Évolution des architectures**
  - RNN (LSTM)
  - Transformers
  - CNN
  - Diffusion

---

# Machine Learning pour le Trading (2/2)

- **Retours sur le trading**
  - Marche en constante évolution (modèles MAJ)
  - Regression difficile / pas tres adaptee
  - Modeles de classification boostes relativement efficaces

<!-- LSTM : input sequence → cellules LSTM → dense → prediction prix/direction -->
<!-- Predictions vs actuel : courbe de prix reelle vs predictions du modèle -->

---

# Difficultes du ML dans le Trading (1/2)

![bg right:25%](images/rnn_unrolled.png)

- **Non stationnarite**
  - Different des Times series classiques
  - Changements continuels dans les distributions de données
  - Pire que ca: adversarial
  - Le marche s'adapte, changement de regimes intentionnels
  - Necessite de beaucoup de feedback, attention aux modèles statiques
- **Identification de regimes distincts**
  - Duree des transitions assez lente / difficile a detecter
  - Detection d'anomalie difficile
  - Emprise du regime localisee / globale
  - Intensite des changements des regimes

---

# Difficultes du ML dans le Trading (2/2)

- **Données inadequates**
  - Ratio signal / bruit mauvais
  - Granularite variable des données (e.g. rapports trimestriels)
  - Données insuffisantes / overfitting
  - Importance d'un pipeline de reentrainement continu

<!-- Signal/bruit : series financieres dominee par le bruit, signal faible et non-stationnaire -->

---

# ML en .Net

- **ML.Net** https://github.com/dotnet/machinelearning
  - Classification, Regression, Deep-learning, ONNX
- **Tensorflow.Net** https://medium.com/@mariusmuntean/operationalize-tensorflow-models-with-ml-net-8b7389628d70
- **TorchSharp** https://github.com/dotnet/TorchSharp
  - Similaire a Pytorch (Bridge), Base de Autodiff.Net
- **Infer**
  - Programmation probabiliste
  - https://dotnet.github.io/infer/default.html
  - https://www.mbmlbook.com/toc.html
- **AutoML**
  - Choix du modèle et hyperparametrisation
  - "experiments" sur differents trainers
- **TimeSeries**

---

# Exemples et Ressources ML.Net

- **Exemples**
  - https://github.com/dotnet/machinelearning-samples/tree/main
  - https://github.com/dotnet/csharp-notebooks/tree/main/machine-learning
- **Accord** http://accord-framework.net/
  - Complet mais obsolete/vieillissant
  - SVM toujours d'actualite
  - Autres algos pris en charge par ML.Net

---

# ML dans Lean/QC (1/2)

- **Exemple Accord SVM**
  - Exemple simpliste
  - Entrainement a la volee
  - A utiliser en combinaison avec d'autres indicateurs/signaux
- **Integration MyIA.Backtesting**
  - Nombreux parametres
  - Entrainement en batch

---

# ML dans Lean/QC (2/2)

- **Types de modèles**
  - Accord SVM: Type de noyau + complexité
  - ML.Net AutoML: Classification, metrique d'optimisation
  - A venir: prediction: modèle regressif
- **Integration Lean dans une branche dediee**
- **Nouveaux exemples QC**
  - https://www.quantconnect.com/docs/v2/writing-algorithms/machine-learning/key-concepts

<!-- ML dans Lean : integration ML.Net/ONNX dans QCAlgorithm -->
<!-- Features importance : classement des variables predictives par gain d'information -->
<!-- Learning curves : train loss decroissant, validation loss en U (overfitting) -->

---

<!-- _class: questions -->

# Questions?

---

# Pour aller plus loin : Notebooks

**Notebooks QuantConnect (~27 notebooks disponibles)**
- Strategies de base: `QuantConnect/BasicTemplateAlgorithm.ipynb`
- Moyennes mobiles: `QuantConnect/MovingAverageCrossover.ipynb`
- RSI Strategy: `QuantConnect/RSIStrategy.ipynb`
- Mean Reversion: `QuantConnect/MeanReversion.ipynb`
- Backtesting: `QuantConnect/BacktestAnalysis.ipynb`
- Optimisation: `QuantConnect/ParameterOptimization.ipynb`
- LSTM pour prediction: `QuantConnect/LSTM-Prediction.ipynb`
- Reinforcement Learning: `QuantConnect/ReinforcementLearning.ipynb`

**Autres notebooks pertinents**
- Optimisation de portefeuille: `Search/Portfolio_Optimization_GeneticSharp.ipynb`
- Modeles probabilistes pour le risque: `Probas/`

---

<!-- _class: title -->

# Merci

Jean-Sylvain Boige
jsboige@myia.org

> **Notebooks associes:** `QuantConnect/` (~27 notebooks)
> Strategies de trading, backtesting, optimisation, machine learning
