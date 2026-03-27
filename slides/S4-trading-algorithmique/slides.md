---
theme: ../theme-ia101
title: "S4 Trading Algorithmique"
info: Cours Intelligence Artificielle - Trading Algorithmique
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Trading Algorithmique

Intelligence Artificielle -- S4

**Trading automatise et IA pour les marches financiers**

- Comprendre les fondamentaux du trading algorithmique
- Apprendre a utiliser Lean/QuantConnect
- Concevoir et implementer un algorithme de trading
- Evaluer et optimiser une strategie algorithmique
- Maitriser le traitement de donnees et l'IA pour le trading

---

# Plan du Cours - Partie 1: Fondamentaux

- Introduction au trading algorithmique
  - Definition, profil du trader algorithmique
  - Types de trading (HFT, MFT, LFT)
<div v-click="1">

- Marches financiers et instruments
  - Actions, Forex, Futures, Cryptomonnaies
</div>
<div v-click="2">

- Ordres de trading
  - Types d'ordres, instructions, gestion de la visibilite
</div>
<div v-click="3">

- Trouver et evaluer une strategie
  - Sources d'idees, metriques de performance
</div>

---

# Plan du Cours - Partie 2: Strategies et Pratique

- Strategies de trading
  - Moyenne reversion, Momentum, Regime switching
  - Arbitrage, Market making, High-frequency trading
  - Trading saisonnier, Portefeuille a haut levier
<div v-click="1">

- Backtesting et gestion du risque
  - Plateformes, mesures de performance, pieges
  - Formule de Kelly, stop loss, risques
</div>
<div v-click="2">

- Lean/QuantConnect
  - Installation, environnement, framework
  - Machine learning pour le trading
</div>

---

# Qu'est-ce que le Trading Algorithmique?

- **Definition**
  - Achat et vente d'actifs financiers pilotes par des algorithmes
  - Elimination des biais emotionnels dans la prise de decision

<div v-click="1">

- **Methodes d'analyse**
  - Analyse technique (indicateurs, patterns graphiques)
  - Donnees fondamentales (revenus, indicateurs macroeconomiques)
  - Donnees extra-financieres (flux d'actualites, sentiment du marche)

</div>
<div v-click="2">

- **Universalite**
  - Tout ce qui est numerisable peut etre utilise en trading quantitatif
  - Diversification facilitee sur plusieurs strategies simultanees

</div>
---
layout: dense
---
# Profil du Trader Algorithmique

- **Formation et diplome**
  - Pas necessairement un diplome avance
  - Origines variees: sciences physiques, ingenierie, informatique

<div v-click="1">

- **Competences requises**
  - Mathematiques, statistiques et programmation
  - Comprehension des marches financiers
  - Curiosite et capacite d'apprentissage continu

</div>
<div v-click="2">

- **Experience pratique**
  - Finance et programmation cruciales
  - Avoir des economies pour les periodes sans gains
  - Importance de la discipline et de la gestion du stress

</div>
---
layout: dense
---
# Avantages du Trading Algorithmique

- **Scalabilite**
  - Augmenter les volumes sans effort supplementaire
  - Gerer plusieurs strategies en parallele, sur differents marches
  - Passage a l'echelle impossible en trading manuel
<div v-click="1">

- **Optimisation du temps**
  - Automatisation des taches repetitives (screening, execution)
  - Plus de temps pour la recherche et l'amelioration des modeles
  - Execution 24/7 sur les marches crypto et forex
</div>
<div v-click="2">

- **Elimination des biais emotionnels**
  - Pas de peur, de cupidite ou d'hesitation
  - Execution disciplinee selon des regles predefinies
  - Resultats reproductibles et mesurables
</div>
<div v-click="3">

- **Autonomie et independance**
  - Pas besoin de clients ni de mandats de gestion
  - Focus sur la performance pure du modele
  - Possibilite de demarrer avec un capital modeste
</div>
---

# Types de Trading Algorithmique (1/2)

- **HFT (High-Frequency Trading)**
  - Operations en millisecondes ou microsecondes
  - Objectif: Exploiter de petites inefficacites du marche
  - Technologie: Necessite une infrastructure technologique de pointe

<div v-click="1">

- **MFT (Medium-Frequency Trading)**
  - Operations sur des secondes, minutes a quelques heures
  - Objectif: Arbitrage, suivi de tendance, et autres strategies
  - Flexibilite: Moins exigeant technologiquement mais necessite une analyse de donnees robuste

</div>
---

# Types de Trading Algorithmique (2/2)

- **LFT (Low-Frequency Trading)**
  - Operations sur des jours, semaines ou mois
  - Objectif: Investissement base sur des facteurs fondamentaux ou des indicateurs techniques
  - Gestion du Risque: Focalisation sur la reduction du risque a long terme

<div v-click="1">

- **Chaque type a ses specificites**
  - Avantages et inconvenients propres
  - Necessite des competences, des infrastructures et des ressources differentes
  - Offre des opportunites de rendement variables

</div>
---
layout: section
---

# Questions?

---

# Vue d'ensemble du Marche

- **Marches Principaux**
  - Actions, Forex, Futures, Cryptomonnaies
<div v-click="1">

- **Roles des Participants**
  - Traders particuliers, institutionnels, market makers, arbitragistes
  - Fournisseurs de liquidite, preneurs de liquidite

</div>
<div v-click="2">

- **Reglementations**
  - MiFID II en Europe
  - Dodd-Frank aux Etats-Unis

</div>
<div v-click="3">

- **Importance des Donnees**
  - Tickers, Order Book, Volume, Time & Sales
  - Impact de la qualite et de la frequence (temps reel vs resolution)

</div>
---
layout: image-overlay
image: ./images/candlestick_patterns.png
imageClass: mid-right
---
layout: dense
---
# Instruments Financiers

- **Actions**
  - Titres qui representent une fraction de la propriete d'une entreprise
<div v-click="1">

- **Forex**
  - Echange de devises etrangeres, souvent a des fins de speculation ou de couverture
</div>
<div v-click="2">

- **Futures**
  - Contrats qui obligent a acheter ou vendre un actif a un prix fixe a une date future

</div>
<div v-click="3">

- **Cryptomonnaies**
  - Monnaies numeriques qui utilisent la cryptographie pour securiser les transactions
  - Aspects reglementaires variables
</div>
<div v-click="4">

- **Classes d'actifs**
  - Categories d'investissement (actions, obligations, matieres premieres)
  - Diversification du risque

</div>
---
layout: image-overlay
image: ./images/candlestick_anatomy.png
imageClass: mid-right
---
layout: dense
---
# Analyse Technique et Fondamentale

- **Analyse Technique**
  - Etude des graphiques de prix et de volume
  - Indicateurs: moyennes mobiles, RSI, MACD, Bollinger Bands
  - Patterns graphiques: chandeliers, tete-epaules, triangles

<div v-click="1">

- **Analyse Fondamentale**
  - Evaluation de la valeur intrinseque d'un actif
  - Donnees financieres: revenus, benefices, ratios
  - Indicateurs macroeconomiques: taux d'interet, inflation, PIB

</div>
<div v-click="2">

- **Combinaison des deux approches**
  - Analyse technique pour le timing d'entree/sortie
  - Analyse fondamentale pour la selection d'actifs

</div>
---
layout: dense
---
# Infrastructure de Trading

- **Plateformes et Courtiers**
  - Interactive Brokers, MetaTrader, Robinhood
<div v-click="1">

- **API de Trading**
  - Interface de programmation permettant l'automatisation des ordres
  - FIX, REST APIs, WebSocket

</div>
<div v-click="2">

- **Flux de Donnees**
  - Fournit des informations en temps reel ou differe sur les marches
  - Certaines plateformes offrent des flux combines

</div>
<div v-click="3">

- **Latence et Couts**
  - Delais d'execution: Temps entre la soumission et l'execution d'un ordre
  - Couts de transaction: Frais associes a l'achat et a la vente d'actifs
</div>
<div v-click="4">

- **Exigence d'Infrastructure**
  - Serveurs co-localises, GPUs pour ML

</div>
---

# Les Ordres de Trading - Types d'Ordres (1/2)

- **Les ordres sont cruciaux pour toute strategie de trading**
<div v-click="1">

- **Ordres au marche**
  - Execution: Immediate au meilleur prix
  - Risque: Prix d'execution incertain
  - Impact: Peut affecter significativement le marche

</div>
<div v-click="2">

- **Ordres a cours limite**
  - Controle: Prix limite pour l'achat/vente
  - Flexibilite: Utilisation aggressive ou passive
  - Risque: Execution incertaine

</div>
---

# Les Ordres de Trading - Types d'Ordres (2/2)

- **Ordres conditionnels et hybrides**
  - Complexite: Inclut des ordres caches, routes
  - Utilite: Pour des strategies plus avancees
<div v-click="1">

- **Ordres stop**
  - Declenchent un ordre au marche ou limite une fois qu'un prix predefini est atteint

</div>
<div v-click="2">

- **Choix du type d'ordre**
  - Depend du besoin d'immediateté et du controle du prix
  - Ordres au marche sont rapides mais incertains en prix
  - Ordres a cours limite offrent plus de controle mais moins de certitude
</div>
<div v-click="3">

- **Impact du mode d'execution**
  - Bourse centrale vs. Dark pools

</div>
---

# Ordres - Instructions Optionnelles (1/2)

- **Les instructions optionnelles offrent plus de controle sur vos ordres**
<div v-click="1">

- **Instructions de Duree: "Good 'til"**
  - GTD: Actif jusqu'a une date donnee
  - GTC: Actif jusqu'a annulation
  - GAT: Actif a un moment donne

</div>
<div v-click="2">

- **Instructions d'Encheres**
  - On-open: Pour enchere d'ouverture
  - On-close: Pour enchere de cloture
  - Next-auction: Pour prochaine enchere valide

</div>
---

# Ordres - Instructions Optionnelles (2/2)

- **Instructions de Remplissage**
  - IOC: Execution ou annulation immediate
  - FOK: Fill-or-Kill: Execution totale immediate ou annulation
  - AON: All-or-None: Execution totale requise
  - Minimum-Volume: Volume minimum requis

<div v-click="1">

- **Importance pour l'efficacite**
  - Comprendre ces instructions ameliore l'efficacite de trading
  - Permettent d'adapter vos ordres a differentes situations de marche

</div>
---

# Ordres - Instructions Specifiques (1/2)

- **Ordres Must-Be-Filled (MBF)**
  - Execution Totale: Doivent etre executes en totalite
  - Interruption de volatilite: Declenche une interruption si non execute
  - Session de Trading Separee: Session speciale pour ces ordres

<div v-click="1">

- **Preferencement et Instructions Dirigees**
  - Trading Bilateral: Direction vers un courtier specifique
  - On parle d'internalisation
  - Controverse: Contournent les regles de priorite
  - Amelioration de Prix: Mecanismes speciaux pour ameliorer le prix

</div>
---
layout: dense
---
# Ordres - Instructions Specifiques (2/2)

- **Instructions de Routage**
  - Do-Not-Route: Execution locale uniquement
  - Directed-Routing: Routage vers un marche specifique

<div v-click="1">

- **Inter-Market Sweeps**
  - Balayage: Balaye le carnet d'ordres sur un marche donne

</div>
<div v-click="2">

- **Instructions de Liaison**
  - One-Cancels-Other (OCO): Deux ordres sont mutuellement exclusifs
  - One-Triggers-Other (OTO): Un ordre declenche un autre ordre

</div>
<div v-click="3">

- **Instructions Diverses**
  - Anonymat: Certains marches offrent l'anonymat
  - Ventes a Decouvert: Drapeau requis sur certains marches
  - Lots Impairs: Appariement de lots ronds avec lots impairs

</div>
---

# Types d'Ordres bases sur des Conditions

- **Ordres a seuil de declenchement suiveur (Trailing Stop)**
  - Verrouillage des prix: S'adapte au marche
  - Flexibilite: Maximise les gains sans predire le stop
  - Ex: Stop de vente a -5% dont le seuil remonte avec le cours

<div v-click="1">

- **Ordres conditionnels / Si touche**
  - Logique d'activation: Cache jusqu'a un niveau de prix
  - Polyvalence: Bases sur le prix d'autres actifs

</div>
<div v-click="2">

- **Ordres sensibles au tick**
  - Dependance au tick: Execute si le dernier prix repond a des conditions
  - Impact sur le marche: Minimise pour un meilleur prix

</div>
---

# Types d'Ordres - Gestion de la Visibilite (1/2)

- **Types d'ordres caches**
  - Ordres Iceberg
  - Partie visible et cachee
  - Frequents sur les marches a forte liquidite (actions, futures)
  - Priorite: Plus basse que les ordres visibles

<div v-click="1">

- **Types d'ordres discretionnaires**
  - Ordres non tenus
  - Trader decide de l'execution
  - Evolution: Plus basees sur des regles

</div>
---

# Types d'Ordres - Gestion de la Visibilite (2/2)

- **Ordres ajustes (Pegged)**
  - Prix dynamique: Suivre la meilleure offre ou demande

<div v-click="1">

- **Ordres achemines (Routed)**
  - Strategies complexes: Routage vers differents lieux
  - Smart Order Routing: Strategies complexes
  - Ex: Interactive Brokers SmartRouting
  - Permet d'eviter le slippage ou optimise l'execution

</div>
---

# Autres Types d'Ordres - Specialises

- **Ordres de croisement**
  - Types varies: Committed, Uncommitted, etc.
  - Mecanismes varies: Differents reseaux de croisement
<div v-click="1">

- **Ordres non engages**
  - Similaires aux IOIs: Besoin de confirmation
  - Protection: Tailles minimales, etc.

</div>
<div v-click="2">

- **Ordres negocies**
  - Mecanisme bilateral: Environnement de negociation
  - Anonymat: Entre investisseurs ou fournisseurs de liquidite
</div>
<div v-click="3">

- **Alertes Automatisees**
  - Notification aux PLPs: Exemple de Millennium ATS

</div>
---

# Order-Contingent et Implied Orders

- **Order-Contingent Order Types**
  - Ordres Lies-Alternatifs: Liste d'ordres alternatifs
  - Ordres Contingents: Ajustent prix et taille

<div v-click="1">

- **Implied Orders**
  - Ordres Implicites: Ajustent prix et taille
  - Importance: Liquidite supplementaire en marche a terme

</div>
---
layout: section
---

# Questions?

---

# Trouver une Strategie qui vous Convient (1/2)

- **Sources d'Idees**
  - Articles academiques, blogs, forums, medias
  - Suivi des meilleures strategies sur plateformes
<div v-click="1">

- **Modification de Strategies**
  - Ajustements pour rentabilite

</div>
<div v-click="2">

- **Echange d'idees**
  - Blogs de trading pour partage
</div>
<div v-click="3">

- **Strategies qui vous conviennent**
  - Temps disponible: Temps complet vs temps partiel
  - Academiques vs. Publiques: Complexite vs simplicite
  - Competences en programmation: Elargit les options

</div>
---

# Trouver une Strategie qui vous Convient (2/2)

- **Votre Capital de Trading**
  - Ancien minimum conseille de 50 000 $
  - Nouveaux minima grace aux cryptos et frais reduits

<div v-click="1">

- **Votre Objectif**
  - Revenu regulier vs gains en capital

</div>
---

# Comment Evaluer une Strategie?

- **Mesures Standard**
  - Ratio de Sharpe: Mesure le rendement ajuste au risque
  - High Watermark: Rendement cumule maximal a un moment donne
  - Drawdown Maximum et Duree: La plus grande baisse et le temps pour recuperer

<div v-click="1">

- **Criteres de performance**
  - Rendement annualise
  - Volatilite des rendements
  - Ratio gain/perte moyen
  - Taux de reussite des trades

</div>
---

# Strategies Plausibles et leurs Pieges (1/2)

- **Drawdowns**
  - Perte de valeur, profondeur et duree a evaluer
<div v-click="1">

- **Slippage**
  - Ecart de prix entre ordre et execution

</div>
<div v-click="2">

- **Couts de Transaction**
  - Impact sur les strategies a haute frequence
</div>
<div v-click="3">

- **Evolution du Marche**
  - Efficacite moindre qu'il y a 10 ans
  - Les marches sont plus efficients

</div>
---

# Strategies Plausibles et leurs Pieges (2/2)

- **Changements de Regime**
  - Donnees historiques parfois non pertinentes

<div v-click="1">

- **Overfitting**
  - Surajustement aux donnees historiques

</div>
<div v-click="2">

- **Frais de financements**
  - Pour les positions a marge

</div>
---

# Intelligence Artificielle et Selection de Stocks

- **Scepticisme initial sur l'IA**
  - Tendance a surajuster les donnees
<div v-click="1">

- **Pratiques qui fonctionnent en IA**
  - Modeles simples, fondements econometriques
  - Mixture d'experts

</div>
<div v-click="2">

- **Strategies "Sous le Radar"**
  - Faible capacite
  - Moins d'arbitrage par grands fonds
</div>
<div v-click="3">

- **Avancees recentes**
  - "Guerre" des modeles
  - Theorie des jeux

</div>
---
layout: section
---

# Questions?

---

# Backtesting (1/2)

- **Qu'est-ce que c'est?**
  - Evaluation d'une strategie d'investissement sur des donnees historiques
<div v-click="1">

- **Pourquoi c'est important**
  - Valider l'efficacite de la recherche originale
  - Experimenter avec des variations pour l'optimiser

</div>
<div v-click="2">

- **Sources de Donnees**
  - Recherche web pour des bases gratuites ou peu couteuses
  - Yahoo Finance, Alpha Vantage, Interactive Brokers, Binance

</div>
---

# Backtesting (2/2)

- **Pieges et Problemes**
  - Donnees ajustees pour les splits et les dividendes: Risque de faux signaux
  - Biais de survie: Surevaluation potentielle des performances
<div v-click="1">

- **Dans le cas ou le Machine Learning est utilise**
  - Le backtesting doit prendre en compte les biais de selection de donnees
  - Separer convenablement les ensembles (training, validation, test)
  - Evaluer la generalisation

</div>
---

# Plateformes de Backtesting (1/2)

- **Excel**
  - Toutes les donnees sont visibles, ce qui reduit le risque de "look-ahead bias"
  - Utilise a la fois pour le backtesting et le trading en direct
  - Inconvenients: Limite aux modeles simples d'investissement

<div v-click="1">

- **MATLAB**
  - Utilise en institutionnel, excellent pour tester des strategies sur de grands portefeuilles
  - Modules statistiques avances
  - Inconvenients: Couteux et moins efficace pour executer les trades

</div>
---

# Plateformes de Backtesting (2/2)

- **TradeStation et autres plateformes**
  - Execution des trades possible directement depuis la plateforme
  - Donnees historiques integrees
  - Inconvenients: Langage proprietaire, vous attache a TradeStation comme courtier

<div v-click="1">

- **Evolution des Plateformes**
  - Python & R: Ont pris le relais de MATLAB dans la plupart des cas
  - Exemple: Zipline et autres frameworks open-source
  - C#: Alternative montante grace aux efforts de Microsoft et Lean

</div>
---

# Lean / QuantConnect

- **Solution open-core en Python et C#**
  - 3 environnements (Lean, Lean-cli-QC)
  - Permettent backtesting, paper trading et live trading
  - Utilisee dans ce cours

<div v-click="1">

- **Avantages**
  - Lean gere nativement les ajustements de donnees (splits, dividendes)
  - Fournit un grand catalogue de donnees alternatives
  - Simplifie l'evaluation point-in-time

</div>
---
layout: image-overlay
image: ./images/efficient_frontier.png
imageClass: mid-right
---

# Mesures de Performance et Pieges (1/2)

- **Mesures Standard**
  - Ratio de Sharpe: Mesure le rendement ajuste au risque, souvent annualise
  - High Watermark: Rendement cumule maximal a un moment donne
  - Drawdown Maximum et Duree: La plus grande baisse et le temps pour recuperer

<div v-click="1">

- **Pieges courants**
  - Look-ahead bias: Utilisation de donnees futures dans le calcul
  - Data-Snooping Bias: Overfitting base sur les donnees historiques
  - Couts de Transaction: Omission des couts associes aux transactions

</div>
---

# Mesures de Performance et Pieges (2/2)

- **Avec Machine Learning**
  - Derive des donnees (data drift)
  - La distribution des donnees evolue dans le temps
  - Rend les patterns historiques obsoletes

---

# Precautions face aux Pieges (1/2)

- **Look-ahead**
  - Utilisation de donnees decalees
  - Forward-testing (paper trading)
<div v-click="1">

- **Data-Snooping Bias**
  - Peu de parametres
  - Augmentation, division et adaptation des donnees de backtest

</div>
<div v-click="2">

- **Modeles de trading sans parametres**
  - Pas de surajustement, fiabilite mais complexite computationnelle

</div>
---
layout: dense
---
layout: dense
---
# Precautions face aux Pieges (2/2)

- **Paper Trading**
  - Test sur des donnees reelles non vues, le plus fiable
<div v-click="1">

- **Analyse de sensibilite**
  - Variation des parametres pour evaluer la stabilite de la performance
</div>
<div v-click="2">

- **Simplification du modele**
  - Elimination des conditions superflues
</div>
<div v-click="3">

- **Repartition du capital de trading**
  - Entre differentes strategies pour diminuer la variance
</div>
<div v-click="4">

- **Couts de Transaction**
  - A integrer dans le Backtest pour des resultats plus realistes
</div>
<div v-click="5">

- **Derive des donnees (data drift) et non stationnarite**
  - Revalider regulierement les modeles
  - Appliquer des techniques comme la differenciation fractionnaire

</div>
---

# Affinement de la Strategie

- **Le Probleme**
  - Rendements diminuent quand une strategie est populaire
<div v-click="1">

- **Solutions**
  - Variations Mineures: Petites variations peuvent ameliorer les rendements
  - Exclusion de Stocks: Eviter certains types d'actions
  - Changement de Timing: Ajuster les points d'entree et de sortie

</div>
---
layout: section
---

# Questions?

---

# Gestion du Risque - Introduction

- **La gestion du risque permet de "preserver" le capital initial tout en optimisant la croissance sur le long terme**
<div v-click="1">

- **Maximisation de la Croissance**
  - Objectif de maximiser la croissance du capital a long terme
  - Rendement Moyen: ( m )
  - Variance des Rendements: ( s^2 )

</div>
<div v-click="2">

- **Eviter la Ruine**
  - Eviter une chute catastrophique du capital a zero
  - Drawdown: Chute maximale du capital sur une periode donnee

</div>
---
layout: image-overlay
image: ./images/normal_distribution.png
imageClass: mid-right
---
layout: dense
---
# Outils et Formules

- **Formule de Kelly**
  - Determine la fraction optimale du capital a risquer par trade
  - f* = (p * b - q) / b
  - p = probabilite de gain, q = probabilite de perte (1-p)
  - b = ratio gain/perte moyen

<div v-click="1">

- **Value-at-Risk (VaR)**
  - Estime la perte maximale potentielle sur une periode
  - Avec un niveau de confiance donne
</div>
<div v-click="2">

- **Conditional Value-at-Risk (CVaR)**
  - Estime la perte moyenne au-dela du VaR
  - Prend en compte les "fat tails"

</div>
---

# Gestion du Risque avec la Formule de Kelly

- **Gestion avec la Formule de Kelly**
  - Reduction de la Taille du Portefeuille: Si les pertes augmentent, reduisez f
<div v-click="1">

- **Contagion Financiere**
  - Le risque de propagation des pertes entre les fonds

</div>
<div v-click="2">

- **Evenements Extremes (Black swans)**
  - Limites de la Formule: Ne prend pas en compte les "fat tails"
  - Gestion des Evenements Imprevus: Utilisation de modeles de Value-at-Risk (VaR)

</div>
<div v-click="3">

- **Utilisation de Stop Loss**
  - Momentum vs Mean-Reverting: L'efficacite varie en fonction du regime du marche
  - Fondamental vs Liquidite: Quand appliquer les stop loss

</div>
---

# Autres Types de Risques

- **Risque de Modele**
  - Biais de survie, biais de lookahead, et erreurs de donnees
  - Changements structurels du marche comme l'impact des nouvelles reglementations

<div v-click="1">

- **Risque Logiciel**
  - Bugs, latence et decalages de donnees
  - Assurez-vous que le systeme de trading automatise est bien teste et surveille

</div>
<div v-click="2">

- **Risques Physiques**
  - Pannes de courant, defaillance du materiel, cyberattaques
  - Solution de secours et plan de recuperation en cas de catastrophe

</div>
---
layout: dense
---
# Preparation Psychologique (1/2)

- **Emotions en Trading**
  - Overtrading en periode de gains
  - Aversion au risque en periode de pertes
  - Importance de suivre scrupuleusement le modele

<div v-click="1">

- **Biais Comportementaux**
  - Effet de dotation
  - Biais du statu quo
  - Aversion a la perte
  - Biais de representativite
  - Comment ces biais affectent la prise de decision en trading

</div>
---

# Preparation Psychologique (2/2)

- **Desespoir et Avidite**
  - Importance de la gestion du stress et de la psychologie
  - Mettre en place des garde-fous pour eviter la prise de decisions impulsives
<div v-click="1">

- **Conseils Pratiques**
  - Commencez petit pour tester votre discipline
  - Avoir un tampon financier ou des sources de revenus alternatives
  - Reduire la pression financiere et psychologique
  - Necessite parfois d'un support psychologique ou d'un coaching (cf. Athletes)

</div>
---
layout: section
---

# Questions?

---
layout: image-overlay
image: ./images/bollinger_bands.png
imageClass: mid-right
---

# Strategies de Moyenne Reversion

- **Moyenne Reversion**
  - Les prix des actions ont tendance a revenir vers une moyenne a long terme
<div v-click="1">

- **Recherche Academique**
  - Proximite a une marche aleatoire
  - Mais certaines conditions permettent la moyenne reversion

</div>
<div v-click="2">

- **Pieges en Backtesting**
  - Biais de Survie: Ignorer les actifs disparus peut fausser les resultats
  - Erreurs de Base de Donnees: Incoherences dans les donnees financieres
</div>
<div v-click="3">

- **Effets de la Concurrence**
  - Reduit les opportunites d'arbitrage, diminuant les rendements

</div>
---
layout: image-overlay
image: ./images/macd_chart.png
imageClass: mid-right
---
layout: dense
---
# Strategies Fondamentales de Momentum

- **Momentum**
  - Tendance d'un actif a continuer a se deplacer dans la meme direction pendant une certaine periode
<div v-click="1">

- **Diffusion Lente de l'Information**
  - Cree des opportunites de momentum

</div>
<div v-click="2">

- **Comportement de Troupeau**
  - Les investisseurs suivent les autres, amplifiant les tendances
</div>
<div v-click="3">

- **Horizons Temporels Imprevisibles**
  - Imprevisibilite de la duree du momentum
</div>
<div v-click="4">

- **Effets de la Concurrence**
  - Accelere l'atteinte de l'equilibre des prix
  - Rend les strategies de momentum moins efficaces a long terme

</div>
---

# Strategies de Regime Switching (1/2)

- **Concept & Types**
  - Les Marches varient entre differents regimes
  - (haussiers/baissiers, inflation/recession, volatilite)
  - La Prediction de ces regimes est un defi
<div v-click="1">

- **Outils & Approches - GARCH**
  - Modele "autoregressif conditionnellement heteroscedastique generalise"
  - Utile pour mesurer la volatilite, moins pour le prix d'actions

</div>
---

# Strategies de Regime Switching (2/2)

- **Modeles probabilistes**
  - Modeles de Markov, de Kalman etc.
  - Necessite un modele de variables hypothetiques ou variables latentes
  - Tres puissant mais complexe

<div v-click="1">

- **Data Mining**
  - Utilise indicateurs techniques, donnees macro, "buzz" mediatique
</div>
<div v-click="2">

- **Application Pratique**
  - Machine Learning pour detection en temps reel
  - Attention aux pieges: biais de "data snooping" et optimisation excessive

</div>
---

# Ponderations par le Volume et le Temps

- **VWAP - Volume Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le volume
  - Utilisation: Frequemment utilise en trading institutionnel pour minimiser l'impact du marche
  - Mecanisme: Calcule le rapport cout/volume a des intervalles reguliers et execute des ordres en fonction

<div v-click="1">

- **TWAP - Time Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le temps
  - Utilisation: Utilise lorsque l'impact du volume sur le prix est moins pertinent
  - Mecanisme: Divise un gros ordre en plus petits morceaux, executes a intervalles reguliers
</div>
<div v-click="2">

- **TWAP/VWAP sont tres utilises par les institutionnels**
  - Pour eviter un prix moyen trop deforme

</div>
---
layout: image-overlay
image: ./images/security_market_line.png
imageClass: mid-right
---

# Strategies Basees sur les Donnees - Modeles Factoriels

- **Exposition Factorielle**
  - Mesure la sensibilite d'un actif a differents facteurs du marche
  - Taux d'interet, volatilite du marche

<div v-click="1">

- **Rendement Factoriel & Specifique**
  - Le rendement factoriel est celui qui peut etre attribue a l'exposition a certains facteurs
  - Le rendement specifique est le rendement qui n'est pas explique par ces facteurs
</div>
<div v-click="2">

- **Utilisation**
  - Ces modeles sont couramment utilises pour la construction de portefeuilles
  - Pour comprendre les sources de rendement

</div>
---
layout: dense
---
# Strategies Basees sur les Donnees - Sentiment Analysis

- **Objectif**
  - Exploiter les donnees textuelles pour predire les mouvements du marche
<div v-click="1">

- **Technologie**
  - Utilise des techniques de NLP (Natural Language Processing)
  - Analyse des textes tels que les nouvelles, les tweets, etc.

</div>
<div v-click="2">

- **Mecanisme**
  - Le sentiment du marche est extrait des donnees textuelles
  - Utilise pour generer des signaux de trading
</div>
<div v-click="3">

- **Utilisation Pratique**
  - Les hedge funds et les traders algorithmiques utilisent l'analyse du sentiment
  - Pour ameliorer leurs strategies
</div>
<div v-click="4">

- **Importance de la mise en place d'un pipeline de donnees**
  - Collecte, nettoyage, feature engineering etc.

</div>
---

# Metriques des Modeles Factoriels

- **Metriques Standards**
  - R-squared: Proportion de variance expliquee
  - Alpha: Rendement ajuste au risque
  - Beta: Sensibilite au marche
  - Information Ratio: Rendement actif par unite de risque actif

<div v-click="1">

- **Analyse de Performance**
  - Attribution de performance par facteur
  - Contribution au risque par facteur
  - Correlation entre facteurs

</div>
---

# Strategies Basees sur les Donnees 2.0 (1/2)

- **Methodes Modernes**
  - Multi-Factoriels: Evolution des modeles 3F de Fama-French vers des modeles multi-factoriels
<div v-click="1">

- **Machine Learning en Trading**
  - Machine Learning Parametrique: Utilisation de reseaux neuronaux et de modeles sequentiels en deep learning comme LSTM
  - Machine Learning Non-Parametrique: Emploi de forets aleatoires, k-NN, SVM pour capturer des relations non-lineaires
  - Succes des techniques d'ensemble, Mixture of experts

</div>
---

# Strategies Basees sur les Donnees 2.0 (2/2)

- **Avancees en ML et RL**
  - Modeles Sequentiels: Utilisation de LSTM, de GRU, de Transformers en deep learning
  - Reseaux bayesiens dynamiques pour capturer des dependances temporelles
  - Reinforcement Learning (RL): Application a l'optimisation de strategie en temps reel
  - Prise de decision avec ou sans modele predictif associe

<div v-click="1">

- **Analyse & Risques Modernes**
  - Metriques Modernes: Transition du R-squared vers des mesures comme l'Information Ratio
  - Optimisation Bayesienne: Utilisee pour la selection de modele et l'ajustement de parametres
  - Mise a Jour Continue: Adaptation aux changements de comportement du marche via techniques d'apprentissage en ligne

</div>
---

# Workflows Semantique et Theorie des Jeux

- **Workflows semantique**
  - Avenement des LLMs (ChatGPT, Llama etc.)
  - Analyse de sentiment avancee
  - Generation de signaux a partir de donnees textuelles

<div v-click="1">

- **Theorie des jeux**
  - Strategies adversariales, poursuite et predation
  - Signalement (baleines etc.)
  - Flash crashs et manipulation de marche
  - Modelisation des interactions entre traders

</div>
---
layout: section
---

# Questions?

---
layout: image-overlay
image: ./images/payoff_put_option.png
imageClass: mid-right
---

# Strategies de Sortie en Trading (1/2)

- **Periode de Detention Fixe**
  - Utilisee par defaut dans divers modeles de trading
  - Momentum: La periode optimale peut etre trouvee via un backtest
  - Attention a l'evolution rapide de l'information
  - Reversion a la Moyenne: Une methode plus robuste pour determiner la periode optimale est disponible

<div v-click="1">

- **Prix ou Profit Cible**
  - Utilise pour definir un objectif de sortie
  - Reversion a la Moyenne: Le prix moyen historique peut servir de prix cible
  - Momentum: Moins fiable car base sur une evaluation fondamentale incertaine

</div>
---

# Strategies de Sortie en Trading (2/2)

- **Derniers Signaux d'Entree**
  - Utiliser le signal d'entree le plus recent comme signal de sortie
  - Momentum: Si le signal change, c'est presque comme un stop-loss
  - Reversion a la Moyenne: Le signal reste generalement le meme, donc pas de stop-loss recommande

<div v-click="1">

- **Prix Stop**
  - Rarement utilise de maniere efficace
  - Momentum: Peut etre justifie si le sens du momentum change
  - Reversion a la Moyenne: Souvent contre-productif, sauf en cas de changement de regime du a des nouvelles

</div>
---

# Strategies de Sortie 2.0 (1/2)

- **Categories Classiques**
  - Periode de Detention Fixe: Adaptation via ML pour prediction de la periode optimale
  - Prix ou Profit Cible: Integration de donnees en temps reel pour ajuster les cibles
  - Derniers Signaux d'Entree & Prix Stop: Utilisation rare, mais avec opportunites pour optimisation par RL

<div v-click="1">

- **Avancees en ML et Analyse Temps Reel**
  - Deep Learning: Utilisation de CNN ou LSTM pour detection de patterns et ajustement de la strategie de sortie
  - Reinforcement Learning (RL): Apprentissage pour optimiser la sortie en fonction du rendement et du risque

</div>
---

# Strategies de Sortie 2.0 (2/2)

- **Gestion de Risques Avancee**
  - Options & Derives: Utilisation pour couvrir les positions et ajuster les strategies de sortie
  - Analyse Sentimentale: Utilisation de NLP pour ajuster les strategies en fonction du sentiment du marche

<div v-click="1">

- **Alertes et Ajustements en Temps Reel**
  - Web Scraping & API: Collecte en temps reel de donnees de marche pour ajuster les strategies
  - Optimisation Continue: Mise a jour en temps reel des parametres via techniques d'apprentissage en ligne

</div>
---
layout: image-overlay
image: ./images/ted_spread.png
imageClass: mid-right
---

# Arbitrage et Paires

- **Pairs Trading**
  - Objectif: Capitaliser sur la relation entre deux actifs similaires
  - Utilisation: Necessite une analyse de co-integration
  - Mecanisme: Achete un actif et vend un actif similaire en anticipation d'une convergence des prix

<div v-click="1">

- **Statistical Arbitrage**
  - Objectif: Exploiter les ecarts de prix entre des actifs fortement correles
  - Utilisation: Necessite une modelisation statistique complexe
  - Mecanisme: Utilise des modeles statistiques pour identifier les opportunites d'arbitrage

</div>
---

# Market Making et Optimal Trading

- **Market Making**
  - Objectif: Acheter et vendre activement pour profiter de l'ecart acheteur-vendeur
  - Utilisation: Necessite une tres faible latence et de gros volumes
  - Mecanisme: Fournit des liquidites en affichant constamment des offres d'achat et de vente

<div v-click="1">

- **Optimal Trading Strategies**
  - Objectif: Minimiser les couts de transaction et l'impact du marche
  - Utilisation: Generalement utilise par les fonds institutionnels et les traders a haute frequence
  - Mecanisme: Utilise des algorithmes pour optimiser le timing et le cout des ordres

</div>
---

# Strategies de Trading a Haute Frequence (1/2)

- **Exploite de petites inefficacites sur le marche ou fournit une liquidite temporaire en echange d'une petite commission**
<div v-click="1">

- **Ratio de Sharpe Eleve**
  - Loi des grands nombres stabilise le rendement
  - Centaines de paris par jour minimisent les ecarts de rendement

</div>
<div v-click="2">

- **Difficultes et Defis**
  - Couts de transaction cruciaux pour les tests
  - Execution a haute vitesse pour maximiser profits/pertes
  - Risque de liquidation rapide (slippage, anomalies de marche)

</div>
---

# Strategies de Trading a Haute Frequence (2/2)

- **Machine Learning et AI**
  - Utilisation de modeles de Deep Learning pour prediction de micro-tendances
  - Reinforcement Learning pour l'ajustement dynamique de strategies

<div v-click="1">

- **Latence Ultra-Faible**
  - Utilisation de FPGA (Field-Programmable Gate Arrays) pour des ordres en microsecondes
  - Co-location de serveurs pres des bourses

</div>
<div v-click="2">

- **Risques et Reglementations**
  - Detection d'abus de marche par des algorithmes de surveillance
  - Impact des regulations comme MiFID II sur la transparence

</div>
---
layout: dense
---
# Strategies de Trading Saisonnier

- **Effet de Janvier**
  - Petites capitalisations beneficient en janvier
  - Vendre en decembre pour raisons fiscales
<div v-click="1">

- **Strategies Mensuelles**
  - Acheter/vendre selon la performance du mois precedent
  - Efficace jusqu'a 2002

</div>
<div v-click="2">

- **Strategies Matieres Premieres**
  - Essence et gaz naturel
  - Fiable car base sur besoins economiques (ex. petrole en ete)
</div>
<div v-click="3">

- **Precautions**
  - Biais de Data-Snooping
  - Verifier la fiabilite et le sens economique

</div>
---

# Strategies de Trading Saisonnier 2.0 (1/2)

- **Concepts Traditionnels**
  - Effet de Janvier: Machine learning pour identifier les meilleures opportunites en temps reel
  - Strategies Mensuelles: Utilisation d'algorithmes adaptatifs pour revalider l'efficacite
  - Strategies Matieres Premieres: Optimisation par RL pour des meilleures entrees et sorties

<div v-click="1">

- **Innovations en ML & Data Analytics**
  - Time Series Forecasting: LSTM et ARIMA pour predire la saisonnalite
  - Reinforcement Learning (RL): Maximisation des rendements en adaptant les strategies saisonnieres
  - Random Forest & SVM: Classification pour detecter les meilleures periodes d'achat/vente

</div>
---

# Strategies de Trading Saisonnier 2.0 (2/2)

- **Intelligence Contextuelle**
  - IoT & Big Data: Utilisation de donnees meteorologiques et de flux logistiques pour optimiser les trades en matieres premieres
  - Sentiment Analysis: Evaluer l'effet du sentiment saisonnier sur les marches
<div v-click="1">

- **Gestion de Risques Avancee**
  - Simulation de Monte Carlo: Estimation des intervalles de confiance pour les strategies
  - Backtesting Adaptatif: Tests dynamiques pour ajuster aux changements du marche

</div>
---
layout: image-overlay
image: ./images/capital_market_line.png
imageClass: mid-right
---

# Portefeuille a Haut Levier vs Haut Beta (1/2)

- **Beta**
  - Mesure de la sensibilite d'un actif par rapport au marche
  - Haut Beta: Plus volatil, plus de rendements mais plus de risques
  - Faible Beta: Moins de risques, meilleur ratio de Sharpe

<div v-click="1">

- **Levier**
  - Utilisation d'emprunts pour augmenter l'exposition aux actifs
  - Effet Amplificateur: Augmente les gains mais aussi les pertes
  - Risques de Queue Epaisse: Pertes imprevues dues a une distribution de rendements atypique

</div>
---

# Portefeuille a Haut Levier vs Haut Beta (2/2)

- **Ratio de Sharpe**
  - Mesure le rendement ajuste au risque
  - Croissance Composee: Proportionnelle au carre du ratio de Sharpe
<div v-click="1">

- **Allocation d'Actifs**
  - Repartition du portefeuille entre differentes classes d'actifs
  - Optimisation 23-77: Entre actions a faible beta et obligations pour un risque minimal

</div>
<div v-click="2">

- **Un faible beta avec un levier modere**
  - Offre theoriquement une meilleure croissance composee a long terme (cf. formule de Kelly)
  - Mais avec des risques inherents

</div>
---

# Portefeuille a Haut Levier vs Haut Beta 2.0 (1/2)

- **Beta Adaptatif**
  - Utilisation de l'apprentissage machine pour ajuster dynamiquement le beta
  - Predictions de Volatilite: Utilisation de series temporelles pour anticiper les changements de volatilite
<div v-click="1">

- **Levier avec Machine Learning**
  - Algorithmes pour decider du moment optimal pour appliquer un levier
  - Risques de Catastrophe: Utilisation d'alertes algorithmiques pour reduire le levier en cas de signaux de crash

</div>
---

# Portefeuille a Haut Levier vs Haut Beta 2.0 (2/2)

- **Optimisation de Ratio de Sharpe avec IA**
  - Utilisation de reseaux de neurones pour maximiser le ratio de Sharpe
  - Apprentissage par Renforcement: Pour une allocation d'actifs dynamique et optimisee

<div v-click="1">

- **Gestion du Risque 2.0**
  - Techniques modernes comme le "Value-at-Risk" (VaR) base sur le deep learning
  - Indicateurs de Sentiment du Marche: Via le traitement du langage naturel pour anticiper les changements de marche
</div>
<div v-click="2">

- **La version 2.0 integre des techniques d'apprentissage machine et d'analyse de donnees pour une gestion plus proactive et adaptative du risque et du rendement**

</div>
---
layout: section
---

# Questions?

---
layout: cover
---

# Initiation a Lean

Documentation officielle QuantConnect

---
layout: dense
---
# Lean/QuantConnect

- **Qu'est-ce que c'est?**
  - Plateforme de trading algorithmique
<div v-click="1">

- **Langages de Programmation**
  - C#, Python

</div>
<div v-click="2">

- **Fonctionnalites Principales**
  - Notebooks d'analyse, Backtesting, optimisation, paper et live trading
</div>
<div v-click="3">

- **Data Library**
  - Donnees historiques de plusieurs marches
</div>
<div v-click="4">

- **Communaute & Ressources**
  - Forums, tutoriels, documentation

</div>
---

# Installation de l'Environnement (1/2)

- **3 environnements**
  - QuantConnect: Plateforme dans le Cloud
  - Lean-Cli + vscode: Plateforme hybride QC + containers locaux
  - Lean: Plateforme Open-source locale

<div v-click="1">

- **QuantConnect**
  - Creer un compte
  - Organisations, Noeuds de ressources
</div>
<div v-click="2">

- **Lean-cli**
  - Terminal
  - IDEs locaux

</div>
---

# Installation de l'Environnement (2/2)

- **VS Code**
  - Extensions: C# dev kit, polyglot, python, git extension pack, Python extension pack, QuantConnect
<div v-click="1">

- **Visual Studio Community / for Mac**
  - Charge de developpement Desktop (Windows) / .Net (Mac)
</div>
<div v-click="2">

- **DotPeek (desassembleur)**
</div>
<div v-click="3">

- **Jetbrains Rider**
  - Licence?

</div>
---

# Mise en Route Lean-cli / VScode

- **Installation pip**
  - `pip install --upgrade lean`
  - `lean --version`
<div v-click="1">

- **Sur QuantConnect**
  - My Account -- Request Token Information

</div>
<div v-click="2">

- **Lean init**
  - Choix de l'"Organisation"
</div>
<div v-click="3">

- **Synchronisation**
  - `lean cloud pull`
  - `lean cloud push`

</div>
---

# Mise en Route Lean (1/2)

- **Fork/Clone git de Lean**
  - Dans le repertoire de votre choix
  - Depot personnalise: https://github.com/myintelligenceagency/Lean
<div v-click="1">

- **Ouvrir la solution**
  - QuantConnect.Lean.sln
  - Affichage des projets, projet de demarrage par defaut
</div>
<div v-click="2">

- **Generer la solution**
  - Restauration des packages, compilation des projets

</div>
---

# Mise en Route Lean (2/2)

- **Executer le Launcher**
  - Demarrage en debug
  - Fichier de config `Lean/Launcher/bin/debug/config.json`
  - Algorithme par defaut: BasicTemplateFrameworkAlgorithm
  - Placer un point d'arret dans la fonction Initialize et relancer

<div v-click="1">

- **Desassemblage**
  - DotPeek / serveur de symboles
</div>
<div v-click="2">

- **Developpement et debuggage en Python**
  - https://github.com/MyIntelligenceAgency/Lean/blob/master/ESGF/Python.md

</div>
---
layout: dense
---
# Environnement d'Algorithme (1/2)

- **QCAlgorithm**
  - Ticker vs Bar
  - Evenements => pas de lookahead
  - \+ Interfaces + Classes de base
  - \+ Strategic Development Framework

<div v-click="1">

- **Objets fondamentaux**
  - Time
  - Symboles
  - Portfolio
  - Securities
  - Brokers

</div>
---

# Environnement d'Algorithme (2/2)

- **Objets fondamentaux (suite)**
  - Indicateurs (e.g. EMA)
  - History
<div v-click="1">

- **Membres locaux**
  - Manipules par les methodes
  - Parfois herites + "Parameters"
  - Possibilite de les initializer

</div>
---

# Evenements (1/2)

- **Initialize**
  - Setxxx, Addxxx, ajout de handlers (InsightsGenerated etc.)
  - Gestion des dates + Consolidateurs
  - Cash / AddEquities/AddForex etc. (+ resolution) vs SetUniverseSelection
  - SetBrokerageModel, SetPortfolioConstruction, SetDataNormalisationMode

<div v-click="1">

- **OnData**
  - Slice => Ticks, TradeBars
  - => dictionaire par symbole
  - Price => close (data, data.Bars, Securities[xx])

</div>
---

# Evenements (2/2)

- **OnData (suite)**
  - Decision => Portfolio.Invested, nextEntryTime
  - Ordres: MarketOrder (symbol, calcul), SetHoldings
  - Journalisation: Log
  - Sortie: condition/entryprice -- Liquidate

<div v-click="1">

- **OnOrderEvent**
  - Filled, Submitted etc.
</div>
<div v-click="2">

- **Autres points d'entree**
  - OnSecuritiesChange, OnEndOfDay, OnBrokerageMessage, OnWarmupFinished etc.
  - Evenements planifies (Schedule)

</div>
---
layout: dense
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
<div v-click="1">

- **Definition des monnaies et montants initiaux**
  - C#: `this.SetAccountCurrency("EUR"); this.SetCash("EUR", 10000);`
  - Python: `self.SetAccountCurrency("BTC"); self.SetCash("EUR", 10000)`

</div>
---
layout: dense
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
<div v-click="1">

- **Ajout d'indicateurs**
  - C#: `this.Fast = EMA(_btcusd, FastPeriod); this.Slow = EMA(_btcusd, SlowPeriod);`
  - Python: `self.fast = self.EMA(symbol, 30, Resolution.Minute); self.slow = self.EMA(symbol, 60, Resolution.Minute)`

</div>
---
layout: dense
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
<div v-click="1">

- **Possibilite de Warmup automatique**
  - `AutomaticIndicatorWarmUp = True`
  - `self.Settings.AutomaticIndicatorWarmUp = True`

</div>
---
layout: dense
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
---
layout: dense
---
layout: dense
---
layout: dense
---
# Initialisation - Consolidation et Graphiques

- **Consolidation de barres**
  - C#: `this._consolidator = Consolidate(_symbol, TimeSpan.FromMinutes(10), ConsolidationHandler);`
  - Python: `self.consolidator = self.Consolidate(self.symbol, timedelta(minutes=10), self.consolidation_handler)`
<div v-click="1">

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

</div>
---
layout: dense
---
# Evenements de Donnees

- **Temps decoupe en "slices"**
  - Peuvent contenir des Ticks (ponctuel) ou TradeBars, QuoteBars (periodes)
<div v-click="1">

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
</div>
<div v-click="2">

- **Alternative: "CurrentSlice"**
  - Dans un evenement planifie

</div>
---
layout: dense
---
layout: dense
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
<div v-click="1">

- **Export de graphiques**
  - Methode Plot (cf initialisation)
</div>
<div v-click="2">

- **Utilisation de donnees historiques**
  - Python: `self.df = self.History(self.Symbol("SPY"), start_time, end_time, Resolution.Hour)`
  - Plusieurs symbols: `self.dataframe = self.History([self.Symbol("IBM"), self.Symbol("AAPL")], start_time, end_time)`

</div>
---

# Gestion Explicite des Ordres (1/2)

- **Types**
  - Market, Limit, StopMarket, StopLimit, MarketOnOpenOrder, MarketOnCloseOrder etc.
<div v-click="1">

- **Exemples**
  - C#: `var orderTicket = this.StopMarketOrder("IBM", 10, price / 0.1m);`
  - Python: `marketOrderTicket = self.LimitOrder("SPY", 100, 21.67)`

</div>
<div v-click="2">

- **Type de retour: OrderTicket**
  - Permet de suivre l'ordre (Status, QuatityFilled etc.)
  - Possibilite de faire des MAJ chez certains Brokers
  - Classe UpdateOrderFields, methode ticket.Update

</div>
---

# Gestion Explicite des Ordres (2/2)

- **Methode OnOrderEvent**
  - C#: `public override void OnOrderEvent(OrderEvent orderEvent)`
  - Python: `def OnOrderEvent(self, orderEvent: OrderEvent) -> None:`
<div v-click="1">

- **Annulation**
  - Methode ticket.Cancel("message") ou request = ticket.CancelOrderRequest()

</div>
---

# Gestion des Ordres par Dimensionnement (1/2)

- **Dimensionnement de position**
  - Ponderer la valeur des actifs du portefeuille
<div v-click="1">

- **Exemples**
  - C# (version simple): `this.SetHoldings("IBM", 0.5);`
  - Python (tous les parametres): `self.SetHoldings(symbol, weight, liquidate_existing_holdings, tag, order_properties)`

</div>
<div v-click="2">

- **Possibilite de definir plusieurs cibles d'actifs simultanement**
  - `self.SetHoldings([PortfolioTarget("SPY", 0.8), PortfolioTarget("IBM", 0.2)], True)`

</div>
---

# Gestion des Ordres par Dimensionnement (2/2)

- **Calcul des quantites tenant compte des frais**
  - `var quantity = CalculateOrderQuantity("IBM", 0.4);`
<div v-click="1">

- **Existence d'un Buffer (slippage)**
  - 2,5% par defaut
  - Personalisation:
    - `Settings.FreePortfolioValuePercentage = 0.05m;` (pourcentage)
    - `self.Settings.FreePortfolioValue = 10000` (Valeur absolue)

</div>
<div v-click="2">

- **Liquidation**
  - C# (un actif): `Liquidate("AAPL", "Liquidated");`
  - Python (toutes les positions): `order_ids = self.Liquidate()`

</div>
---
layout: dense
---
# Notebooks de Recherche

- **Research Environnement**
  - Environnement d'exploration facilitant l'iteration
  - Jupyter / Python
  - .Net Interactive / C#

<div v-click="1">

- **Workflow**
  - Hypothese / Edge -> Research -> Strategy -> Backtests/Optimisation -> Paper/Live trading
</div>
<div v-click="2">

- **Kernel dedie**
  - Execution QC en ligne
  - Execution sous container Docker / lean-cli
</div>
<div v-click="3">

- **QuantBooks**
  - Classe heritant de QCAlgorithm
  - Utilisation de donnees historisees / dataframes pour analyse

</div>
---

# Framework de Haut Niveau

- **Ensemble de modules de haut niveau**
  - Universe Selection: Choix des instruments disponible
  - Alpha Creation: Construction de signaux (insights)
  - Portfolio construction: construction et maintenance du portefeuille (targets)
  - Risk management (minimization de risque)
  - Execution (immediate ou optimisee)

<div v-click="1">

- **Abstractions facilitant la gestion de portefeuille**
  - Utilisable en combinaison avec des primitives de bas niveau
  - (Alpha, PortfolioConstruction, Risk, Execution) peuvent etre utilises individuellement ou combines

</div>
---
layout: dense
---
# Selection d'Univers

- **Un univers definit les actifs disponibles pour le portefeuille**
<div v-click="1">

- **Selection manuelle**
  - `AddUniverseSelection(new ManualUniverseSelectionModel(symbols));`
</div>
<div v-click="2">

- **Selection parametrique ou planifiee**
  - Ex: EmaCrossUniverseSelectionModel
  - Selectionne les actifs d'un ensemble en retournement haussier le plus fort

</div>
<div v-click="3">

- **Combinaisons d'univers possible**
</div>
<div v-click="4">

- **Methode OnSecurityChanged quand des actifs sont rajoutes ou enleves**
  - C#: `public override void OnSecuritiesChanged(SecurityChanges changes)`
  - Python: `def OnSecuritiesChanged(self, algorithm: QCAlgorithm, changes: SecurityChanges) -> None:`

</div>
---

# Alphas (1/2)

- **Classes chargees de generer des signaux**
  - = Insights (direction, amplitude et confiance)
  - e.g. A partir d'indicateurs
<div v-click="1">

- **Ajout a l'initialisation**
  - `self.AddAlpha(RsiAlphaModel())`

</div>
<div v-click="2">

- **Alphas par defaut**
  - ConstantAlphaModel, HistoricalReturnsAlphaModel, EmaCrossAlphaModel, MacdAlphaModel, RsiAlphaModel
  - BasePairsTradingAlphaModel, PearsonCorrelationPairsTradingAlphaModel etc.

</div>
---
layout: dense
---
layout: dense
---
# Alphas (2/2)

- **Alpha personnalise**
  - Python: classe + initialisation + creation d'insights
    ```python
    class MyAlphaModel(AlphaModel):
        def OnSecuritiesChanged(self, algorithm: QCAlgorithm,
                                changes: SecurityChanges) -> None:
            pass
        def Update(self, algorithm: QCAlgorithm,
                   data: Slice) -> List[Insight]:
            pass
    ```
  - C#
    ```csharp
    class MyAlphaModel : AlphaModel
    {
        public override IEnumerable<Insight> Update(
            QCAlgorithm algorithm, Slice data)
        public override void OnSecuritiesChanged(
            QCAlgorithm algorithm, SecurityChanges changes)
    }
    ```
---
layout: dense
---
layout: dense
---
# Insights

- **Definit les signaux retournes par la methode Update des Alphas**
<div v-click="1">

- **Exemples**
  - Python: `insight = Insight.Price("IBM", timedelta(minutes = 20), InsightDirection.Up)`
  - C#: `var insight = Insight.Price("IBM", TimeSpan.FromMinutes(20), InsightDirection.Up);`
</div>
<div v-click="2">

- **Caracteristiques**
  - Parametres importants: Direction, Period, Magnitude, Confidence, Weight
  - Possibilite de les regrouper: `return Insight.Group([insight1, insight2, insight3])`
  - Possibilite de les annuler: `self.insight.Cancel(algorithm.UtcTime)`
</div>
<div v-click="3">

- **Si pas de reference utilisation de l'insight manager**
  - Filtrage par symbole, par direction etc.
  - `var insights = algorithm.Insights.GetInsights(insight => insight.Direction == InsightDirection.Up);`
  - `algorithm.Insights.Cancel(symbols)`

</div>
---

# Construction de Portefeuille (1/2)

- **Modele de construction de portefeuille**
  - Creee des "targets" qui se traduisent par des ordres
<div v-click="1">

- **Exemples**
  - Python: `self.SetPortfolioConstruction(EqualWeightingPortfolioConstructionModel())`
  - C#: `SetPortfolioConstruction(new EqualWeightingPortfolioConstructionModel());`

</div>
<div v-click="2">

- **Modeles fournis par defaut**
  - EqualWeightingPortfolioConstructionModel: Poids egal entre les actifs avec Insights
  - ConfidenceWeightedPortfolioConstructionModel: Ponderation par la confiance de l'insight
  - InsightWeightingPortfolioConstructionModel: Ponderation par poids de l'insight

</div>
---
layout: dense
---
layout: dense
---
# Construction de Portefeuille (2/2)

- **Modeles fournis par defaut (suite)**
  - SectorWeightingPortfolioConstructionModel: Ponderation par secteur industriel
  - AccumulativeInsightPortfolioConstructionModel: Compte les insights par symbole et direction
  - MeanVarianceOptimizationPortfolioConstructionModel: Minimise la volatilite
  - BlackLittermanOptimizationPortfolioConstructionModel: Utilise un optimiseur
  - MeanReversionPortfolioConstructionModel: Retour a la moyenne
  - RiskParityPortfolioConstructionModel: Minimisation du risque
<div v-click="1">

- **Optimiseurs fournis**
  - MaximumSharpeRatioPortfolioOptimizer, MinimumVariancePortfolioOptimizer
  - UnconstrainedMeanVariancePortfolioOptimizer, RiskParityPortfolioOptimizer

</div>
---
layout: dense
---
# Gestion du Risque

- **Objectif: gestion du risque des cibles**
  - Renvoyees par le gestionnaire de portefeuille
  - Idealement, doit etre integre des la conception, pas apres optimisation
  - Sinon, souvent performances degradees
<div v-click="1">

- **Definition**
  - C#: `this.AddRiskManagement(new MaximumDrawdownPercentPerSecurity());`
  - Python: `self.AddRiskManagement(MaximumSectorExposureRiskManagementModel())`

</div>
<div v-click="2">

- **Modeles fournis par defaut**
  - MaximumDrawdownPercentPerSecurity, MaximumDrawdownPercentPortfolio
  - MaximumUnrealizedProfitPercentPerSecurity
  - MaximumSectorExposureRiskManagementModel, TrailingStopRiskManagementModel

</div>
---

# Modeles d'Execution

- **Determine comment les ordres sont executes**
<div v-click="1">

- **Definition**
  - C#: `this.SetExecution(new ImmediateExecutionModel());`
  - Python: `self.SetExecution(ImmediateExecutionModel())`
</div>
<div v-click="2">

- **Modeles fournis**
  - ImmediateExecutionModel
  - SpreadExecutionModel (Necessite des QuoteBars)
  - StandardDeviationExecutionModel
  - VolumeWeightedAveragePriceExecutionModel

</div>
---
layout: dense
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

<div v-click="1">

- **Configuration dynamique**
  - Fichier config.json
  - Interface en ligne dediee / UI similaire dans l'extension vscode

</div>
---
layout: dense
---
# Optimisation de Parametres (2/2)

- **Lanceur d'Optimisation**
  - Execute une serie de backtests
  - Dans l'objectif de trouver la meilleure combinaison des parametres
  - Pour optimiser une mesure (e.g. ratio de Sharpe)
<div v-click="1">

- **Environnement**
  - QuantConnect: bouton et Formulaire de parametrage (Utilisation de credits dans le cloud)
  - Lean-cli: Commande dediee
  - Lean: QuantConnect.Optimizer.Launcher

</div>
<div v-click="2">

- **Bon usage**
  - Attention a la combinatoire (Produit cartesien de toutes les possibilites voire + pour Euler)
  - Utilisation d'une version d'algo "rapide" (test manuel de sensibilite a la resolution)
  - Attention au sur-apprentissage (Optimisation sur une periode donnee, validation finale sur une periode + recente)

</div>
---

# Optimisation de Parametres - Configuration (1/2)

- **Configuration**
  - Designation de l'algo C# ou Python identique: "algorithm-type-name", etc.
  - A priori pas de debug, au besoin utiliser la journalisation
<div v-click="1">

- **Designation des parametres a optimiser**
  - parameters: name, min, max, step

</div>
<div v-click="2">

- **2 strategies d'exploration**
  - GridSearch: teste toutes les combinaisons
  - EulerSearch: teste toutes les combinaisons, puis raffine a partir de la meilleure
  - Parametres supplementaires pour la subdivision des steps initiaux: min-step, default-segment-amount

</div>
---

# Optimisation de Parametres - Configuration (2/2)

- **Definition des objectifs**
  - Parametre optimization-criterion a optimiser
  - Parametre target a maximiser ou minimiser (extremum)
  - Cf class PerformanceMetrics
  - Cible a atteindre target-value (Permet d'arreter l'optimisation de facon prematuree)
<div v-click="1">

- **Ajout de contraintes**
  - Parametres target, operator, target-value
  - Permet de disqualifier certaines configurations (risque trop eleve)

</div>
---
layout: section
---

# Questions?

---
layout: image-overlay
image: ./images/lstm_cell.png
imageClass: mid-right
---

# Machine Learning pour le Trading (1/2)

- **Prediction de Series temporelles**
  - Regression: Prediction du prix
  - Classification: Prediction de la tendance (trend haussier, baissier, neutre)
  - Detection d'anomalie

<div v-click="1">

- **Evolution des architectures**
  - RNN (LSTM)
  - Transformers
  - CNN
  - Diffusion

</div>
---

# Machine Learning pour le Trading (2/2)

- **Retours sur le trading**
  - Marche en constante evolution (modeles MAJ)
  - Regression difficile / pas tres adaptee
  - Modeles de classification boostes relativement efficaces

---
layout: image-overlay
image: ./images/rnn_unrolled.png
imageClass: mid-right
---
layout: dense
---
# Difficultes du ML dans le Trading (1/2)

- **Non stationnarite**
  - Different des Times series classiques
  - Changements continuels dans les distributions de donnees
  - Pire que ca: adversarial
  - Le marche s'adapte, changement de regimes intentionnels
  - Necessite de beaucoup de feedback, attention aux modeles statiques

<div v-click="1">

- **Identification de regimes distincts**
  - Duree des transitions assez lente / difficile a detecter
  - Detection d'anomalie difficile
  - Emprise du regime localisee / globale
  - Intensite des changements des regimes

</div>
---

# Difficultes du ML dans le Trading (2/2)

- **Donnees inadequates**
  - Ratio signal / bruit mauvais
  - Granularite variable des donnees (e.g. rapports trimestriels)
  - Donnees insuffisantes / overfitting
  - Importance d'un pipeline de reentrainement continu

---
layout: dense
---
# ML en .Net

- **ML.Net** https://github.com/dotnet/machinelearning
  - Classification, Regression, Deep-learning, ONNX
<div v-click="1">

- **Tensorflow.Net** https://medium.com/@mariusmuntean/operationalize-tensorflow-models-with-ml-net-8b7389628d70
</div>
<div v-click="2">

- **TorchSharp** https://github.com/dotnet/TorchSharp
  - Similaire a Pytorch (Bridge), Base de Autodiff.Net
</div>
<div v-click="3">

- **Infer**
  - Programmation probabiliste
  - https://dotnet.github.io/infer/default.html
  - https://www.mbmlbook.com/toc.html
</div>
<div v-click="4">

- **AutoML**
  - Choix du modele et hyperparametrisation
  - "experiments" sur differents trainers
</div>
<div v-click="5">

- **TimeSeries**

</div>
---

# Exemples et Ressources ML.Net

- **Exemples**
  - https://github.com/dotnet/machinelearning-samples/tree/main
  - https://github.com/dotnet/csharp-notebooks/tree/main/machine-learning
<div v-click="1">

- **Accord** http://accord-framework.net/
  - Complet mais obsolete/vieillissant
  - SVM toujours d'actualite
  - Autres algos pris en charge par ML.Net

</div>
---

# ML dans Lean/QC (1/2)

- **Exemple Accord SVM**
  - Exemple simpliste
  - Entrainement a la volee
  - A utiliser en combinaison avec d'autres indicateurs/signaux
<div v-click="1">

- **Integration MyIA.Backtesting**
  - Nombreux parametres
  - Entrainement en batch

</div>
---

# ML dans Lean/QC (2/2)

- **Types de modeles**
  - Accord SVM: Type de noyau + complexite
  - ML.Net AutoML: Classification, metrique d'optimisation
  - A venir: prediction: modele regressif
<div v-click="1">

- **Integration Lean dans une branche dediee**
</div>
<div v-click="2">

- **Nouveaux exemples QC**
  - https://www.quantconnect.com/docs/v2/writing-algorithms/machine-learning/key-concepts

</div>
---
layout: section
---

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
layout: cover
---

# Merci

Jean-Sylvain Boige
jsboige@myia.org

> **Notebooks associes:** `QuantConnect/` (~27 notebooks)
> Strategies de trading, backtesting, optimisation, machine learning
