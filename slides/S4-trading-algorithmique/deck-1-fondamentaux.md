---
theme: ../theme-ia101
title: "S4 Trading Algorithmique - Partie 1 : Fondamentaux"
info: Cours Intelligence Artificielle - Trading Algorithmique - Fondamentaux
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Trading Algorithmique

Intelligence Artificielle -- S4 -- Partie 1 : Fondamentaux

**Trading automatise et IA pour les marches financiers**

- Comprendre les fondamentaux du trading algorithmique
- Apprendre a utiliser Lean/QuantConnect
- Concevoir et implementer un algorithme de trading
- Evaluer et optimiser une strategie algorithmique
- Maitriser le traitement de donnees et l'IA pour le trading

---

# Pourquoi le Trading Algorithmique ?

- **Un marche en pleine transformation**
  - Plus de 70% des transactions sur les marches americains sont automatisees
  - Les hedge funds quantitatifs (Renaissance, Two Sigma, Citadel) dominent la performance
  - L'acces aux outils s'est democratise : Python, APIs gratuites, cloud computing

<div v-click="1">

- **Pourquoi ce cours ?**
  - Comprendre les mecanismes qui regissent les marches modernes
  - Acquerir les competences pratiques avec Lean/QuantConnect
  - Developper une pensee critique face aux promesses du trading automatise
  - Preparer une carriere en finance quantitative ou en data science financiere

</div>
<div v-click="2">

- **Ce que ce cours n'est PAS**
  - Une promesse de gains faciles
  - Un cours de day trading ou de speculation
  - Le trading algorithmique demande rigueur, patience et discipline

</div>

> Ref: *Hands-On AI Trading* Ch1 p.3-7

---

# Plan du Cours - Partie 1 : Fondamentaux

Ce cours est organise en 3 decks thematiques :

- **Deck 1 : Fondamentaux** (ce deck)
  - Definition, profil du trader algorithmique
  - Types de trading (HFT, MFT, LFT)
  - Marches financiers et instruments
  - Ordres de trading
  - Trouver et evaluer une strategie

<div v-click="1">

- **Deck 2 : Strategies et Gestion du Risque**
  - Strategies de trading (Momentum, Mean Reversion, Arbitrage...)
  - Backtesting et metriques de performance
  - Gestion du risque (Kelly, stop loss, diversification)

</div>
<div v-click="2">

- **Deck 3 : Pratique avec Lean/QuantConnect**
  - Installation et environnement QuantConnect
  - Framework Lean : structure d'un algorithme
  - Machine learning pour le trading

</div>

---

# Plan du Cours - Detail de ce Deck

**Deck 1 : Fondamentaux** -- ce que nous allons couvrir :

- Qu'est-ce que le trading algorithmique ? Profil du trader quant
- Types de trading : HFT, MFT, LFT et leurs differences
- Les acteurs du marche (Renaissance, Two Sigma, Citadel, QC)
<div v-click="1">

- Vue d'ensemble des marches et instruments financiers
- Analyse technique et fondamentale, patterns graphiques
- Infrastructure de trading et carnet d'ordres
</div>
<div v-click="2">

- Types d'ordres (Market, Limit, Stop, Trailing, Iceberg, OCO)
- Trouver et evaluer une strategie (Sharpe, drawdown, pieges)
- Le livre de reference : *Hands-On AI Trading* (Wiley 2025)
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

> Notebook: QC-Py-01-Setup.ipynb

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

- **Parcours types**
  - Quantitative analyst (modelisation, recherche)
  - Algo developer (implementation, infrastructure)
  - Portfolio manager (allocation, supervision)

</div>
<div v-click="3">

- **Experience pratique**
  - Finance et programmation cruciales
  - Avoir des economies pour les periodes sans gains
  - Discipline et gestion du stress indispensables

</div>

---

# Les Acteurs du Trading Quantitatif

- **Jim Simons / Renaissance Technologies**
  - $100B+ AUM, 66% CAGR sur 30 ans (Medallion Fund)
  - Considere comme le plus grand trader quantitatif de l'histoire

<div v-click="1">

- **Two Sigma**
  - 1600 employes, >$60B AUM, approche entierement data-driven

</div>
<div v-click="2">

- **Citadel Securities**
  - 27% du volume US equity, market maker dominant

</div>
<div v-click="3">

- **DE Shaw**
  - Pionnier du trading algorithmique depuis 1988

</div>
<div v-click="4">

- **QuantConnect**
  - 300K+ utilisateurs, democratisation du trading quantitatif
  - Plateforme open-source, acces gratuit aux donnees et au cloud

</div>
<div v-click="5">

- **Message** : le trading algo n'est plus reserve aux institutions. Les outils modernes permettent a des individuels de developper et tester des strategies professionnelles.

</div>

---

# Avantages du Trading Algorithmique (1/2)

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

---

# Avantages du Trading Algorithmique (2/2)

- **Elimination des biais emotionnels**
  - Pas de peur, de cupidite ou d'hesitation
  - Execution disciplinee selon des regles predefinies
  - Resultats reproductibles et mesurables
<div v-click="1">

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

- **LFT (Low-Frequency Trading)** -- notre terrain de jeu dans ce cours
  - Operations sur des jours, semaines ou mois
  - Objectif : investissement base sur des facteurs fondamentaux ou des indicateurs techniques
  - Accessible avec un PC personnel, Python, et un compte QC gratuit

<div v-click="1">

- **Notre positionnement dans ce cours**
  - Nous travaillons en **LFT** (rebalancement journalier a bimensuel)
  - Capital simule de 100 000 $ pour la comparabilite entre strategies
  - Objectif Sharpe > 0.5 (battre le buy-and-hold SPY), idealement > 1.0
  - Les strategies MFT et HFT sont presentees pour la culture mais ne sont pas praticables dans notre cadre

</div>

---

# Comparaison HFT / MFT / LFT

<div class="colored-table">

| Critere | HFT | MFT | LFT |
|---------|-----|-----|-----|
| **Horizon** | Microsecondes a secondes | Minutes a heures | Jours a mois |
| **Trades/jour** | 10 000+ | 10 - 100 | 0 - 5 |
| **Sharpe typique** | > 5 | 1 - 3 | 0.5 - 1.5 |
| **Capital min.** | > 1M$ | 10K - 100K$ | 1K - 50K$ |
| **Infrastructure** | Co-location, FPGA | Serveur dedie | PC personnel |
| **Competences** | C++, reseaux, hardware | Python, stats | Finance, analyse |
| **Barriere a l'entree** | Tres haute | Moyenne | Basse |

</div>

---

# Le Workflow du Trader Quantitatif

Un processus iteratif en 6 etapes :

1. **Hypothese** : Idee de strategie (observation de marche, papier academique)

<div v-click="1">

2. **Recherche** : Exploration dans un notebook QC (QuantBook, pandas, plots)

</div>
<div v-click="2">

3. **Implementation** : Codage dans `main.py` (QCAlgorithm, Initialize, OnData)

</div>
<div v-click="3">

4. **Backtest** : Execution historique et analyse des metriques (Sharpe, MaxDD, CAGR)

</div>
<div v-click="4">

5. **Paper Trading** : Validation en temps reel sans argent reel

</div>
<div v-click="5">

6. **Live Trading** : Deploiement avec capital reel et monitoring continu

</div>
<div v-click="6">

- A chaque etape, on peut revenir en arriere pour affiner
- La majorite du temps est passe dans les etapes 1-4

</div>

> Ref: *Hands-On AI Trading* Ch2 "Research Process" p.25-26

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

> Ref: *Hands-On AI Trading* Ch1 "Market Mechanics" p.3

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

> Ref: *Hands-On AI Trading* Ch1 "Assets and Derivatives" p.15-24 | Notebooks: QC-Py-06 (Options), QC-Py-07 (Futures/Forex)

---
layout: image-overlay
image: ./images/candlestick_anatomy.png
imageClass: top-right visible
---

# Analyse Technique et Fondamentale

- **Analyse Technique**
  - Etude des graphiques de prix et de volume
  - Indicateurs : moyennes mobiles, RSI, MACD, Bollinger
  - Patterns : chandeliers, tete-epaules, triangles
  - Un chandelier encode 4 infos : open, close, high, low

<div v-click="1">

- **Analyse Fondamentale**
  - Evaluation de la valeur intrinseque d'un actif
  - Ratios financiers : P/E, P/B, EV/EBITDA
  - Indicateurs macro : taux, inflation, PIB

</div>
<div v-click="2">

- **Combinaison des deux approches**
  - Technique pour le timing, fondamentale pour la selection
  - Les traders quantitatifs combinent les deux

</div>

> Notebook: QC-Py-11-Technical-Indicators.ipynb

---
layout: image-overlay
image: ./images/candlestick_patterns.png
imageClass: mid-right visible
---

# Patterns Graphiques Courants

- **Chandeliers japonais**
  - Doji : indecision du marche (ouverture = fermeture)
  - Marteau / Pendu : retournement potentiel
  - Englobante : signal fort de changement de tendance

<div v-click="1">

- **Figures classiques**
  - Tete-Epaules : retournement de tendance majeur
  - Double Top / Double Bottom : niveaux de support/resistance
  - Triangles : compression de volatilite avant cassure

</div>
<div v-click="2">

- **Limites de l'analyse graphique**
  - Subjectivite dans l'interpretation
  - Les patterns fonctionnent mieux en combinaison avec des indicateurs
  - Le trading algorithmique permet de tester objectivement ces patterns sur des donnees historiques

</div>

> Ref: *Hands-On AI Trading* Ch6 Ex17 "Head Shoulders Pattern Matching with CNN" p.256

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

> Ref: *Hands-On AI Trading* Ch1 "Brokerages and Transaction Costs" p.10-13

---
layout: image-overlay
image: ./images/order_book_depth.gif
imageClass: mid-right visible
---

# Le Carnet d'Ordres (Order Book)

- **Structure du carnet**
  - **Bid** (offre d'achat) : prix que les acheteurs sont prets a payer
  - **Ask** (offre de vente) : prix que les vendeurs demandent
  - **Spread** : ecart entre le meilleur bid et le meilleur ask

<div v-click="1">

- **Profondeur de marche** (a droite)
  - Visualise les volumes cumules d'ordres a chaque niveau de prix
  - Un carnet "epais" = marche liquide (faible impact des ordres)
  - Un carnet "mince" = risque de slippage eleve

</div>
<div v-click="2">

- **Pourquoi c'est important**
  - Comprendre le carnet d'ordres est fondamental pour toute strategie
  - Les market makers profitent du spread
  - Les ordres iceberg cachent la vraie profondeur

</div>

> Ref: *Hands-On AI Trading* Ch1 "The Limit Order Book" p.4

---

# Types d'Ordres Essentiels

- **Market Order** (Ordre au marche)
  - Execution immediate au meilleur prix disponible
  - Simple mais risque de slippage en marche peu liquide

<div v-click="1">

- **Limit Order** (Ordre a cours limite)
  - Execution au prix specifie ou mieux
  - Controle du prix d'execution, mais pas de garantie d'execution

</div>
<div v-click="2">

- **Stop Order** (Ordre stop)
  - Declenche un market order quand le prix atteint un seuil predefini
  - Protection contre les pertes : le stop loss classique

</div>
<div v-click="3">

- **Trailing Stop** (Stop suiveur)
  - Stop qui suit le prix a une distance fixe (ex: -5% du plus haut)
  - Protege les gains acquis tout en laissant courir la tendance

</div>

> Notebook: QC-Py-09-Order-Types.ipynb

---

# Types d'Ordres Avances

- **Iceberg Order** (Ordre iceberg)
  - Ordre fractionne pour masquer la taille reelle sur le carnet
  - Utilise par les institutionnels pour eviter l'impact de marche

<div v-click="1">

- **OCO (One-Cancels-Other)**
  - Deux ordres lies : l'execution de l'un annule automatiquement l'autre
  - Exemple : un take profit et un stop loss simultanes

</div>
<div v-click="2">

- **OTO (One-Triggers-Other)**
  - Un ordre declenche automatiquement un autre a son execution
  - Exemple : achat declenche un stop loss automatique

</div>
<div v-click="3">

- **Bracket Order** (Ordre encadre)
  - Combinaison : entree + stop loss + take profit
  - Gestion complete du risque en un seul passage d'ordre

</div>

---
layout: image-overlay
image: ./images/book_cover_handson.png
imageClass: mid-right visible
---

# Le Livre de Reference

- **Hands-On AI Trading with Python, QuantConnect, and AWS**
- Wiley, 2025 | ISBN 978-1-394-26843-6

<div v-click="1">

- **Auteurs** :
  - Jiri Pik (RocketEdge, ex-Goldman/JPMorgan)
  - Ernest Chan (Predictnow.ai, 3 livres Wiley)
  - Jared Broad (CEO QuantConnect)
  - Philip Sun (Adaptive Investments, Boston University)
  - Vivek Singh (AWS GenAI)

</div>
<div v-click="2">

- 20+ exemples implementes, code sur GitHub
- Repo: `github.com/QuantConnect/HandsOnAITradingBook`
- Coupon QC: `education2025`

</div>

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

> Ref: *Hands-On AI Trading* Ch2 "Sourcing Ideas" p.42-45

---

# Trouver une Strategie qui vous Convient (2/2)

- **Votre Capital de Trading**
  - Ancien minimum conseille de 50 000 $ (pattern day trader rule aux US)
  - Nouveaux minima grace aux cryptos (fractional trading) et frais quasi-nuls
  - QC Cloud : backtesting et paper trading **gratuits** -- zero capital pour commencer

<div v-click="1">

- **Votre Objectif**
  - Revenu regulier : strategies a haute frequence de trades (scalping, mean-reversion intraday)
  - Gains en capital : suivi de tendance long terme (momentum, allocation tactique)
  - Couverture (hedging) : proteger un portefeuille existant contre les baisses de marche

</div>
<div v-click="2">

- **Votre Tolerance au Risque**
  - Quel drawdown maximum pouvez-vous supporter ? (10% conservateur, 25% modere, 50% agressif)
  - Horizon d'investissement : court terme (semaines) vs long terme (annees)
  - Regle d'or : ne jamais trader de l'argent dont on ne peut pas se permettre la perte totale

</div>

---

# Comment Evaluer une Strategie?

- **Mesures Standard**
  - **Ratio de Sharpe** : SR = (R_p - R_f) / sigma_p -- le "Saint Graal" de l'evaluation
  - **High Watermark** : Rendement cumule maximal a un moment donne
  - **Drawdown Maximum** : La plus grande baisse (profondeur + duree de recuperation)

<div v-click="1">

- **Criteres de performance**
  - Rendement annualise (CAGR) : le rendement compose annuel
  - Volatilite des rendements : mesure du risque
  - Ratio gain/perte moyen : taille moyenne des gains vs pertes
  - Taux de reussite (win rate) : attention, un win rate de 30% peut etre tres profitable !

</div>
<div v-click="2">

- **Exemple concret**
  - Strategie A : Rendement 15%, Volatilite 20% => Sharpe = 0.75
  - Strategie B : Rendement 10%, Volatilite 8% => Sharpe = 1.25
  - La strategie B est meilleure sur base ajustee au risque malgre un rendement brut plus faible

</div>

> Notebook: QC-Py-12-Backtesting-Analysis.ipynb

---

# Strategies Plausibles et leurs Pieges (1/2)

- **Drawdowns** (la realite brutale de toute strategie)
  - Perte de valeur depuis un pic : profondeur, duree, et vitesse de recuperation a evaluer
  - Exemple : notre meilleure strategie (EMA-Cross-Alpha, Sharpe 0.98) a un MaxDD de 19% -- acceptable
  - Mais InverseVolatility-Rank v1 avait un MaxDD de 54.7% -- inacceptable pour un capital reel
  - Regle : si vous ne pouvez pas dormir avec votre drawdown, reduisez votre exposition
<div v-click="1">

- **Slippage** (l'ecart entre theorie et realite)
  - Difference entre le prix prevu et le prix d'execution reelle
  - Causes : volatilite, taille de l'ordre, liquidite du marche, latence du systeme
  - Impact : peut transformer une strategie profitable en strategie perdante sur petits alphas

</div>
<div v-click="2">

- **Couts de Transaction** (le tueur silencieux de rendements)
  - Commissions : de 0$ (Robinhood) a 0.005$/action (Interactive Brokers)
  - Spread bid-ask : cout cache, particulierement significatif sur les small caps
  - Impact proportionnel a la frequence : une strategie qui trade 50x/jour paie 50x plus qu'une strategie mensuelle
</div>
<div v-click="3">

- **Evolution du Marche** (les strategies ont une date de peremption)
  - Les anomalies disparaissent une fois publiees : les arbitrageurs les exploitent et les eliminent
  - Exemple : l'effet Janvier s'est fortement attenue depuis les annees 2000 (trop connu, trop exploite)
  - Consequence : une strategie doit etre re-evaluee regulierement, pas juste deployee et oubliee

</div>

---

# Strategies Plausibles et leurs Pieges (2/2)

- **Changements de Regime** (le risque le plus sous-estime)
  - Les donnees historiques pre-COVID ne predisent pas le comportement post-COVID
  - Les correlations entre actifs changent en crise (tout baisse ensemble, la diversification echoue)
  - Exemple concret : TLT (obligations longues) etait un refuge fiable jusqu'en 2022, puis s'est effondre avec la hausse des taux

<div v-click="1">

- **Overfitting** (le piege le plus courant en trading quantitatif)
  - Plus vous testez de strategies, plus vous trouverez de "faux positifs" par hasard
  - Un Sharpe de 2.0 sur 3 ans avec 50 parametres est probablement du surajustement
  - Regle : si votre strategie ne marche que sur une periode precise, elle est overfittee

</div>
<div v-click="2">

- **Frais de financement** (le cout cache du levier)
  - Positions a marge : interet annuel sur le capital emprunte (4-8% en 2024-2026)
  - Short selling : cout d'emprunt des titres + risque de rappel (short squeeze, cf. GameStop 2021)
  - Ces frais erosent la performance reelle par rapport au backtest "ideal"

</div>

> Ref: *Hands-On AI Trading* Ch2 "Time and Look-ahead Bias" p.29-30

---

# Intelligence Artificielle et Selection de Stocks

- **Scepticisme initial sur l'IA**
  - Tendance a surajuster les donnees historiques
  - Les marches financiers ne sont pas comme la vision par ordinateur
  - Les patterns changent constamment
<div v-click="1">

- **Pratiques qui fonctionnent en IA**
  - Modeles simples avec fondements econometriques solides
  - Mixture d'experts : combiner plusieurs modeles specialises
  - Features engineering soigne > architectures complexes

</div>
<div v-click="2">

- **Strategies "Sous le Radar"**
  - Marches de niche a faible capacite (small caps, crypto alt coins)
  - Moins d'arbitrage par les grands fonds qui ne s'y interessent pas
  - Opportunite pour les traders individuels et les petites equipes
</div>
<div v-click="3">

- **Avancees recentes (2023-2026)**
  - LLMs pour l'analyse de sentiment et la generation de signaux
  - Foundation models pre-entraines sur les series temporelles financieres

</div>

> Ref: *Hands-On AI Trading* Ch9 "Role of GenAI in Creating Alpha" p.341

---

# Quiz Interactif : Vrai ou Faux ?

**1. "Le trading algorithmique est toujours profitable"**

<div v-click="1">

- **FAUX** : Beaucoup de strategies perdent de l'argent. Sur nos 67 strategies backtestees, certaines ont un Sharpe negatif.

</div>

**2. "Plus de 70% des transactions US sont automatisees"**

<div v-click="2">

- **VRAI** : Les estimations varient de 60% a 80% selon les marches.

</div>

**3. "Il faut un doctorat pour etre trader quantitatif"**

<div v-click="3">

- **FAUX** : QC compte 300K+ utilisateurs de tous niveaux. Les outils modernes democratisent l'acces.

</div>

**4. "Le backtesting garantit les performances futures"**

<div v-click="4">

- **FAUX** : L'overfitting est le piege principal. "Past performance is not indicative of future results."

</div>

**5. "Le ML bat toujours l'analyse technique"**

<div v-click="5">

- **FAUX** : Nos backtests montrent que des modeles simples (EMA, Momentum) rivalisent souvent avec le ML.

</div>

---
layout: section
---

# Suite : Strategies et Gestion du Risque

Deck 2
