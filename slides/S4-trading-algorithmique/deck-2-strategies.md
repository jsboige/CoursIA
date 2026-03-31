---
theme: ../theme-ia101
title: "S4 Trading Algorithmique - Partie 2 : Strategies et Risque"
info: Cours Intelligence Artificielle - Strategies de Trading et Gestion du Risque
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Strategies de Trading et Gestion du Risque

Intelligence Artificielle -- S4 -- Partie 2

**Au programme :**

- Backtesting et plateformes (Lean/QuantConnect)
- Mesures de performance et pieges
- Gestion du risque (Kelly, VaR, psychologie)
- Strategies classiques : mean reversion, momentum, regime switching, factoriels
- Panorama ML/AI : du Random Forest aux LLMs
- Lecons du terrain : 67 projets backtestes, echecs inclus

Livre de reference : *Hands-On AI Trading* (Pik, Chan, Broad, Sun, Singh -- Wiley 2025)

---

# Backtesting (1/2)

- **Le backtesting : votre laboratoire de trading**
  - Simulation d'une strategie sur des donnees historiques (prix, volumes, fondamentaux)
  - Question fondamentale : *"Si j'avais applique cette strategie en 2015, qu'aurais-je obtenu ?"*
  - C'est la premiere etape obligatoire AVANT d'engager le moindre centime de capital reel
<div v-click="1">

- **Pourquoi c'est important**
  - Valider l'efficacite de la recherche avant d'engager du capital reel
  - Experimenter avec des variations (parametres, periodes, actifs, univers)
  - Estimer les metriques cles : Sharpe, CAGR, drawdown max, win rate, nombre de trades
  - Comparer objectivement plusieurs strategies entre elles sur la meme periode

</div>
<div v-click="2">

- **Sources de Donnees**
  - Gratuites : Yahoo Finance, Alpha Vantage, Binance (crypto), FRED (macro)
  - Professionnelles : Interactive Brokers, Bloomberg, Refinitiv, Quandl
  - QuantConnect fournit gratuitement des donnees ajustees (splits, dividendes)
  - Attention : les donnees gratuites ont souvent des biais de survie
  - Notebooks : `QC-Py-03-Data-Management.ipynb`, `QC-Py-12-Backtesting-Analysis.ipynb`

</div>

> Ref: *Hands-On AI Trading* Ch2 p.26 | Notebooks: QC-Py-12, QC-Py-03

---

# Backtesting (2/2)

- **Pieges et Problemes** (tout backtest ment -- la question est : combien ?)
  - Donnees ajustees pour les splits et dividendes : risque de faux signaux historiques
  - Biais de survie : les entreprises faillies disparaissent des donnees (vos backtests ne testent que les "gagnants")
  - Slippage et couts de transaction : le backtest "parfait" n'existe pas en conditions reelles
  - **Regle empirique : le rendement live est 30 a 50% inferieur au backtest** -- prevoir cette marge
<div v-click="1">

- **Dans le cas ou le Machine Learning est utilise**
  - Le backtesting doit prendre en compte les biais de selection de donnees
  - Separer convenablement les ensembles (training, validation, test)
  - Evaluer la generalisation sur des donnees jamais vues
  - **Walk-forward** : decoupe temporelle glissante (jamais de shuffle)

</div>
<div v-click="2">

- **Bonnes pratiques de notre depot**
  - Periode standard : 2015-2026 (11 ans, couvrant bull + bear + COVID + hausse taux)
  - Toujours comparer au benchmark (SPY buy-and-hold, Sharpe ~0.50)
  - Reporter Sharpe, CAGR, MaxDD, et nombre de trades
  - Capital initial standard : 100 000$ pour la comparabilite entre strategies

</div>

> Ref: *Hands-On AI Trading* Ch4 p.83-85 | Lopez de Prado (2018) "Advances in Financial ML"

---

# Plateformes de Backtesting (1/2)

- **Excel**
  - Toutes les donnees sont visibles, ce qui reduit le risque de "look-ahead bias"
  - Utilise a la fois pour le backtesting et le trading en direct
  - Inconvenients: Limite aux modeles simples d'investissement, pas de ML avance

<div v-click="1">

- **MATLAB**
  - Utilise en institutionnel, excellent pour tester des strategies sur de grands portefeuilles
  - Modules statistiques avances (Financial Toolbox, Econometrics Toolbox)
  - Inconvenients: Couteux (~2000$/an) et moins efficace pour executer les trades

</div>
<div v-click="2">

- **R / RStudio**
  - Excellent pour l'analyse statistique et les modeles econometriques
  - Packages : quantmod, TTR, PerformanceAnalytics, tidyquant, rugarch (GARCH)
  - Inconvenients: Plus lent que Python pour le ML, communaute plus petite en trading

</div>

> La tendance 2020-2026 : Python domine le trading quantitatif, R conserve une niche en econometrie academique.
> Julia emerge comme alternative haute-performance pour la recherche (mais communaute encore petite).



---

# Plateformes de Backtesting (2/2)

- **TradeStation et autres plateformes proprietaires**
  - Execution + donnees integrees, mais langage proprietaire (EasyLanguage) et lock-in courtier

<div v-click="1">

- **Evolution des Plateformes Python** (ecosysteme en mutation rapide)
  - **Zipline** (Quantopian, ferme en 2020) : pionnier open-source, communaute dispersee
  - **Backtrader** : communaute active, prototypage rapide, leger
  - **QC Lean** : open-core, le plus complet (Python + C#), donnees gratuites, cloud + local + live
  - **VectorBT** : backtesting vectorise ultra-rapide (numpy), analyses massives
  - Lean est utilise dans ce cours : pipeline le plus complet (recherche -> live)
</div>
<div v-click="2">

- **Comparaison rapide**

| Plateforme | Donnees | Cloud | Live | ML | Status |
|------------|---------|-------|------|----|--------|
| **Lean/QC** | Gratuites | Oui | Oui | Oui | Reference |
| **Backtrader** | A fournir | Non | Broker | Non | Actif |
| **VectorBT** | A fournir | Non | Non | Pandas | Rapide |

</div>

---

# Lean / QuantConnect

- **Solution open-core en Python et C#**
  - 3 environnements : QuantConnect Cloud, Lean-cli + VS Code, Lean local
  - Pipeline complet : recherche -> backtest -> paper trading -> live trading
  - **Utilisee dans ce cours** : 28 notebooks progressifs + 67 projets backtestes dans ce depot

<div v-click="1">

- **Avantages techniques**
  - Donnees ajustees (splits, dividendes) : 75,000+ actions US, 100+ forex, 200+ crypto, futures, options
  - Framework modulaire : Alpha, Portfolio, Risk, Execution (separation des responsabilites)
  - ML natif sur le cloud (sklearn, numpy, pandas), paper trading -> live sans changement de code
  - Exemples crypto : `projects/EMA-Cross-Crypto`, `projects/BTC-MACD-ADX`

</div>
<div v-click="2">

- **Architecture du framework (4 composants interchangeables)**
  - **AlphaModel** : signaux (direction + magnitude + confiance)
  - **PortfolioConstructionModel** : traduit signaux en poids de portefeuille
  - **RiskManagementModel** : limites (MaxDD, trailing stop, position max)
  - **ExecutionModel** : execution des ordres (VWAP, immediat, market on close)
  - Debut : `QC-Py-01-Setup.ipynb` puis `QC-Py-02-Platform-Fundamentals.ipynb`

</div>

---
layout: image-overlay
image: ./images/efficient_frontier.png
imageClass: mid-right visible
---

# Mesures de Performance et Pieges (1/2)

- **Mesures Standard** (les 4 piliers)
  - **Ratio de Sharpe** : (rendement - taux sans risque) / volatilite, annualise (sqrt(252))
  - **Drawdown Maximum** : la plus grande baisse depuis le dernier sommet (en %)
  - **High Watermark** : rendement cumule maximal, reference pour le drawdown

<div v-click="1">

- **Pieges courants** (la "trinite" des biais)
  - **Look-ahead bias** : Utilisation de donnees futures dans le calcul (le plus dangereux)
  - **Data-Snooping Bias** : Overfitting base sur les donnees historiques
  - **Couts de Transaction** : Omission des couts (commissions, slippage, spread)
  - **Biais de survie** : ne tester que sur les actifs qui existent encore

</div>

---

# Mesures de Performance et Pieges (2/2)

- **Avec Machine Learning**
  - Derive des donnees (data drift) : la distribution des donnees evolue dans le temps
  - Les patterns historiques deviennent obsoletes (non-stationnarite des marches)
  - Le modele qui marchait en 2020 peut echouer en 2024

<div v-click="1">

- **Metriques complementaires importantes**
  - **Calmar Ratio** : CAGR / MaxDD -- combine rendement et risque extreme
  - **Sortino Ratio** : comme Sharpe mais ne penalise que la volatilite a la baisse
  - **Information Ratio** : rendement actif / tracking error vs benchmark
  - **Win Rate** : % de trades gagnants (attention : ne suffit pas sans le ratio gain/perte)

</div>
<div v-click="2">

- **Regles pratiques d'interpretation**
  - Sharpe > 0.5 : acceptable, > 1.0 : bon, > 2.0 : excellent (mais verifier l'overfitting)
  - MaxDD < 20% : acceptable pour la plupart des investisseurs (institutionnels : < 10%)
  - Minimum 100 trades pour la significativite statistique
  - Comparer toujours au benchmark : SPY buy-and-hold a un Sharpe d'environ 0.50
  - Notre meilleur : `Framework_Composite_TrendWeather` (Sharpe 1.16, MaxDD -14%)

</div>

---

# Precautions face aux Pieges (1/2)

- **Look-ahead bias** (le piege le plus dangereux et le plus sournois)
  - Utilisation de donnees decalees (toujours `shift(1)` en pandas, `History()` en QC)
  - Forward-testing (paper trading) pour valider en conditions reelles sans biais
  - Exemple classique : utiliser le prix de cloture du jour pour decider d'acheter le meme jour
  - Autre piege : normaliser les features sur toute la periode (inclut le futur dans la normalisation)
<div v-click="1">

- **Data-Snooping Bias** (overfitting sur l'historique -- le tueur silencieux)
  - Peu de parametres : chaque parametre est une opportunite d'overfitting
  - Augmentation, division et adaptation des donnees de backtest (cross-temporal validation)
  - Test de robustesse : la strategie marche-t-elle sur des periodes/actifs differents ?
  - Test de Bonferroni : corriger pour les tests multiples (si vous testez 100 strategies, 5 seront "significatives" par hasard a 5%)
  - "If you torture the data long enough, it will confess to anything" -- Ronald Coase

</div>

---

# Precautions : Robustesse et Validation

- **Modeles de trading sans parametres** (le Graal de la robustesse)
  - Pas de surajustement possible, fiabilite maximale mais alpha plus faible
  - Exemple : momentum pur (acheter les 10% meilleurs du mois precedent, vendre les 10% pires)
  - Le seul "parametre" est la fenetre temporelle (3, 6, 12 mois) -- tres etudie academiquement

<div v-click="1">

- **Validation out-of-sample** (la regle d'or de tout backtest serieux)
  - Split temporel 60/20/20 : entrainement, validation, test final -- jamais de shuffle temporel
  - Walk-forward : fenetre glissante qui avance dans le temps (simule un deploiement reel)
  - Si le Sharpe chute de >50% hors-echantillon, c'est probablement de l'overfitting
  - Toutes nos strategies sont backtestees sur 2015-2026 (11 ans, couvrant bull + bear + COVID + hausse des taux)

</div>

---
layout: compact
---

# Precautions face aux Pieges (2/2)

- **Paper Trading** (le test ultime)
  - Test sur des donnees reelles non vues en temps reel, le plus fiable
  - QuantConnect offre le paper trading directement depuis le cloud
<div v-click="1">

- **Analyse de sensibilite** (parameter stability testing)
  - Variation des parametres (+/-20%) pour evaluer la stabilite de la performance
  - Si le Sharpe change drastiquement avec un petit changement de parametre = overfitting
</div>
<div v-click="2">

- **Simplification du modele** (principe du rasoir d'Occam)
  - Elimination des conditions superflues qui n'ajoutent pas de valeur predictive
</div>
<div v-click="3">

- **Repartition du capital de trading** (diversification des alphas)
  - Repartir entre differentes strategies decorreles pour diminuer la variance globale
  - Exemple : 40% trend, 30% mean-reversion, 30% factoriel
</div>
<div v-click="4">

- **Couts de Transaction** (souvent sous-estimes)
  - A integrer dans le Backtest pour des resultats plus realistes
  - Composantes : commissions + spread + slippage + impact de marche (pour les gros ordres)
</div>
<div v-click="5">

- **Derive des donnees (data drift)** (le probleme fondamental)
  - Revalider les modeles regulierement (trimestriel minimum)
  - Ce qui marchait il y a 5 ans peut ne plus marcher (regime change)

</div>

> Ref: *Hands-On AI Trading* Ch8 "Corrective AI" p.305

---

# Affinement de la Strategie

- **Le Probleme** (l'erosion inevitable de l'alpha -- la "loi de la jungle" des marches)
  - Rendements diminuent quand une strategie devient populaire (alpha decay)
  - Le marche est un ecosysteme adaptatif : les participants copient ce qui marche, ce qui annule l'avantage
  - Exemple frappant : l'anomalie du "low P/E" (Basu, 1977) a ete reduite de 50% depuis sa publication
<div v-click="1">

- **Solutions** (garder un avantage competitif)
  - Variations Mineures: Petites variations de parametres peuvent ameliorer les rendements
  - Exclusion de Stocks: Eviter certains types d'actions (micro-caps illiquides, ADRs)
  - Changement de Timing: Ajuster les points d'entree et de sortie (rebalancing frequency)
  - Innovation: Combiner des alphas connus de maniere originale (composite strategies)

</div>
<div v-click="2">

- **Exemple du depot : evolution progressive**
  - `EMA-Cross-Stocks` (0.87) -> `EMA-Cross-Alpha` (0.98) -> `EMATrend-Composite` (0.87) -> `Framework_Composite_TrendWeather` (1.16)
  - Chaque iteration ajoute sophistication mais aussi risque d'overfitting

</div>

---
layout: dense
---

# Panorama des Strategies (1/2) -- Classiques

<div class="colored-table">

| Strategie | Categorie | Sharpe | CAGR | MaxDD | Periode |
|-----------|-----------|--------|------|-------|---------|
| **Framework_Composite_TrendWeather** | Composite | 1.155 | 19.3% | -14.2% | 2015-2026 |
| **EMA-Cross-Alpha** | Trend | 0.980 | 17.8% | -18.5% | 2015-2026 |
| **Portfolio-Optimization-ML** | Allocation | 0.896 | 15.2% | -12.8% | 2015-2026 |
| **EMATrend-Composite** | Composite | 0.870 | 14.5% | -16.3% | 2015-2026 |
| **EMA-Cross-Stocks** | Trend | 0.867 | 14.2% | -19.1% | 2015-2026 |
| **AllWeather** | Allocation | 0.670 | 8.5% | -15.2% | 2015-2026 |
| **SectorMomentum** | Momentum | 0.621 | 12.1% | -22.4% | 2015-2026 |
| **MomentumStrategy** | Momentum | 0.573 | 11.8% | -25.3% | 2015-2026 |
| **RegimeSwitching** | Regime | 0.553 | 10.2% | -18.7% | 2015-2026 |
| **FamaFrench** | Factoriel | 0.544 | 9.8% | -20.1% | 2015-2026 |

</div>

Echecs pedagogiques : PairsTrading (-0.36), ForexCarry (-0.32), InverseVolatility-Rank (0.12). Benchmark : SPY (Sharpe ~0.50).

---
layout: dense
---

# Panorama des Strategies (2/2) -- ML/AI

<div class="colored-table">

| Strategie | Modele ML | Sharpe | Ref Livre |
|-----------|----------|--------|-----------|
| **ML-Random-Forest** | Random Forest | 0.903 | Ch5 Ex09 |
| **XGBoost-Classification** | XGBoost | 0.571 | Ch5 |
| **MLP-Direction-Classifier** | MLP sklearn | 0.536 | Ch6 Ex15 |
| **RL-DQN-Trading** | DQN (MLPRegressor) | 0.529 | Ch7 Ex01 |
| **LSTM-Forecasting** | LSTM | 0.529 | Ch6 Ex14 |
| **Sector-ML-Classification** | RF Sectoriel | 0.410 | Ch6 Ex03 |
| **Markov-Regime-Detection** | HMM | 0.410 | Ch6 Ex04 |
| **Chronos-Foundation-Forecasting** | Chronos | 0.249 | Ch6 Ex18 |
| **SVM-Wavelet-Forecasting** | SVM + Wavelet | 0.150 | Ch6 Ex05 |

</div>

Modeles simples > complexes en finance : le bruit penalise les architectures sur-parametrees.

---
layout: compact
---

# Gestion du Risque - Introduction

- **"Rule #1: Never lose money. Rule #2: Never forget rule #1"** -- Warren Buffett
  - La gestion du risque est plus importante que la generation de signaux
  - Un drawdown de 50% necessite un gain de 100% pour revenir a l'equilibre
  - Asymetrie fondamentale : les pertes font plus de degats que les gains equivalents

<div v-click="1">

- **Maximisation de la Croissance** (formule fondamentale)
  - Objectif : maximiser la croissance **composee** (geometrique) du capital a long terme
  - Formule : g = m - s^2/2 (la croissance composee est REDUITE par la variance)
  - Implication contre-intuitive : reduire la variance augmente la croissance meme a rendement egal
  - Exemple : 10% rendement, 20% vol -> g = 8% ; 10% rendement, 40% vol -> g = 2%

</div>
<div v-click="2">

- **Eviter la Ruine** (la regle numero zero)
  - Drawdown : mesure de la pire chute depuis le dernier sommet (peak-to-trough)
  - Regle pratique : limiter le risque a 1-2% du capital par trade (position sizing)
  - Exemple du depot : `AllWeather` MaxDD -15% vs `MomentumStrategy` MaxDD -25%
  - La probabilite de ruine augmente exponentiellement avec le levier

</div>

---
layout: image-overlay
image: ./images/normal_distribution.png
imageClass: mid-right visible
---

# Outils et Formules de Gestion du Risque

- **Formule de Kelly** (John L. Kelly Jr., 1956, Bell Labs)
  - Determine la fraction optimale du capital a risquer par trade pour maximiser la croissance composee
  - f* = (p x b - q) / b
  - p = probabilite de gain, q = probabilite de perte (1-p), b = ratio gain/perte moyen
  - Utilisee par Ed Thorp (casino) puis adaptee aux marches financiers

<div v-click="1">

- **Value-at-Risk (VaR)**
  - Estime la perte maximale potentielle sur une periode avec un niveau de confiance
  - Exemple : VaR 95% journaliere = 2% signifie qu'on a 5% de chances de perdre plus de 2%
  - Methodes : historique, parametrique (gaussien), Monte Carlo
</div>
<div v-click="2">

- **Conditional Value-at-Risk (CVaR / Expected Shortfall)**
  - Estime la perte moyenne au-dela du VaR (dans les pires scenarios)
  - Plus conservateur que le VaR, prend en compte les "fat tails"
  - Prefere par les regulateurs (Bale III) car le CVaR est sous-additif (coherent)

</div>

---
layout: image-overlay
image: ./images/normal_distribution_pdf.png
imageClass: mid-right visible
---

# Exemple : Formule de Kelly en Pratique

- **Scenario typique d'une strategie quantitative**
  - Probabilite de gain (p) = 55%, Probabilite de perte (q) = 45%
  - Gains moyens = 2%, Pertes moyennes = 1.5%
  - Ratio gain/perte (b) = 2% / 1.5% = 1.33
  - Ce scenario est realiste : une bonne strategie gagne un peu plus souvent qu'elle ne perd

<div v-click="1">

- **Calcul pas a pas**
  - f* = (p x b - q) / b = (0.55 x 1.33 - 0.45) / 1.33
  - f* = (0.73 - 0.45) / 1.33 = **0.21 soit 21% du capital** par trade (Kelly plein)
  - Demi-Kelly : 10.5% -- recommande en pratique (marge de securite, parametres incertains)
  - Quart-Kelly : 5.25% -- pour les traders tres conservateurs
  - La plupart des fonds ne risquent que 1-5% par trade (beaucoup moins que Kelly)

</div>

---

# Formule de Kelly : Intuition et Limites

- **Theorie vs pratique**
  - Kelly maximise la croissance composee a long terme (geometrique, pas arithmetique)
  - Un sur-levier (miser plus que Kelly) garantit la ruine mathematique a long terme
  - La distribution normale sous-estime les evenements extremes ("fat tails")
<div v-click="1">

- **En pratique**
  - Les parametres p et b sont estimes avec erreur -> demi-Kelly plus sur
  - Ed Thorp (professeur + joueur de blackjack) a popularise Kelly dans les annees 1960-1970
  - La plupart des professionnels utilisent le **demi-Kelly** ou le **quart-Kelly**

</div>

---

# Gestion du Risque avec la Formule de Kelly

- **Gestion dynamique avec Kelly** (adapter f en temps reel)
  - Reduire la fraction f quand les pertes s'accumulent (Kelly adaptatif)
  - Recalculer p et b periodiquement (trimestriel) avec les donnees recentes
  - Si le Sharpe decline sous 0.3 sur 6 mois, basculer en mode defensif avant de toucher au modele
<div v-click="1">

- **Contagion Financiere** (risque systemique)
  - 2008 (Lehman) et 2020 (COVID) : tous les actifs baissent en meme temps
  - Diversifier entre classes decorreles, mais les correlations augmentent en crise

</div>
<div v-click="2">

- **Evenements Extremes (Black Swans, Nassim Taleb)**
  - Kelly ne prend pas en compte les "fat tails" (queues epaisses, kurtosis > 3)
  - Un evenement "6 sigma" arrive tous les 5-10 ans au lieu de 1x par 1.5M jours
  - Gestion : VaR, CVaR, stress testing, scenarios Monte Carlo

</div>
<div v-click="3">

- **Utilisation de Stop Loss**
  - Momentum : stop loss naturel (le signal change de direction)
  - Mean-Reversion : stop loss contre-productif (on vend au pire moment)
  - Notre depot : trailing stop 15% sur momentum, pas de stop sur mean-reversion

</div>

---

# Autres Types de Risques

- **Risque de Modele** (le risque que votre modele soit faux)
  - Biais de survie, biais de lookahead, et erreurs de donnees (garbage in, garbage out)
  - Changements structurels du marche : nouvelles reglementations, innovations technologiques
  - Exemple : une strategie entrainee pre-COVID echoue pendant le COVID (changement de regime)
  - Exemple : une strategie de carry FX qui marchait avant 2020 echoue apres (taux convergents)

<div v-click="1">

- **Risque Logiciel** (la machine peut se tromper aussi)
  - Bugs, latence et decalages de donnees (data feed delayed de quelques secondes)
  - Assurez-vous que le systeme de trading automatise est bien teste et surveille 24/7
  - Exemple celebre : Knight Capital (2012), bug de deploiement, perte de 440M$ en 45 minutes
  - Exemple : un off-by-one dans l'indice des donnees = look-ahead bias invisible

</div>
<div v-click="2">

- **Risques Physiques et Operationnels** (les risques "non-financiers")
  - Pannes de courant, defaillance du materiel, cyberattaques (ransomware)
  - Solution de secours obligatoire : serveurs redondants, plan de recuperation
  - Risque de liquidite : impossible de sortir d'une position pendant un flash crash (bid vide)
  - Risque de contrepartie : faillite du courtier (MF Global 2011 : 1.6Md$, FTX 2022 : 8Md$)
  - Risque reglementaire : changement de regles en cours de jeu (interdiction du short selling, etc.)

</div>

---

# Preparation Psychologique (1/2)

- **Emotions en Trading** (meme en algo, le trader doit gerer sa psychologie)
  - Overtrading en periode de gains : "je suis un genie, augmentons le levier"
  - Aversion au risque en periode de pertes : desactiver l'algo au pire moment (panic exit)
  - Tentation de modifier les parametres apres chaque perte (tweaking compulsif)
  - Le trading algorithmique ne supprime PAS l'emotion : il la deplace vers la supervision
  - Etude : 80% des traders retail perdent de l'argent, principalement a cause de biais psychologiques

<div v-click="1">

- **Biais Comportementaux** (Kahneman & Tversky, Prospect Theory, prix Nobel 2002)
  - **Effet de dotation** : surestimer ce qu'on possede deja (garder une position perdante trop longtemps)
  - **Aversion a la perte** : une perte de 1000$ fait 2x plus mal qu'un gain de 1000$ ne fait plaisir
  - **Biais de confirmation** : ne chercher que les preuves qui confirment notre these initiale
  - **Biais de representativite** : "la derniere fois que ca ressemblait a ca, le marche a monte"
  - **Ancrage** : fixer un "prix d'achat" mental qui influence irrationnellement les decisions de vente
  - **Illusion de controle** : croire qu'on peut predire le marche mieux que les autres

</div>

---

# Preparation Psychologique (2/2)

- **Le cycle emotionnel du trader** (Wall Street Cheat Sheet)
  - Euphorie -> Confiance -> Complaisance -> Anxiete -> Panique -> Capitulation -> Depression -> Espoir
  - Ce cycle se repete a chaque bulle et krach (dotcom 2000, subprimes 2008, crypto 2022)
  - Importance de la gestion du stress et de la psychologie pour ne pas suivre le cycle
  - Mettre en place des garde-fous automatiques pour eviter les decisions impulsives
<div v-click="1">

- **Conseils Pratiques** (du bon sens, mais difficile a appliquer)
  - Commencez petit : paper trading pendant 3 mois minimum
  - Ne jamais trader l'argent dont on a besoin (tampon financier obligatoire)
  - Tenir un journal de trading : decisions ET emotions (post-mortem regulier)
  - Regles de pause : apres 3 pertes consecutives, arreter pour la journee

</div>
<div v-click="2">

- **Avantage du trading algorithmique**
  - L'algo execute sans emotion, mais le trader doit resister a l'envie de le "debrancher"
  - Regle : definir les regles de supervision AVANT le deploiement (MaxDD, perte max/jour)
  - Arret automatique si regles violees : `MaximumDrawdownPercentPerSecurity`

</div>

---
layout: image-overlay
image: ./images/bollinger_bands.png
imageClass: mid-right visible
---

# Strategies de Moyenne Reversion

- **Moyenne Reversion** (concept fondamental en finance)
  - Les prix tendent a revenir vers une moyenne a long terme (hypothese d'Ornstein-Uhlenbeck)
  - Indicateurs : Bollinger Bands (a droite), z-score du spread, RSI en zone extreme
  - Signal : acheter quand le prix est "trop bas" (z-score < -2), vendre quand "trop haut" (> +2)
  - Fonctionne mieux sur les paires d'actifs co-integres que sur les actifs individuels
<div v-click="1">

- **Pieges courants** (pourquoi la mean-reversion est difficile)
  - Biais de Survie : actifs delistes faussent les resultats (ils ne "revertent" pas, ils disparaissent)
  - Co-integration necessaire (pas juste la correlation -- la correlation peut changer sans warning)
  - Plus une anomalie est connue, plus elle s'erode (alpha decay accelere par les ETFs smart-beta)
</div>

---

# Mean Reversion : Projets et Lecons

- **Projets du depot** (resultats backtestes 2015-2026)
  - `MeanReversion` (Sharpe 0.29) -- RSI mean-reversion classique sur actions US
  - `PairsTrading` (Sharpe -0.36) -- Echec pedagogique : co-integration instable dans le temps
  - `TrendFilteredMeanReversion` (Sharpe -0.02) -- Mean reversion + filtre SMA200
<div v-click="1">

- **Pourquoi les resultats sont modestes** (ce que nos backtests revelent)
  - La mean-reversion fonctionne sur des horizons courts (intraday, quelques jours) mais nos strategies operent en daily/weekly
  - Sur actions US : le momentum domine le mean-reversion depuis 2010 (marche haussier structurel)
  - Le pairs trading exige une co-integration stable, mais les relations entre actifs derivent (regime changes)
  - Le filtre SMA200 ajoute du "cash drag" : on est souvent hors-marche pendant les meilleures periodes

</div>
<div v-click="2">

- **Lecon** : la mean-reversion pure est plus adaptee au forex/crypto qu'aux actions US
  - Notebook : `QC-Py-11-Technical-Indicators.ipynb` | Alternative prometteuse : PCA Stat-Arb (livre Ex13)

</div>

> Ref: *Hands-On AI Trading* Ch6 Ex13 "PCA Stat-Arb" p.228

---
layout: image-overlay
image: ./images/macd_chart.png
imageClass: top-right visible
---

# Strategies Fondamentales de Momentum

- **Momentum** (anomalie la plus documentee en finance)
  - Un actif qui monte tend a continuer a monter
  - Jegadeesh & Titman (1993) : effet present 30+ ans apres
  - Le MACD est un indicateur classique de momentum
  - Principe : acheter les "gagnants" 3-12 mois, vendre les "perdants"
<div v-click="1">

- **Sources du momentum** (pourquoi ca marche)
  - Diffusion lente de l'information vers les prix
  - Comportement de troupeau (herding behavior)
  - Sous-reaction initiale puis sur-reaction tardive

</div>
<div v-click="2">

- **Risques specifiques du momentum**
  - "Momentum crash" : retournement brutal lors de
    changement de regime (mars 2009, aout 2023)
  - Quand le momentum s'arrete, les pertes sont rapides

</div>

---

# Momentum : Projets et Resultats

- **Projets du depot** (backtestes 2015-2026)
  - `EMA-Cross-Alpha` (Sharpe 0.98) -- croisement de moyennes mobiles optimise, notre meilleur alpha
  - `SectorMomentum` (Sharpe 0.62) -- rotation sectorielle avec momentum rank, diversifie
  - `MomentumStrategy` (Sharpe 0.57) -- momentum classique multi-actifs
  - `DualMomentum` (Sharpe 0.35) -- momentum absolu + relatif (Gary Antonacci)
<div v-click="1">

- **Ce que nos resultats confirment** (patterns recurrents)
  - Le momentum simple (EMA crossover) bat les approches plus sophistiquees sur nos donnees
  - La rotation sectorielle ajoute de la diversification mais reduit le Sharpe vs stock-picking
  - Le DualMomentum est plus defensif (meilleur MaxDD) mais sacrifie du rendement

</div>
<div v-click="2">

- **Lecon** : le momentum est la strategie la plus robuste historiquement, malgre les "crash risks"
  - Notebook : `QC-Py-13-Alpha-Models.ipynb`

</div>

> Ref: *Hands-On AI Trading* Ch6 Ex01 p.143 | Jegadeesh & Titman (1993)

---

# Strategies de Regime Switching (1/2)

- **Concept & Types de regimes**
  - Les Marches varient entre differents regimes qui changent les correlations et la volatilite
  - Regimes typiques : haussier/baissier, haute/basse volatilite, inflation/deflation, risk-on/risk-off
  - La Prediction de ces regimes est un defi majeur : les transitions sont rares et soudaines
  - Exemple : le passage au regime COVID (mars 2020) en quelques jours
<div v-click="1">

- **Outils & Approches - GARCH**
  - Modele "autoregressif conditionnellement heteroscedastique generalise"
  - Utile pour mesurer la volatilite, moins pour le prix d'actions
  - Projets : `RegimeSwitching` (Sharpe 0.55), `Markov-Regime-Detection` (Sharpe 0.41)
  - Notebook : `QC-Py-28-Market-Regime-Detection.ipynb`

</div>

> Ref: *Hands-On AI Trading* Ch6 Ex04 "Alpha by HMM" p.158 | Hamilton (1989)

---
layout: compact
---

# Strategies de Regime Switching (2/2)

- **Modeles probabilistes** (l'elite de la detection de regime)
  - **HMM** (Hidden Markov Models) : detectent les regimes latents (bull/bear/sideways)
  - **Filtre de Kalman** : estimation continue de l'etat cache du marche en temps reel
  - **GARCH a regimes** : volatilite conditionnelle qui change selon l'etat du marche
  - Necessite un modele de variables hypothetiques ou variables latentes
  - Tres puissant mais complexe a calibrer : choix du nombre d'etats, initialisation sensible

<div v-click="1">

- **Data Mining et signaux macro** (inputs du detecteur de regime)
  - Indicateurs techniques : VIX (peur), put/call ratio (couverture), breadth (participation)
  - Donnees macroeconomiques : PIB trimestriel, inflation CPI, taux directeurs Fed/BCE
  - Spreads de credit : OAS investment grade vs high yield (stress du marche obligataire)
  - "Buzz" mediatique et sentiment des reseaux sociaux (Twitter/X, Reddit, StockTwits)
</div>
<div v-click="2">

- **Application Pratique et limites**
  - Machine Learning pour detection en temps reel des changements de regime
  - Notre implementation : `RegimeSwitching` utilise un HMM a 3 etats (bull, bear, sideways)
  - `Markov-Regime-Detection` : approche bayesienne avec probabilites de transition
  - Attention aux pieges: biais de "data snooping" et optimisation excessive des seuils
  - La detection est souvent en retard de 2-4 semaines : le regime change avant le modele
  - Solution partielle : combiner regime detection + momentum pour reduire le retard

</div>

---

# Ponderations par le Volume et le Temps

- **VWAP - Volume Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le volume sur la journee
  - Utilisation: Frequemment utilise en trading institutionnel pour minimiser l'impact du marche
  - Mecanisme: Calcule le rapport cout/volume a des intervalles reguliers et execute des ordres en fonction
  - Un ordre est "bien execute" s'il bat le VWAP

<div v-click="1">

- **TWAP - Time Weighted Average Price**
  - Objectif: Obtenir un prix moyen pondere par le temps
  - Utilisation: Utilise lorsque l'impact du volume sur le prix est moins pertinent
  - Mecanisme: Divise un gros ordre en plus petits morceaux, executes a intervalles reguliers
  - Plus simple que VWAP, utile pour les marches peu liquides
</div>
<div v-click="2">

- **TWAP/VWAP sont les standards de l'execution institutionnelle**
  - Pour eviter un prix moyen trop deforme par un seul gros ordre (market impact)
  - QuantConnect Lean offre un `VolumeWeightedAveragePriceExecutionModel` natif
  - Dans le framework : c'est le role de l'**ExecutionModel** (separe de la strategie)
  - Pour un retail trader : les ordres sont assez petits pour que l'execution immediate suffise

</div>

---
layout: image-overlay
image: ./images/security_market_line.png
imageClass: top-right visible
---

# Strategies Basees sur les Donnees - Modeles Factoriels

- **Exposition Factorielle** (decomposer le rendement)
  - Sensibilite d'un actif aux facteurs systematiques
  - Macro : taux, inflation, PIB, credit spreads
  - Style : taille, valeur, momentum, quality
  - Fama-French (1992) : ~90% de la variance expliquee

<div v-click="1">

- **Rendement Factoriel & Specifique**
  - R(i) = alpha + beta1 x Market + beta2 x SMB
    &nbsp;&nbsp;+ beta3 x HML + epsilon
  - Factoriel = betas (exposition systematique)
  - Specifique = alpha + epsilon (idiosyncrasique)
  - Objectif : capturer l'alpha residuel apres controle
</div>

---

# Modeles Factoriels : Projets et Extensions

- **Facteurs classiques et extensions**
  - Fama-French : Market, Size (SMB), Value (HML) -- prix Nobel 2013
  - Extensions modernes : Momentum (UMD), Quality (QMJ), Low Volatility (BAB)
  - Aujourd'hui : les 5 facteurs Fama-French + momentum expliquent ~90% de la variance des portefeuilles
<div v-click="1">

- **Projets du depot** (resultats backtestes 2015-2026)
  - `FamaFrench` (Sharpe 0.54) -- Modele classique 3 facteurs, stable et comprehensible
  - `RiskParity` (Sharpe 0.40) -- Allocation par parite de contribution au risque (Bridgewater-style)

</div>
<div v-click="2">

- **Application pratique** (comment utiliser les facteurs dans vos strategies)
  - Les facteurs servent a decomposer votre alpha : votre strategie capte-t-elle du vrai alpha ou juste du beta deguise ?
  - Un Sharpe de 1.0 avec un beta de 1.5 est moins impressionnant qu'un Sharpe de 0.5 avec un beta de 0.3
  - Combiner facteurs + momentum est l'approche la plus robuste dans nos backtests
  - Notebook : `QC-Py-10-Risk-Portfolio-Management.ipynb`

</div>

> Ref: *Hands-On AI Trading* Ch8 p.327

---

# Strategies Basees sur les Donnees - Sentiment Analysis

- **Objectif** (l'alpha cache dans le texte non structure)
  - Exploiter les donnees textuelles non structurees pour predire les mouvements du marche
  - Hypothese : le sentiment du marche precede les mouvements de prix de 1 a 5 jours
  - Les donnees textuelles sont massives : des milliers de news par jour, des centaines d'earnings calls par trimestre
<div v-click="1">

- **Technologie** (evolution rapide du domaine)
  - Utilise des techniques de NLP (Natural Language Processing)
  - Analyse des textes tels que les nouvelles, les tweets, les transcriptions d'earnings calls
  - Evolution : bag-of-words (2010) -> Word2Vec (2015) -> BERT (2018) -> FinBERT (2020) -> GPT/Claude (2023+)

</div>
<div v-click="2">

- **Mecanisme et pipeline** (de la collecte au signal)
  - Le sentiment du marche est extrait des donnees textuelles (score continu de -1 a +1)
  - Le score de sentiment est utilise comme feature additionnelle pour generer des signaux
  - Pipeline : collecte texte -> preprocessing -> scoring NLP -> aggregation -> signal -> execution
  - Defis : bruit (faux positifs), latence (le marche reagit en minutes), sarcasme, jargon financier
</div>

---

# Sentiment Analysis : Utilisation Pratique

- **De l'academie a Wall Street** (le NLP comme avantage competitif)
  - Les hedge funds investissent massivement dans le NLP (Two Sigma, Citadel, Point72)
  - Datasets commerciaux : RavenPack, Bloomberg News Analytics, Thomson Reuters
  - En 2025 : les LLMs (GPT, Claude) permettent du zero-shot sans entrainement specifique
<div v-click="1">

- **Le pipeline concret pour un quant individuel**
  - Source gratuite : Tiingo News API (integree a QC) -- des milliers d'articles/jour
  - Scoring : FinBERT (pre-entraine, ~15% accuracy vs BERT generique) ou LLM via API
  - Signal : aggreger les scores sur une fenetre temporelle, filtrer le bruit (seuils)
  - Integration : le score de sentiment devient une feature parmi d'autres dans votre alpha

</div>
<div v-click="2">

- **Notebooks et references**
  - `QC-Py-17-Sentiment-Analysis.ipynb`, `QC-Py-18-ML-Features-Engineering.ipynb`
  - *Hands-On AI Trading* Ch6 Ex16 (LLM pipeline) + Ex19 (FinBERT)

</div>

---
layout: compact
---

# Strategies de Trading a Haute Frequence (1/2)

- **Principe : exploiter des micro-inefficacites a tres grande vitesse**
  - Profit par trade minuscule (< 0.01%) mais multiplie par des milliers/millions de trades/jour
  - Fournit de la liquidite au marche en echange d'un spread (market making HFT)
  - Represente 50-70% du volume quotidien sur les marches US (estimation SEC)
  - Types : market making, arbitrage statistique, arbitrage de latence, event-driven micro
<div v-click="1">

- **Ratio de Sharpe Eleve** (la loi des grands nombres en action)
  - Loi des grands nombres : des milliers de petits paris (quasi-)independants chaque jour
  - Sharpe annualise > 5 courant pour les firmes HFT (vs < 2 pour la plupart des strategies)
  - Volatilite du P&L tres faible sur une base journaliere (profit presque garanti par jour)
  - Exemple : Virtu Financial a eu 1 seul jour de perte en 1238 jours de trading (2009-2014)
  - Le HFT est le seul domaine ou le Sharpe est structurellement > 3 grace au volume de trades

</div>
<div v-click="2">

- **Difficultes et Defis** (pas pour les debutants)
  - Couts de transaction : a cette echelle, chaque centime de spread compte enormement
  - Course a la latence : difference de microsecondes = avantage competitif (winner-takes-all)
  - Risque de "flash crash" : pertes catastrophiques en quelques millisecondes si le modele deraille
  - Barrieres a l'entree colossales : infrastructure coutant des millions de dollars par an
  - Marche oligopolistique : domie par 5-10 firmes (Citadel Securities, Virtu, Jump Trading, etc.)

</div>

---

# Strategies de Trading a Haute Frequence (2/2)

- **Machine Learning et AI pour le HFT** (la frontiere technologique)
  - Utilisation de modeles de Deep Learning pour prediction de micro-tendances (tick-level)
  - Reinforcement Learning pour l'ajustement dynamique de strategies d'execution
  - Les modeles doivent etre ultra-rapides : inference en microsecondes (FPGA, ASIC)
  - Tendance : modeles de plus en plus legers (distillation, quantisation) pour la vitesse

<div v-click="1">

- **Latence Ultra-Faible** (la course aux microsecondes)
  - Utilisation de FPGA (Field-Programmable Gate Arrays) pour des ordres en < 1 microseconde
  - Co-location de serveurs dans le meme datacenter que la bourse (NYSE: Mahwah NJ, CME: Aurora IL)
  - Fibres optiques dediees, micro-ondes et lasers entre datacenters (Chicago-New York en 4ms)
  - Budget infrastructure : 10-100M$/an pour les firmes HFT majeures (Citadel Securities, Virtu, Jump)

</div>
<div v-click="2">

- **Risques et Reglementations**
  - Detection d'abus de marche (spoofing, layering) par des algorithmes de surveillance
  - Impact des regulations comme MiFID II (EU) et Reg NMS (US) sur la transparence
  - Debat ethique : le HFT ameliore-t-il (liquidite) ou degrade-t-il (flash crashes) la qualite du marche ?
  - Flash Crash du 6 mai 2010 : le Dow Jones a perdu 1000 points en 5 minutes puis s'est retabli
  - Note : le HFT n'est pas praticable dans notre cadre pedagogique (QC Cloud latence ~100ms)

</div>

---

# Strategies de Trading Saisonnier

- **Effet de Janvier** (l'effet saisonnier le plus etudie)
  - Petites capitalisations beneficient en janvier (tax-loss selling en decembre)
  - Vendre en decembre pour raisons fiscales, racheter en janvier = rally de janvier
  - Effet en diminution depuis les annees 2000 (trop connu, exploite par les ETFs)
  - Exemple US : le Russell 2000 surperformait le S&P 500 de ~2% en janvier (1980-2000)
<div v-click="1">

- **Strategies Mensuelles et "Turn of the Month"**
  - Acheter/vendre selon la performance du mois precedent (reversal mensuel)
  - "Sell in May and go away" : effet historique mais inconsistant depuis 2010
  - Turn of the Month : rendements plus eleves les 3 derniers + 3 premiers jours du mois
  - Explication : flux de liquidite des fonds de pension et paies en fin de mois

</div>
<div v-click="2">

- **Strategies Matieres Premieres** (ancrees dans la realite physique)
  - Essence et gaz naturel : saisonnalite liee aux saisons physiques (offre/demande reelle)
  - Fiable car base sur besoins economiques reels (petrole en ete = driving season, gaz en hiver = chauffage)
  - Aussi : cereales (saison de plantation/recolte), metaux (construction, saisonnier)
</div>

---

# Trading Saisonnier : Precautions et Projets

- **Precautions** (pourquoi les resultats sont faibles)
  - Biais de Data-Snooping : avec 252 jours de trading, on trouvera toujours un "pattern" par hasard
  - Les effets saisonniers purs generent peu d'alpha en 2025 (trop connus, trop exploites par les ETFs)
  - Les saisonnalites fonctionnent mieux comme **filtre additionnel** que comme strategie primaire
<div v-click="1">

- **Projets du depot** (resultats backtestes 2015-2026)
  - `TurnOfMonth` (Sharpe 0.13) -- Strategie calendaire pure, alpha quasi nul apres frais
  - `VIX-TermStructure` (Sharpe 0.05) -- Structure des termes VIX, Sharpe trop faible pour deployer

</div>
<div v-click="2">

- **Lecon** : nos backtests confirment la theorie -- les anomalies calendaires seules ne suffisent pas
  - Approche recommandee : utiliser la saisonnalite comme un filtre parmi d'autres (ex: eviter mai-septembre)
  - La VIX term structure reste un indicateur de regime utile, meme si elle ne genere pas d'alpha seule

</div>

---
layout: image-overlay
image: ./images/capital_market_line.png
imageClass: top-right visible
---

# Portefeuille a Haut Levier vs Haut Beta (1/2)

- **Beta** (sensibilite au marche)
  - Pente de la regression R(i) = alpha + beta x R(marche) + epsilon
  - Haut Beta (> 1.2) : amplifie les mouvements (tech, crypto)
  - Faible Beta (< 0.8) : amortit (utilities, healthcare)
  - Beta negatif : inverse du marche (or, VIX, puts)
  - Anomalie "low-beta" : faible beta = meilleur Sharpe

<div v-click="1">

- **Levier** (l'amplificateur a double tranchant)
  - Emprunter pour augmenter l'exposition au-dela du capital
  - Amplifie gains ET pertes proportionnellement
  - Risque de queue epaisse (distribution leptokurtique)
  - LTCM (1998) : levier x25, perte 4.6Md$ en 4 mois
  - Archegos (2021) : levier x5-10, perte 20Md$ pour les banques

</div>

---
layout: compact
---

# Portefeuille a Haut Levier vs Haut Beta (2/2)

- **Ratio de Sharpe et croissance composee** (la theorie de Markowitz)
  - Mesure le rendement ajuste au risque : SR = (R - Rf) / sigma
  - Croissance composee g = m - s^2/2 : proportionnelle au carre du ratio de Sharpe
  - Implication : un portefeuille a faible beta + levier peut battre un portefeuille a haut beta
  - C'est le fondement theorique de "Betting Against Beta" (Frazzini & Pedersen, 2014)
<div v-click="1">

- **Allocation d'Actifs** (la decision la plus importante en investissement)
  - Repartition du portefeuille entre differentes classes d'actifs (actions, obligations, matieres premieres)
  - Optimisation 23-77 : entre actions a faible beta et obligations pour un risque minimal (Markowitz)
  - Le "All-Weather" de Ray Dalio : 30% actions, 40% obligations longues, 15% obligations moyennes, 7.5% or, 7.5% matieres premieres

</div>
<div v-click="2">

- **Projets du depot** (resultats backtestes 2015-2026)
  - `AllWeather` (Sharpe 0.67, MaxDD -15%) -- "Toutes saisons" inspire de Ray Dalio, tres stable
  - `Portfolio-Optimization-ML` (Sharpe 0.90, MaxDD -13%) -- Optimisation ML, notre meilleur
  - `RiskParity` (Sharpe 0.40, MaxDD -12%) -- Allocation par parite de contribution au risque
  - Notebook : `QC-Py-21-Portfolio-Optimization-ML.ipynb`

</div>

---

# Lecons apprises : 10 patterns de nos 67 strategies

Ce que 67 backtests et 11 ans de donnees nous ont enseigne :

<div v-click="1">

1. **Biweekly rebalance** > weekly ou monthly (equilibre couts/reactivite)

</div>
<div v-click="2">

2. **SMA200 regime filter** reduit le beta mais cause du cash drag

</div>
<div v-click="3">

3. **Anti-overfitting** : `max_depth=5`, `min_samples=10` pour les arbres

</div>
<div v-click="4">

4. **Walk-forward** > cross-validation classique (ne jamais melanger futur/passe)

</div>
<div v-click="5">

5. **Modeles simples** (RF, XGBoost) > modeles complexes mal entraines (LSTM)

</div>
<div v-click="6">

6. **Backtest 2015-2026** = 11 ans couvrant bull, bear, COVID, hausse des taux

</div>
<div v-click="7">

7. **TLT risk-off** detruit la valeur post-2022 (obligations longues en hausse de taux)

</div>
<div v-click="8">

8. **Liquidation selective** > liquidation totale (reduire les positions risquees)

</div>
<div v-click="9">

9. **MLP sklearn** fonctionne sur QC Cloud (pas besoin de PyTorch/TensorFlow)

</div>
<div v-click="10">

10. **Un Sharpe de 0.5 stable** > un Sharpe de 2.0 instable

</div>

---

# Echecs pedagogiques : pourquoi certaines strategies echouent

*"L'experience, c'est le nom que chacun donne a ses erreurs."* -- Oscar Wilde. Documenter les echecs est aussi important que celebrer les succes.

<div v-click="1">

- **PairsTrading** (Sharpe -0.36) -- l'echec le plus instructif
  - La co-integration est instable dans le temps (fenetre de 2 ans insuffisante)
  - Ce qui marchait en 2010 ne marche plus en 2020 : les marches evoluent
  - La relation statistique entre deux actifs derive inexorablement
  - Test d'Engle-Granger positif en-sample, negatif hors-sample : piege classique

</div>
<div v-click="2">

- **ForexCarry** (Sharpe -0.32) -- victime du regime monetaire
  - La prime de carry s'est evaporee avec la convergence des taux G10 post-2020
  - Strategie structurellement cassee : quand tous les taux sont proches de zero, pas de carry
  - Meme apres la hausse des taux 2022-2024, le carry ne s'est pas retabli de facon stable

</div>
<div v-click="3">

- **InverseVolatility-Rank** (3 iterations -- exemple d'echec methodique)
  - v1 : MaxDD 54.7% -- drawdown inacceptable, allocation trop agressive
  - v2 : MaxDD 22.7% mais Sharpe negatif -- amelioration du risque, rendement toujours negatif
  - v3 : MaxDD 41%, Sharpe 0.12 -- plafond structurel confirme apres 3 iterations
  - Lecon : parfois l'hypothese de depart est fausse, il faut savoir abandonner

</div>

---
layout: compact
---

# Du ML classique au Deep Learning : timeline

<div v-click="1">

- **1990s** : Regression lineaire, facteurs Fama-French (1992)
  - Les premiers modeles quantitatifs systematiques (LTCM, DE Shaw, Renaissance)

</div>
<div v-click="2">

- **2000s** : SVM, arbres de decision, k-NN
  - Debut du machine learning applique a la finance, surtout en credit scoring

</div>
<div v-click="3">

- **2010s** : Random Forest, XGBoost, ensembles
  - Notre `ML-Random-Forest` (Sharpe 0.90) -- le meilleur ML du depot

</div>
<div v-click="4">

- **2015** : LSTM, RNN pour series temporelles
  - Notre `LSTM-Forecasting` (Sharpe 0.53) -- plus complexe, pas meilleur

</div>
<div v-click="5">

- **2018** : Transformers (Vaswani et al.), autoencoders variationnels
  - Revolution en NLP (BERT, GPT), debut d'application en finance pour le sentiment

</div>
<div v-click="6">

- **2023** : Foundation models (Chronos, TimesFM)
  - Notre `Chronos-Foundation-Forecasting` (Sharpe 0.25) -- prometteur mais immature

</div>
<div v-click="7">

- **2025** : LLMs pour sentiment, agents IA autonomes
  - Notre `QC-Py-26-LLM-Trading-Signals` -- la frontiere actuelle
  - Agents autonomes : observation -> raisonnement -> execution en boucle

</div>

Tendance claire : la complexite des modeles augmente mais le ratio signal/bruit des marches reste faible.

La question cle n'est pas "quel modele utiliser ?" mais "ai-je assez de signal dans mes donnees ?"

> "All models are wrong, but some are useful." -- George Box

---

# ML en pratique : le pipeline complet

Le livre *Hands-On AI Trading* structure le ML en finance en 5 etapes claires. Chaque etape a ses pieges specifiques.

<div v-click="1">

**1. Problem Definition** (Ch3) -- classifier la direction (up/down) plutot que predire le prix exact. Definir l'horizon.

</div>
<div v-click="2">

**2. Data Preparation** (Ch4) -- 80% du travail : EDA, outliers, feature engineering, normalisation, PCA. Attention aux fuites de donnees (data leakage).

</div>
<div v-click="3">

**3. Model Choice** (Ch5) -- commencer simple (RF avant LSTM). Plus de parametres != meilleur modele.

</div>
<div v-click="4">

**4. Applied ML** (Ch6) -- 19 exemples concrets du trend scanning (Ex01) au FinBERT (Ex19), tous dans le depot QC.

</div>
<div v-click="5">

**5. Validation** -- walk-forward (respecter la chronologie), split 60/20/20, out-of-sample obligatoire.

</div>

> Ref: *Hands-On AI Trading* Part II (Ch3-5) | Notebooks: QC-Py-18, QC-Py-19

---
layout: two-cols
---

# Feature Engineering pour le trading

**Features qui marchent :**

- **Techniques** : RSI(14), MACD(12,26,9), Bollinger %B(20), ATR(14), volume ratio 5j/20j
- **Momentum** : Returns 5j/10j/20j, momentum rank cross-sectionnel, MACD signal
- **Volatilite** : Realized vol 20j/60j, vol ratio (court/long), Garman-Klass
- **Fondamentales** : P/E, revenue growth, free cash flow %, debt/equity
- **Sentiment** : News score NLP, earnings call tone (LLM), put/call ratio
- **Macro** : VIX, spread 10Y-2Y, credit spreads, PMI

::right::

<div style="padding-top: 3em;">

**Features qui ne marchent PAS :**

- Prix absolu (non stationnaire)
- Volume brut (non normalise)
- Indicateurs sans normalisation
- Trop de features (curse of dimensionality)
- Features correlees sans PCA
- Donnees du futur (look-ahead bias)

**Regle d'or** : toute feature doit etre stationnaire (rendements, pas prix) et disponible au moment de la decision (pas de look-ahead).

</div>

> Ref: *Hands-On AI Trading* Ch4 "Feature Engineering" p.61-65 | Notebook: QC-Py-18-ML-Features-Engineering
> Voir aussi: Ch4 "PCA and Dimensionality Reduction" p.68-72 pour reduire les features correlees

---
layout: compact
---

# Reinforcement Learning pour le trading

<div v-click="1">

- **1. L'agent observe** l'etat du marche (state representation)
  - Features techniques (RSI, MACD, Bollinger %B) + fondamentales (P/E, volume)
  - Fenetre glissante de 20 jours (~60 features)

</div>
<div v-click="2">

- **2. Choisit une action** parmi les allocations (discrete action space)
  - AGGRESSIVE (80/20) / MODERATE (50/50) / DEFENSIVE (20/80)
  - Exploration epsilon-greedy : 1.0 -> 0.01 sur 1000 episodes
  - DQN : reseau de neurones approximant la Q-function

</div>
<div v-click="3">

- **3. Recoit une recompense** basee sur le rendement risk-adjusted
  - Sharpe ratio glissant (30 jours), replay buffer de 5000 experiences

</div>
<div v-click="4">

- **Notre implementation** : `RL-DQN-Trading` (Sharpe 0.53)
  - MLPRegressor(64, 32) -- reseau simple, efficace sur QC Cloud (pas de GPU)
  - Surpasse une allocation statique 60/40

</div>
<div v-click="5">

- **Limites du RL en finance**
  - Environnement non-stationnaire, signal de recompense retarde et bruite
  - Plus prometteur pour l'execution (VWAP adaptatif) que pour les signaux

</div>

> Ref: *Hands-On AI Trading* Ch7 "Better Hedging with RL" p.281-303 | Notebook: QC-Py-25-Reinforcement-Learning

---

# LLMs et GenAI pour le trading

<div v-click="1">

- **Sentiment en temps reel** (la killer app des LLMs en finance)
  - Analyser earnings calls, tweets, rapports analystes
  - Detecter les changements de ton avant que le marche ne reagisse

</div>
<div v-click="2">

- **Extraction structuree et generation de signaux**
  - Transformer des 10-K SEC (~200 pages) en features quantitatives automatiquement
  - Scoring de confiance base sur l'analyse linguistique (tone shift analysis)

</div>
<div v-click="3">

- **FinBERT** : Modele pre-entraine sur texte financier (Prosus AI)
  - +5-10% accuracy vs BERT generique, entraine sur 47K phrases Reuters
  - **OpenAI / Claude** : Zero-shot classification, pas besoin d'entrainement
  - Livre Ex16 (LLM pipeline) + Ex19 (FinBERT) : implementations completes

</div>
<div v-click="4">

- **Limites et perspectives**
  - Cout API (~0.01$/appel), latence (2-10s, inadapte au HFT), hallucinations
  - Perspective 2026 : agents IA autonomes qui observent, raisonnent et executent

</div>

> Ref: *Hands-On AI Trading* Ch9 p.341-360, Ch6 Ex16+Ex19 | Notebook: QC-Py-26-LLM-Trading-Signals

---

# Synthese Partie 2 : ce qu'il faut retenir

Les marches financiers sont un environnement hostile pour les modeles : bruit eleve, regimes changeants, et concurrence feroce. Voici les cles de survie :

- **Backtesting** : indispensable, mais attention aux biais (look-ahead, survie, data-snooping)
  - Toujours valider out-of-sample, walk-forward, et comparer au benchmark
<div v-click="1">

- **Gestion du risque** : plus importante que la generation de signaux
  - Kelly (dimensionnement), VaR/CVaR (monitoring), stop loss (protection), diversification
</div>
<div v-click="2">

- **Strategies classiques** : mean-reversion (difficile), momentum (robuste), factoriel (stable)
  - Le momentum est l'anomalie la plus persistante de la finance moderne
</div>
<div v-click="3">

- **ML/AI** : les modeles simples surperforment souvent les complexes en finance
  - RF (Sharpe 0.90) > LSTM (0.53) > Chronos (0.25) -- le bruit penalise la complexite
</div>
<div v-click="4">

- **LLMs** : frontiere actuelle pour le sentiment et l'extraction de features textuelles
  - FinBERT, GPT, Claude : zero-shot possible, mais cout API et latence a considerer
</div>
<div v-click="5">

- **Lecon principale** : documenter les echecs, valider out-of-sample, garder les modeles simples
  - 67 projets backtestes dans ce depot : la meilleure facon d'apprendre est de pratiquer
  - Prochaine etape : mise en pratique sur Lean/QuantConnect dans le Deck 3
</div>

---
layout: section
---

# Suite : Pratique avec Lean/QuantConnect

Deck 3
