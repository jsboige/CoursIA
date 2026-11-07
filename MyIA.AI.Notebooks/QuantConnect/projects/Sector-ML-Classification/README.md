# Sector ML Classification

**Statut** : stratégie de recherche, mesurée sur QC Cloud le 2026-11-04 (voir [Résultats mesurés](#résultats-mesurés)). Point de départ : le chapitre de classification ML de *Hands-On AI Trading*.

## Description

Rotation sectorielle pilotée par un classifieur Random Forest. Pour chacun des huit ETF sectoriels SPDR de l'univers, le modèle estime la probabilité que le rendement des 10 séances suivantes dépasse +1,2 %. L'algorithme détient à poids égaux les secteurs les mieux classés, et se replie sur les secteurs défensifs quand SPY passe sous sa moyenne mobile à 200 jours.

### Univers

| Ticker | Secteur | Défensif |
|--------|---------|----------|
| XLK | Technologie | |
| XLF | Finances | |
| XLV | Santé | oui |
| XLE | Énergie | |
| XLY | Consommation discrétionnaire | |
| XLP | Consommation de base | oui |
| XLI | Industrie | |
| XLU | Services publics | oui |

SPY sert de référence (`set_benchmark`) et de filtre de régime ; il n'est jamais détenu.

### Fonctionnement

- **Régime** : le marché est baissier quand SPY clôture sous sa SMA 200.
- **Rééquilibrage bimensuel**, 30 minutes après l'ouverture : premier jour de bourse du mois, puis quatorze séances plus tard (`month_start("SPY", 14)`).
- **Marché haussier** : les 4 secteurs à plus forte probabilité de la classe BUY.
- **Marché baissier** : seuls XLU, XLP et XLV sont notés. L'algorithme garde les 2 premiers, ou passe entièrement en liquidités si la meilleure probabilité est inférieure à 0,35.
- **Allocation** : poids égaux ; seules les lignes sorties de la sélection sont liquidées.
- **Réentraînement mensuel**, le premier jour de bourse du mois, 60 minutes après l'ouverture. La fenêtre d'entraînement se termine 15 jours avant la date du réentraînement et remonte de `TRAIN_LOOKBACK_DAYS = 252 * 4` jours. Cette valeur est passée à `timedelta` en jours calendaires : la fenêtre couvre donc environ 2,8 ans, et non les 4 ans qu'annonce le commentaire du code. Un échantillon est tiré toutes les 5 séances.
- **Modèle** : `RandomForestClassifier(n_estimators=100, max_depth=5, min_samples_leaf=10, random_state=42)` après un `StandardScaler`. La graine est fixée : deux exécutions du même code sur les mêmes données donnent les mêmes ordres.
- **Chauffe** : 220 jours.

### Variables (11)

- rendements sur 5, 10, 20 et 50 séances (4 variables) ;
- volatilité des rendements quotidiens sur 20 séances ;
- RSI 14 normalisé, `(RSI - 50) / 50` : l'indicateur `RSI` de QC (lissage de Wilder) en prédiction, une moyenne glissante simple des hausses et des baisses à l'entraînement ;
- rapport SMA 20 / SMA 50 ;
- position du prix dans le range des 20 dernières séances ;
- rapport du prix au plus haut sur 52 semaines ;
- rendement relatif à SPY sur 5 et 10 séances (2 variables).

### Étiquettes

Rendement des 10 séances suivantes : classe 2 (BUY) au-dessus de +1,2 %, classe 0 (AVOID) sous -0,8 %, classe 1 (HOLD) entre les deux. Seule la probabilité de la classe 2 sert au classement.

## Résultats mesurés

Backtests QC Cloud du 2026-11-04, fenêtre codée 2015-01-01 → 2024-12-31, capital de départ 100 000, modèle de courtage et type de compte du code (`set_brokerage_model`, compte sur marge), paramètres par défaut. Les deux bras de la stratégie ne diffèrent que par le calcul du RSI d'entraînement.

| Bras | Backtest | Sharpe (QC) | CAGR | Pire baisse | Ordres |
|------|----------|-------------|------|-------------|--------|
| Code actuel, RSI d'entraînement corrigé (#23329) | `7ae7eab21fb1455fa56f4f051d714ed0` | 0,382 | 9,57 % | 35,3 % | 1033 |
| Code d'avant #23329, RSI d'entraînement constant | `c9ba4426833348253d1b31b2285b99a3` | 0,46 | 11,20 % | 35,3 % | 1024 |
| Témoin : SPY détenu seul | `6c2bce7882ff4af927e3bd67fc84847b` | 0,535 | 12,99 % | 33,5 % | 1 |

**Lecture.** Sur cette fenêtre, aucun des deux bras ne fait mieux que SPY détenu seul : le code actuel rend un Sharpe de 0,382 et un CAGR de 9,57 %, contre 0,535 et 12,99 % pour le témoin, avec une pire baisse plus profonde (35,3 % contre 33,5 %). Le correctif du RSI d'entraînement (#23329) n'améliore pas la mesure : le bras d'avant, dont la variable RSI était constante à l'entraînement, rendait un Sharpe de 0,46 et un CAGR de 11,20 %. Rendre au modèle une variable informative ne suffit donc pas ici. L'écart entre les deux bras (une variable sur onze) est mesuré sur une seule fenêtre et une seule graine : ce n'est pas une preuve que la variable nuit. Le Sharpe est celui que calcule QC, taux sans risque déduit. Ces chiffres décrivent une stratégie de recherche ; ils ne valent pas recommandation.

L'historique de la docstring de `main.py` (v2b à v5) est un journal d'itération : il a été mesuré sur des fenêtres (2015-2026, 2018-2026 pour v2b) qui ne sont plus celle du code, avant le correctif du RSI. Le code actuel ne le reproduit pas.

## Fichiers

- `main.py` : algorithme QC (classifieur Random Forest, filtre de régime SMA 200).
- `research.ipynb` : carnet de recherche (features, étiquettes, entraînement, simulation sur 2023-2025, analyse des secteurs retenus).
- `test_historical_rsi.py` : tests du RSI d'entraînement, sans moteur QC (`python -m unittest test_historical_rsi` depuis le dossier du projet).
- `config.json` : configuration du projet.

## Références

- **Livre** : *Hands-On AI Trading* (chapitre ML Classification).
- **Carnet associé** : QC-Py-19-ML-Supervised-Classification.ipynb.
