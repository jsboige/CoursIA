# Crypto LSTM Prediction

**Statut** : 🔄 Phase de recherche — basé sur le livre HandsOnAITrading.

## Description

Sélection d'actifs crypto par **ranking cross-sectionnel** (Broad Ch8, *Hands-On AI Trading*) : prédire quel actif surperforme l'autre à J+1 (BTC vs ETH), et non un prix absolu. Deux modèles PyTorch sont comparés : DLinear et LSTM.

### Caractéristiques principales

- **Architecture DLinear** (AAAI 2023) : décomposition ultra-simple + couches linéaires, comparée à un LSTM de référence
  - Bloc SeriesDecomposition (séparation tendance/saisonnalité par moyenne mobile)
  - Pas de mécanisme d'attention — version shared-channel : 122 paramètres exactement (deux `nn.Linear(60, 1)`, calculable depuis la classe du notebook)
  - Performance SOTA en prévision de séries temporelles

- **Implémentation PyTorch** : stack Deep Learning complète
  - Dataset et DataLoader personnalisés
  - Module SeriesDecomposition
  - Modèle DLinear (prévision tendance + saisonnière)

- **Cible** : ranking cross-sectionnel BTC vs ETH (`y = 1` si BTC surperforme ETH à J+1, classification binaire)

## Architecture

```
Input → SeriesDecomposition → [Trend, Seasonal] → DLinear → Prediction
         (Moving Avg)
```

### Composants du modèle DLinear

1. **SeriesDecomposition** : décompose la série temporelle en composantes tendance et saisonnières
2. **Couche linéaire de tendance** : projette les features de tendance
3. **Couche linéaire saisonnière** : projette les features saisonnières
4. **Reconstruction** : combine les prédictions tendance + saisonnière

## Fichiers

- `main.py` : algorithme QC avec intégration du modèle PyTorch
- `research.ipynb` : notebook de recherche avec entraînement et évaluation du modèle
- `_generate_research.py` : script qui régénère `research.ipynb` (les cellules sont écrites dans le script, il ne lit pas `main.py`)
- `config.json` : configuration du projet
- `README.en.md` : version anglaise du README

## Le code d'origine ne passait aucun ordre (#23563)

Jusqu'à #23563, `main.py` ne pouvait passer aucun ordre, sur aucune fenêtre. Quatre verrous indépendants l'en empêchaient, et chacun suffisait à lui seul.

1. **La planification lève une erreur d'exécution.** `Rebalance` et `CheckRetrain` sont planifiés avec `TimeRules.AfterMarketOpen`. Un actif crypto est coté en continu et n'a pas d'ouverture. Sur QC Cloud, le backtest s'arrête dès le début du préchauffage (« Unable to locate next market open within two weeks »), sans statistique ni ordre. C'est le verrou qui se déclenche en premier.
2. **L'entraînement lève à la première passe.** Les séquences d'entrée ont la forme (N, 60, 11) ; le code y ajoute un axe et obtient (N, 60, 11, 1), alors que `DLinear` et `SimpleLSTM` sont construits pour une seule série. L'exception est attrapée, et le modèle reste non entraîné.
3. **La séquence d'inférence est toujours trop courte.** `build_sequence` demande 70 barres, mais ne construit des vecteurs qu'à partir de la 50ᵉ : au plus 20 vecteurs, pour 60 exigés.
4. **La prédiction lève aussi**, sur la même forme à quatre axes.

Le code d'origine visait aussi une autre stratégie que celle de ce README et de `research.ipynb` : il ne tradait que BTC, sur une cible binaire de hausse de 1 % entraînée avec une perte quadratique, puis lue comme un rendement.

## Portage du classement BTC/ETH (paramètre `fix`)

Le paramètre `fix` choisit le code exécuté. `fix=off` exécute le code d'origine, inchangé ; il sert de témoin. `fix=on` (par défaut) porte dans `main.py` le design de `research.ipynb`, qui fait foi :

- 26 variables journalières : 11 pour BTC, 11 pour ETH, 4 croisées, calculées comme dans le carnet ;
- une séquence de 60 jours qui s'arrête à la clôture t ; la cible vaut 1 si le rendement de BTC dépasse celui d'ETH de t à t+1 ;
- `DLinear` (canaux partagés, 122 paramètres) ou `SimpleLSTM` (paramètre `model`), perte `BCEWithLogitsLoss`, Adam, 20 époques ;
- entraînement initial sur l'historique depuis 2017, puis réentraînement tous les 90 jours en fenêtre croissante ; le modèle n'est remplacé qu'après un entraînement réussi ;
- chaque jour, à l'arrivée des barres journalières de t (00:00 UTC, clôture journalière de Binance) : 98 % en BTC si la probabilité dépasse 0,5, 98 % en ETH sinon. La décision part de `OnData` : l'ordre se remplit à l'instant, au cours de t, et la position encaisse le rendement de t à t+1 que le modèle prédit. Le changement de ligne vend d'abord, puis achète sur des liquidités déjà créditées. Un compteur `invalid_orders` (statistique d'exécution) compte les ordres refusés ; un run sain l'a à 0.

Le portage n'utilise pas l'Object Store : ses clés sont partagées entre tous les projets, et un modèle chargé d'un autre run aurait vu le futur.

Le carnet ne prédit pas tout à fait J+1 : sa séquence s'arrête à la ligne i−1, et sa cible compare les rendements de i+1 à i+2. Le portage suit l'intention écrite (« BTC surperforme ETH à J+1 »), c'est-à-dire le rendement que l'algorithme encaisse. L'écart du carnet est suivi en #23564.

## Mesure (#23563)

Le protocole est fixé dans #23563 avant toute lecture de résultat. Il reprend la règle de #23012 :

- backtests QC Cloud, compte cash Binance, 100 000 USDT au départ, frais Lean ;
- modèle `dlinear` sur quatre graines (0, 1, 7, 42) ;
- trois références : BTC détenu, ETH détenu et 50/50 rééquilibré chaque mois.

Les deux fenêtres exécutent le même `main.py` (sha256 `c6aa416e237a…`). Il ne diffère de celui de ce dossier que par un mot de docstring, corrigé après la mesure (« deuxième passage »).

Le Sharpe « taux nul » se calcule sur la valeur du portefeuille relevée chaque jour, annualisé par √365. Le Sharpe QC est celui des statistiques du backtest. Les colonnes profit net, drawdown et ordres sont lues dans les statistiques QC. Les frais sont rapportés à la valeur moyenne du portefeuille, par an. La significativité de l'écart de Sharpe vient de `Paradox46Benchmarks/significance.py` : Ledoit-Wolf, bootstrap stationnaire, puis correction de Holm sur les deux références. Aucun paramètre n'a été réglé après lecture.

**Fenêtre w1 : du 2021-01-01 au 2026-03-01 (1886 jours)**

| Bras | Sharpe taux nul | Sharpe QC | Profit net | Drawdown max | Ordres | Frais / an | Jours BTC / ETH |
|---|---|---|---|---|---|---|---|
| graine 0 | 0,533 | 0,594 | 114,5 % | 81,0 % | 381 | 7,1 % | 1476 / 411 |
| graine 1 | 0,448 | 0,480 | 61,9 % | 83,1 % | 425 | 7,8 % | 1406 / 481 |
| graine 7 | 0,470 | 0,509 | 75,0 % | 81,4 % | 413 | 7,8 % | 1383 / 504 |
| graine 42 | 0,512 | 0,564 | 100,6 % | 80,3 % | 417 | 8,0 % | 1440 / 447 |
| BTC détenu | 0,554 | 0,615 | 131,3 % | 75,8 % | 1 | < 0,1 % | — |
| ETH détenu | 0,630 | 0,789 | 173,7 % | 79,0 % | 1 | < 0,1 % | — |
| 50/50 mensuel | 0,642 | 0,761 | 201,4 % | 75,2 % | 126 | 0,1 % | — |

**Fenêtre w2 : du 2026-03-01 au 2026-10-29 (244 jours)**

| Bras | Sharpe taux nul | Sharpe QC | Profit net | Drawdown max | Ordres | Frais / an | Jours BTC / ETH |
|---|---|---|---|---|---|---|---|
| graine 0 | 0,804 | 0,853 | 17,3 % | 27,7 % | 53 | 7,8 % | 213 / 31 |
| graine 1 | 0,927 | 1,016 | 20,7 % | 27,9 % | 57 | 8,4 % | 214 / 30 |
| graine 7 | 1,016 | 1,153 | 23,7 % | 29,3 % | 53 | 7,8 % | 210 / 34 |
| graine 42 | 0,990 | 1,119 | 23,3 % | 26,2 % | 65 | 9,7 % | 208 / 36 |
| BTC détenu | 0,845 | 0,900 | 18,0 % | 28,1 % | 1 | 0,1 % | — |
| ETH détenu | 0,675 | 0,739 | 15,7 % | 34,5 % | 1 | 0,1 % | — |
| 50/50 mensuel | 0,769 | 0,832 | 17,5 % | 30,6 % | 16 | 0,2 % | — |

Sur toutes les graines et les deux fenêtres, les compteurs d'exécution sont propres : 0 ordre refusé, 0 jour avec une seule des deux barres, 0 échec d'entraînement. Le modèle a été entraîné 21 fois sur w1 et 3 fois sur w2.

**Verdict, selon la règle de #23563 : NO BEATS sur w1, INCONCLUSIVE sur w2.**

- **w1.** Les quatre graines ont un Sharpe sous celui de BTC détenu : 0,448 à 0,533, contre 0,554. Le 50/50 mensuel fait mieux que toutes (0,642).
- **w2.** La graine 0 reste sous BTC détenu. Les graines 1, 7 et 42 le dépassent (0,927 à 1,016, contre 0,845), mais aucun écart n'est significatif. Contre BTC détenu, la p-value bilatérale de Ledoit-Wolf va de 0,39 à 0,61, et la p-value de Holm vaut 1 partout. Sur 244 jours, des séries corrélées entre 0,98 et 0,99 avec BTC détenu ne se départagent pas.

Deux constats expliquent l'écart avec les références :

- **Le modèle reste surtout en BTC** : 73 à 78 % des jours sur w1, 85 à 88 % sur w2. Le classement ressemble donc à BTC détenu, avec 37 à 49 changements de ligne par an.
- **Chaque changement coûte deux ordres.** Les frais montent à 7 à 10 % de la valeur moyenne par an, contre 0,1 à 0,2 % pour le 50/50. Sur w1, ils pèsent au moins autant que l'écart de rendement annuel composé avec BTC détenu (1,7 à 7,8 points). La mesure ne dit pas si un écart subsisterait sans frais : ce bras n'a pas été mesuré.

`SimpleLSTM` (`model=lstm`) n'est pas mesuré : le verdict ne porte que sur `DLinear`.

## Référence

- **Paper** : « Are Transformers Effective for Time Series Forecasting? » (AAAI 2023)
- **Livre** : Hands-On AI Trading (chapitre Deep Learning)
- **Notebook associé** : QC-Py-22-Deep-Learning-LSTM.ipynb

## Statut

Projet de recherche. Le classement BTC/ETH porté depuis `research.ipynb` est mesuré sur QC Cloud (section « Mesure ») : NO BEATS sur 2021-2026, INCONCLUSIVE sur la fenêtre récente.

---

**Note** : les marchés crypto sont très volatils. Cette stratégie est à but éducatif.
