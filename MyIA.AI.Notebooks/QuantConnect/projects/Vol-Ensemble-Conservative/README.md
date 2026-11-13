# Vol-Ensemble-Conservative

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** `33248352` (voir `config.json`, local-id : `209093652`)

## Description

Ensemble conservateur de prévision de volatilité combinant les modèles GARCH(1,1) et HAR-RV sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Utilise le maximum des deux prévisions de volatilité (approche conservatrice). Cible 8 % de volatilité annualisée (la moitié de la cible normale de 16 %). Applique un filtre de régime SMA200 avec réduction de position de 50 % en marché baissier, et une SMA50 pour la direction des trades. Rebalance hebdomadaire. La plus conservatrice des trois stratégies de volatilité.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Vol-Ensemble-Conservative/main.py
```

### QC Cloud
Ouvrir le projet cloud (project-id : `33248352`), compiler et lancer un backtest.

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Ensemble GARCH+HAR (max conservateur) | Hebdomadaire | Vol target 8 %, régime SMA200 (-50 % baissier), direction SMA50, fenêtre 500 jours |

### Baseline alignée (2018-2025)

Exécution dorsale standardisée #1630 (projet QC Cloud `33248352`, backtest `db77ae49`).

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.265 |
| CAGR | 6.142 % |
| Max Drawdown | 10.40 % |
| Probabilistic Sharpe Ratio | 13.6 % |
| Dates négociables | 1761 |

Interprétation : MaxDD 10.40 % = baseline dorsale la plus serrée à ce jour (bat Vol-GARCH-Target 10.80 %, GlobalMacro-Regime 22.8 %, HAR-RV-J-Kelly 37.1 %). Sharpe positif 0.265 mais inférieur au GARCH seul Vol-GARCH-Target (0.325) : l'overlay conservateur (prévision max-de-l'ensemble HAR+GARCH, demi vol-target 8 %, régime SMA200 -50 % baissier, direction SMA50) a serré le drawdown au prix du rendement, et la composante HAR n'a pas apporté de valeur ajustée du risque au-delà du GARCH seul. Promue Tier 4 -> 2 (Historique). totalOrders = 0 = artefact d'extraction du wrapper (CAGR 6.14 % implique des trades réels).

## Mesure contre des références détenues (#26322)

`main.py` est mesuré contre deux références détenues — SPY détenu et le 60/40 (SPY 60 %, BND 40 %) — et deux diagnostics : `ew6` (les six ETF de l'univers à poids égal) et `noregime` (la même règle sans le filtre de régime SMA200). Le protocole est écrit dans #26322 avant le premier backtest ; le paramètre `mode` ajoute ces exécutions sans toucher la décision de la stratégie. Tous les backtests tournent sur les nœuds QC le même jour (2026-11-13, compile de la tête `1d12269`). Les tests viennent de `Paradox46Benchmarks/significance.py`, à taux sans risque nul : écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire et écart de moyennes de Newey-West.

- **Verdict.** Il compare la stratégie à SPY détenu et au 60/40, avec une correction de Holm sur six p-valeurs. `BEATS` exige un écart de Sharpe positif et une p de Holm (Ledoit-Wolf) inférieure à 0,05 contre les deux références. `NO BEATS` signifie un Sharpe inférieur à celui de SPY détenu. Tous les autres cas sont `INCONCLUSIVE`.
- **Diagnostic.** `ew6` et `noregime` passent dans une exécution séparée, avec Holm sur six p-valeurs. `ew6` demande si le vol-targeting d'ensemble apporte quelque chose à la détention de l'univers à poids égal ; `noregime`, si le filtre SMA200 améliore la stratégie. Ils ne changent pas le verdict.

**Contrôle d'innocuité : tenu.** Sur la fenêtre codée, le code instrumenté (backtest `8e7e531a`) et le code d'origine (`28f542c7`, lancé le même jour) produisent 884 ordres chacun, 1761 dates négociables chacun, et des statistiques identiques au centime : Sharpe 0,27, CAGR 6,148 %, drawdown 10,400 %, PSR 0,933 %, profit net $50 485,89, équité finale $151 875,62, frais −$1 508,92. L'identité vérifiée est celle des compteurs et des statistiques ; le diff ordre par ordre n'a pas été extrait.

**Fenêtres.** La stratégie n'investit qu'après avoir accumulé 500 rendements ; son préchauffage de 250 séances en fournit la moitié. La trace de la fenêtre 1 reste à $100 000 pendant 251 séances : son premier mouvement date du 2019-01-02. Toute l'année 2018 passe donc en liquidités, quand SPY détenu y perd 7,0 % et le 60/40 3,7 % (mesurés sur les traces). Cette année compte dans la mesure : elle épargne à la stratégie la baisse de 2018, et ses séances à rendement nul pèsent dans son Sharpe.

- **Fenêtre 1** : 2018-01-02 → 2024-12-31, 1761 séances.
- **Fenêtre 2** : 2025-01-02 → 2026-06-30, 373 séances sur la trace (QC rapporte 374 dates négociables) ; la fin effective a été lue sur la trace.

Sharpe annualisé de la trace `shadow`, taux sans risque nul. L'écart est celui de la stratégie moins la référence.

| Fenêtre | Séances | Stratégie | SPY détenu (écart, p LW, p Holm) | 60/40 (écart, p LW, p Holm) | Verdict |
|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | 1761 | 0,783 | 0,744 (+0,039 ; 0,920 ; 1,0) | 0,742 (+0,042 ; 0,916 ; 1,0) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-06-30 | 373 | 0,847 | 0,983 (−0,136 ; 0,887 ; 1,0) | 1,137 (−0,290 ; 0,762 ; 1,0) | `NO BEATS` |

Diagnostics `ew6` et `noregime`, même convention, exécution séparée. La corrélation est celle des rendements journaliers.

| Fenêtre | Mode | Sharpe trace | Corrélation | Écart | p LW | p Holm |
|---|---|---|---|---|---|---|
| 2018 → 2024 | `ew6` | 0,527 | 0,625 | +0,256 | 0,453 | 1,0 |
| 2018 → 2024 | `noregime` | 0,844 | 0,989 | −0,061 | 0,217 | 0,867 |
| 2025 → 2026-06 | `ew6` | 1,813 | 0,555 | −0,965 | 0,215 | 1,0 |
| 2025 → 2026-06 | `noregime` | 0,867 | 0,998 | −0,020 | 0,570 | 1,0 |

Volatilité annualisée, rendement annualisé et drawdown maximal des mêmes traces :

| Mode | Fenêtre | Volatilité | Rendement annualisé | Drawdown max |
|---|---|---|---|---|
| stratégie | 2018-2024 | 8,1 % | 6,2 % | 10,4 % |
| SPY détenu | 2018-2024 | 19,4 % | 13,4 % | 33,7 % |
| 60/40 | 2018-2024 | 12,2 % | 8,7 % | 21,7 % |
| `ew6` | 2018-2024 | 11,5 % | 5,6 % | 21,5 % |
| `noregime` | 2018-2024 | 8,5 % | 7,1 % | 10,4 % |
| stratégie | 2025-01 → 2026-06-30 | 7,5 % | 6,3 % | 5,4 % |
| SPY détenu | 2025-01 → 2026-06-30 | 17,9 % | 17,3 % | 18,7 % |
| 60/40 | 2025-01 → 2026-06-30 | 11,1 % | 12,7 % | 11,2 % |
| `ew6` | 2025-01 → 2026-06-30 | 12,2 % | 23,8 % | 9,1 % |
| `noregime` | 2025-01 → 2026-06-30 | 7,6 % | 6,5 % | 5,4 % |

Statistiques QC des mêmes backtests. Le Sharpe QC déduit un taux sans risque, celui de la trace non : les deux tableaux ne se comparent pas colonne à colonne.

| Mode | Fenêtre | Sharpe QC | CAGR | Drawdown max | PSR | Ordres |
|---|---|---|---|---|---|---|
| stratégie | 2018-2024 | 0,27 | 6,15 % | 10,4 % | 0,93 % | 884 |
| SPY détenu | 2018-2024 | 0,483 | 13,27 % | 33,7 % | 4,19 % | 1 |
| 60/40 | 2018-2024 | 0,371 | 8,58 % | 21,7 % | 2,05 % | 449 |
| `ew6` | 2018-2024 | 0,171 | 5,54 % | 21,5 % | 0,40 % | 914 |
| `noregime` | 2018-2024 | 0,345 | 7,05 % | 10,4 % | 1,68 % | 861 |
| stratégie | 2025-01 → 2026-06-30 | −0,023 | 5,57 % | 5,4 % | 6,35 % | 76 |
| SPY détenu | 2025-01 → 2026-06-30 | 0,6 | 17,53 % | 18,7 % | 24,79 % | 1 |
| 60/40 | 2025-01 → 2026-06-30 | 0,533 | 12,67 % | 11,2 % | 22,22 % | 85 |
| `ew6` | 2025-01 → 2026-06-30 | 1,169 | 23,02 % | 9,1 % | 53,24 % | 203 |
| `noregime` | 2025-01 → 2026-06-30 | −0,001 | 5,77 % | 5,4 % | 6,78 % | 74 |

**Lecture.** Sur la fenêtre 1, la stratégie rend moins de la moitié de SPY détenu (6,2 % contre 13,4 % par an sur les traces), avec une volatilité 2,4 fois plus faible et un drawdown trois fois plus faible ; à taux nul, elle fait jeu égal avec SPY détenu et le 60/40 (0,783 contre 0,744 et 0,742), sans écart mesurable. Sur la fenêtre 2, elle rend 6,3 % contre 17,3 % (SPY détenu) avec un tiers de la volatilité, mais son Sharpe à taux nul reste derrière les deux références : `NO BEATS`, sans qu'aucun écart ne soit significatif (373 séances).

**La convention de Sharpe change le classement — la prédiction de la fenêtre 1 est réfutée.** La prédiction écrite dans #26322 annonçait `NO BEATS` sur la fenêtre 1. Sous la convention QC, la stratégie est derrière SPY détenu (0,27 contre 0,483) ; à taux nul, elle est devant en point (0,783 contre 0,744). La stratégie est 2,4 fois moins volatile (8,1 % contre 19,4 % par an sur les traces) : la même déduction du taux sans risque pèse d'autant plus sur son Sharpe QC — le mécanisme documenté par Vol-GARCH-Target (#21778). Le verdict mesuré est `INCONCLUSIVE`. Les autres prédictions : innocuité tenue ; « stratégie inférieure ou égale à `ew6` » réfutée en point (0,783 contre 0,527, écart +0,256 non significatif — la question reste ouverte) ; « écart `noregime` non significatif » tenue (`noregime` devant de 0,061, p LW 0,217).

**Sur la fenêtre 2, le vol-targeting n'ajoute rien de mesurable à la détention de l'univers.** `ew6` y domine : Sharpe trace 1,813 contre 0,847, écart −0,965, écart de moyennes de Newey-West p brut 0,043 (Holm 0,257). Sur la fenêtre 1, c'est l'inverse en point (+0,256), sans significativité. Sur l'ensemble des deux fenêtres, aucune exécution ne sépare la stratégie de l'univers équipondéré de façon significative après Holm.

**Le filtre SMA200 ne change rien de mesurable.** Les rendements de la stratégie et de `noregime` sont corrélés à 0,989 (fenêtre 1) et 0,998 (fenêtre 2) ; les écarts (−0,061, puis −0,020) ne sont jamais significatifs. L'overlay conservateur resserre le drawdown sans coût ni gain de Sharpe mesurable : en sortie d'année 2018 il était débrayé (marché haussier), et ses activations 2020 et 2022 arrivent sur des positions déjà réduites par le vol-targeting.

**Écart avec la baseline ci-dessus.** Le contrôle reprend les chiffres de la baseline — Sharpe 0,27 contre 0,265, CAGR 6,148 % contre 6,142 %, drawdown 10,400 % contre 10,40 % (écart d'arrondi et rafraîchissement des prix entre juin et novembre) — mais pas son PSR : 13,6 % n'est pas reproduit (0,933 %). Le `totalOrders = 0` de la baseline était bien un artefact d'extraction : le contrôle compte 884 ordres.

**Propriétés du code, gardées telles quelles dans cette mesure.** Les rendements journaliers se calculent dans `on_data` par `history(sym, 2, Resolution.DAILY)`, sans vérifier que l'avant-dernière barre est la veille de la courante ; un éventuel décalage toucherait les cinq modes de la même façon. Le compte est déclaré sur marge IBKR ; le plafond de 0,25 par actif et la normalisation limitent l'exposition brute. La première exécution `w1-6040` (`74c62256`) est morte en erreur d'exécution — BND abonné mais absent des dictionnaires d'état — d'où la garde du commit `1d12269` ; l'exécution reprise (`1cdcde24`, mêmes paramètres) est celle consignée ici.

**Traces et panier.** Les traces `shadow` des dix exécutions, les relectures des onze backtests et les sorties des quatre exécutions de `significance.py` sont déposées dans le dossier partagé des traces QC, sous `26322-vol-ensemble-conservative-held-references/` (le chemin complet se lit dans la PR de consignation). La stratégie est inscrite comme candidate au panier de la matrice de corrélation hebdomadaire (#19821 brique 4), variante déclarée par défaut : `w1-strategy`.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Vol-targeting d'ensemble conservateur (max de GARCH + HAR) avec filtre de régime |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec comparaison des modèles d'ensemble et analyse des paramètres conservateurs |

## Références

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
