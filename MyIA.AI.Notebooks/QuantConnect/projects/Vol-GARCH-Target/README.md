# Vol-GARCH-Target

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** `33245149` (voir `config.json`, local-id : `818573377`)

## Description

Stratégie de vol-targeting GARCH(1,1) sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Chaque actif cible 10 % de volatilité annualisée avec des tailles de position ajustées par la prévision GARCH. Utilise une SMA200 pour la direction de la tendance : l'actif est détenu au-dessus de sa moyenne à 200 jours, et sorti du portefeuille (poids nul) en dessous. Le modèle est ré-estimé tous les 22 jours de bourse sur une fenêtre d'apprentissage de 500 jours. Rebalance hebdomadaire le lundi.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Vol-GARCH-Target/main.py
```

### QC Cloud
Ouvrir le projet cloud (project-id : `33245149`), compiler et lancer un backtest.

### Paramètres de `main.py` (#21778)

Sans paramètre, `main.py` exécute la stratégie sur sa fenêtre codée (2018-01-01 → 2025-01-01). Trois paramètres de backtest servent à la mesurer contre des références détenues, sans toucher à sa décision :

- `mode` : `strategy` (défaut), `spy` (SPY détenu), `6040` (SPY 60 %, BND 40 %) ou `rv21`. `rv21` est la stratégie elle-même, à une différence près : la variance prévue est celle des 21 derniers rendements journaliers, au lieu de la prévision GARCH. Les références `spy` et `6040` se rééquilibrent le premier jour de cotation de chaque mois, une minute après l'ouverture ; BND n'est abonné qu'en mode `6040` ;
- `start_date` et `end_date` (format `%Y%m%d`) : remplacent les bornes de la fenêtre.

Chaque mode trace aussi `shadow` : la valeur du portefeuille à l'ouverture de chaque séance de SPY, répartie sur les séries e0 à e4 (contrat #18923).

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Vol-targeting GARCH(1,1) | Hebdomadaire (lundi) | Vol target 10 %, tendance SMA200, fenêtre 500 jours, ré-estimation tous les 22 jours |

### Baseline alignée (2018-2025)

Vérifiée sur QC Cloud (projet 33245149, backtest `a0f7a5b59e878becd574612b85791d51`).

| Période | Sharpe | CAGR | MaxDD | PSR |
|---------|--------|------|-------|-----|
| 2018-2025 (alignée) | 0.325 | 6.97 % | 10.80 % | 14.9 % |

La force de la stratégie est le contrôle du risque, pas le rendement. Un MaxDD de 10.80 % est le plus serré des baselines dorsales à ce jour (cf GlobalMacro-Regime 22.8 %, HAR-RV-J-Kelly 37.1 %, Cloud-VolTargeting mono-actif 38.2 %) — la prévision de variance GARCH(1,1), le plafond de 30 % par actif et le filtre de tendance SMA200 se combinent en un véritable budget de risque qui contient les drawdowns. Le Sharpe de 0.325 est positif mais modeste, et le PSR de 14.9 % est non significatif. Notablement, elle bat Cloud-VolTargeting (mono-actif SPY, vol réalisée, clamp 150 %) à la fois sur le Sharpe (0.325 vs 0.207) et le MaxDD (10.8 % vs 38.2 %) : la prévision GARCH plus la diversification multi-actifs surperforme une naïve vol réalisée mono-actif avec clamp de levier. Promue Tier 4 (Untested) vers Tier 2 (Historique). Voir le doc comparative-backtests pour la table cross-strategy.

## Mesure contre des références détenues (#21778)

`main.py` est mesuré contre deux références détenues, avec les paramètres décrits plus haut : SPY détenu et le 60/40 (SPY 60 %, BND 40 %). Le protocole est écrit dans #21778 avant le premier backtest. Chaque backtest tourne sur les nœuds QC. Les tests viennent de `Paradox46Benchmarks/significance.py`, à taux sans risque nul : écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire et écart de moyennes de Newey-West.

- **Verdict.** Il compare la stratégie à SPY détenu et au 60/40, avec une correction de Holm sur six p-valeurs. `BEATS` exige un écart de Sharpe positif et une p de Holm (Ledoit-Wolf) inférieure à 0,05 contre les deux références. `NO BEATS` signifie un Sharpe inférieur à celui de SPY détenu. Tous les autres cas sont `INCONCLUSIVE`.
- **Diagnostic.** `rv21` passe dans une exécution séparée, avec Holm sur trois p-valeurs. Il demande si la prévision GARCH apporte quelque chose par rapport à une volatilité réalisée sur 21 séances, toutes choses égales par ailleurs, et ne change pas le verdict.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du `main.py` d'origine : 825 ordres sur 825 identiques (date, symbole, quantité) et 27 statistiques QC sur 27. Tous les ordres sont remplis, aucun n'est refusé. Le compte est déclaré sur marge ; les poids visés somment au plus à 100 %, sans emprunt voulu. Tous sont créés à 10:00, heure de New York, 30 minutes après l'ouverture.

**Fenêtres.** La stratégie n'investit qu'après avoir accumulé 500 rendements, alors que son préchauffage n'en fournit qu'environ 250.

- **Fenêtre codée.** Son premier ordre date du 2018-12-31. Elle passe donc toute l'année 2018 en liquidités, quand SPY détenu y perd 6,0 % et le 60/40 3,4 % (mesurés sur les traces). Cette année est comprise dans la mesure : elle épargne à la stratégie la baisse de 2018, et elle compte aussi des séances à rendement nul dans son Sharpe.
- **Après la fenêtre codée.** Les backtests partent du 2023-11-01, et le premier ordre de la stratégie tombe le 2024-11-04. Les traces des quatre modes sont coupées à la première séance de 2025, pour une mesure sur des portefeuilles déjà investis. La fenêtre s'arrête au 2026-07-23 : les nœuds QC ont coupé le backtest demandé jusqu'au 2026-10-21, et la fin a été lue sur la trace.

Sharpe annualisé de la trace `shadow`, taux sans risque nul. L'écart est celui de la stratégie moins la référence.

| Fenêtre | Séances | Stratégie | SPY détenu (écart, p LW, p Holm) | 60/40 (écart, p LW, p Holm) | Verdict |
|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | 1761 | 0,809 | 0,758 (+0,050 ; 0,894 ; 1,0) | 0,751 (+0,058 ; 0,880 ; 1,0) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-07-23 | 389 | 1,580 | 1,047 (+0,533 ; 0,412 ; 1,0) | 1,164 (+0,416 ; 0,509 ; 1,0) | `INCONCLUSIVE` |

Diagnostic contre `rv21`, même convention.

| Fenêtre | Stratégie | `rv21` | Corrélation journalière | Écart | p LW | p Holm (3 tests) |
|---|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | 0,809 | 0,787 | 0,998 | +0,021 | 0,339 | 0,678 |
| 2025-01-02 → 2026-07-23 | 1,580 | 1,666 | 0,999 | −0,086 | 0,021 | 0,059 |

Volatilité annualisée, rendement annualisé et drawdown maximal des mêmes traces :

| Mode | Fenêtre | Volatilité | Rendement annualisé | Drawdown max |
|---|---|---|---|---|
| stratégie | 2018-2024 | 8,9 % | 7,0 % | 10,8 % |
| SPY détenu | 2018-2024 | 19,4 % | 13,7 % | 33,7 % |
| 60/40 | 2018-2024 | 12,1 % | 8,7 % | 21,7 % |
| `rv21` | 2018-2024 | 9,0 % | 6,9 % | 11,0 % |
| stratégie | 2025-01 → 2026-07-23 | 11,7 % | 19,5 % | 10,3 % |
| SPY détenu | 2025-01 → 2026-07-23 | 17,6 % | 18,3 % | 18,7 % |
| 60/40 | 2025-01 → 2026-07-23 | 10,8 % | 12,8 % | 11,2 % |
| `rv21` | 2025-01 → 2026-07-23 | 11,8 % | 20,9 % | 10,3 % |

Statistiques QC des mêmes backtests. Le Sharpe QC déduit un taux sans risque, celui de la trace non : les deux tableaux ne se comparent pas colonne à colonne. Pour la seconde fenêtre, les statistiques QC portent sur tout le backtest, du 2023-11-01 au 2026-07-23, donc sur l'année passée en liquidités par la stratégie et `rv21`.

| Mode | Backtest | Sharpe QC | CAGR | Drawdown max | Ordres |
|---|---|---|---|---|---|
| stratégie | 2018-2024 | 0,329 | 6,98 % | 10,8 % | 825 |
| SPY détenu | 2018-2024 | 0,496 | 13,58 % | 33,7 % | 3 |
| 60/40 | 2018-2024 | 0,378 | 8,66 % | 21,7 % | 147 |
| `rv21` | 2018-2024 | 0,316 | 6,87 % | 11,0 % | 817 |
| stratégie | 2023-11 → 2026-07-23 | 0,238 | 9,06 % | 10,3 % | 291 |
| SPY détenu | 2023-11 → 2026-07-23 | 0,965 | 24,13 % | 18,7 % | 2 |
| 60/40 | 2023-11 → 2026-07-23 | 0,845 | 16,52 % | 11,2 % | 56 |
| `rv21` | 2023-11 → 2026-07-23 | 0,299 | 9,77 % | 10,3 % | 274 |

**Lecture.** Sur la fenêtre codée, la stratégie rend environ deux fois moins que SPY détenu (7,0 % contre 13,7 % par an), avec une volatilité deux fois plus faible et un drawdown trois fois plus faible. Par unité de risque, à taux nul, elle fait jeu égal avec SPY détenu et le 60/40 ; aucun écart n'est mesurable, et l'année 2018 passée en liquidités pèse dans les deux sens. Après la fenêtre codée, la stratégie rend autant que SPY détenu avec deux tiers de sa volatilité ; ses écarts de Sharpe sont larges en point, mais 389 séances ne suffisent pas à les distinguer de zéro.

**La prévision GARCH n'apporte rien de mesurable.** Sur les deux fenêtres, la stratégie et `rv21` ont des rendements journaliers corrélés à 0,998 ou plus. Sur la fenêtre codée, GARCH fait mieux en point, sans écart significatif. Après elle, c'est la volatilité réalisée sur 21 séances qui fait mieux : l'écart de Sharpe est significatif sans correction (p = 0,021), et à la limite après Holm (0,059). Le bootstrap place son intervalle à 95 % entièrement sous zéro. Une partie de cet écart peut venir de la récursion de la prévision GARCH, décrite plus bas.

**La convention de Sharpe change le classement.** Sous la convention QC, la stratégie reste derrière SPY détenu (0,329 contre 0,496) ; à taux nul, elle le dépasse en point (0,809 contre 0,758). La stratégie est deux fois moins volatile (8,9 % contre 19,4 % par an sur les traces) : la même déduction du taux sans risque pèse environ deux fois plus sur son Sharpe. La prédiction écrite dans #21778 plaçait la stratégie sous SPY détenu à taux nul ; la mesure l'a réfutée. Les autres prédictions tiennent : contrôle tenu, verdict `INCONCLUSIVE`, corrélation avec `rv21` au-dessus de 0,9.

**Écart avec la baseline ci-dessus.** Le backtest de contrôle donne un Sharpe QC de 0,329 et un PSR de 1,5 %, là où la baseline publie 0,325 et 14,9 % pour le même code et la même fenêtre. Le Sharpe, le CAGR et le drawdown concordent, pas le PSR. Le PSR de 14,9 % n'est pas reproduit.

**Propriétés du code, gardées telles quelles dans cette mesure.**

- **Récursion GARCH.** Entre deux ré-estimations, `_garch_forecast` met à jour la variance conditionnelle avec le seul dernier rendement, puis la prévision applique ce même rendement une seconde fois. Le rendement de la veille du rééquilibrage compte donc deux fois, et ceux des quatre séances précédentes ne comptent pas.
- **Rendement journalier.** Il est calculé dans `on_data` à partir de `self.history(sym, 2, Resolution.DAILY)`. Cette mesure n'a pas vérifié si l'avant-dernière barre de cette requête est la veille de la barre courante. Un éventuel décalage toucherait `strategy` et `rv21` de la même façon.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Vol-targeting GARCH(1,1) avec filtre de tendance SMA200 sur 6 ETF multi-actifs |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec analyse du modèle GARCH et exploration des paramètres |

## Références

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
