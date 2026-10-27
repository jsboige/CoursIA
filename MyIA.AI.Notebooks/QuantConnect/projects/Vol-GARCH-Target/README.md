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

`seed_initial_prices` n'est armé qu'en modes `spy` et `6040`, comme dans les projets voisins, et il est sans effet ici. Dans les quatre modes, `rebalance`, `_rebalance_reference` et `_trace` ne font rien tant que dure le préchauffage de 250 séances, qui donne un prix à chaque titre abonné. Le mode `strategy` garde ainsi le chemin du code d'origine, que le contrôle d'innocuité compare ordre par ordre.

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

Les trois p brutes du diagnostic (Ledoit-Wolf, bootstrap, écart moyen) valent 0,339, 0,215 et 0,641 sur la fenêtre codée, puis 0,021, 0,051 et 0,020 après elle. Holm les range par ordre croissant, multiplie la plus petite par 3, la suivante par 2 et la dernière par 1, puis reporte à chaque rang le maximum déjà atteint. Sur la fenêtre codée, la p de Ledoit-Wolf est au deuxième rang : 2 × 0,339 = 0,678 dépasse 3 × 0,215 = 0,645. Après elle, la plus petite est celle de l'écart moyen (0,0198) : 3 × 0,0198 = 0,059, et ce maximum s'impose aussi à la p de Ledoit-Wolf, dont le produit seul vaudrait 2 × 0,0207 = 0,041.

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

**La prévision GARCH n'apporte rien de mesurable.** Sur les deux fenêtres, la stratégie et `rv21` ont des rendements journaliers corrélés à 0,998 ou plus. Sur la fenêtre codée, GARCH fait mieux en point, sans écart significatif. Après elle, c'est la volatilité réalisée sur 21 séances qui fait mieux : l'écart de Sharpe est significatif sans correction (p = 0,021), et à la limite après Holm (0,059). Le bootstrap place son intervalle à 95 % entièrement sous zéro. Cet écart venait en partie de la récursion de la prévision GARCH, décrite plus bas : une fois celle-ci corrigée, il se réduit de moitié et n'est plus significatif (p de Ledoit-Wolf 0,160, p de Holm 0,479, intervalle bootstrap contenant zéro ; section « Significativité de la version corrigée »).

**La convention de Sharpe change le classement.** Sous la convention QC, la stratégie reste derrière SPY détenu (0,329 contre 0,496) ; à taux nul, elle le dépasse en point (0,809 contre 0,758). La stratégie est deux fois moins volatile (8,9 % contre 19,4 % par an sur les traces) : la même déduction du taux sans risque pèse environ deux fois plus sur son Sharpe. La prédiction écrite dans #21778 plaçait la stratégie sous SPY détenu à taux nul ; la mesure l'a réfutée. Les autres prédictions tiennent : contrôle tenu, verdict `INCONCLUSIVE`, corrélation avec `rv21` au-dessus de 0,9.

**Écart avec la baseline ci-dessus.** Le backtest de contrôle donne un Sharpe QC de 0,329 et un PSR de 1,5 %, là où la baseline publie 0,325 et 14,9 % pour le même code et la même fenêtre. Le Sharpe, le CAGR et le drawdown concordent, pas le PSR. Le PSR de 14,9 % n'est pas reproduit.

**Propriétés du code, gardées telles quelles dans cette mesure.** Les deux défauts ci-dessous sont ceux du code que #21778 a mesuré ; ils sont corrigés depuis #21782, et la correction est mesurée dans la section suivante.

- **Récursion GARCH.** Entre deux ré-estimations, `_garch_forecast` met à jour la variance conditionnelle avec le seul dernier rendement, puis la prévision applique ce même rendement une seconde fois. Le rendement de la veille du rééquilibrage compte donc deux fois, et ceux des quatre séances précédentes ne comptent pas.
- **Rendement journalier.** Il est calculé dans `on_data` à partir de `self.history(sym, 2, Resolution.DAILY)`. Cette mesure n'a pas vérifié si l'avant-dernière barre de cette requête est la veille de la barre courante. Un éventuel décalage toucherait `strategy` et `rv21` de la même façon.

## Correction de la récursion GARCH (#21782)

Les deux propriétés ci-dessus sont corrigées ; la correction est mesurée sur les mêmes fenêtres et contre les mêmes références.

- **Récursion.** `cond_var` tient désormais la prévision du prochain rendement non observé. Entre deux ré-estimations, la variance avance d'un pas par rendement reçu depuis le dernier appel — les compteurs absolus `return_count` / `folded_count` portent cette position, la fenêtre glissante du `deque` ne permettant pas d'indexer un rendement de façon stable — et la prévision n'est appliquée qu'une fois.
- **Rendement journalier.** `_daily_log_return` aligne la paire de clôtures sur `bar.end_time` (un historique LEAN inclut ou non la séance courante selon l'heure de l'appel), et écarte une paire non finie, non positive, ou séparée de plus de quatre jours calendaires. Sur 2023-11 → 2026-07-23, le filtre calendaire a écarté 24 rendements en 129 rééquilibrages sans changer une seule statistique publiée ci-dessous, et les garde-fous de finitude n'ont rien écarté : cette partie est une robustesse, pas un correctif de performance.

### Ce que la correction change

Backtests QC Cloud, mêmes paramètres que #21778 (projet 38215259, copie instrumentée).

| Fenêtre | Version | Ordres | Sharpe QC | CAGR | Drawdown max |
|---|---|---|---|---|---|
| 2018-01 → 2025-01 | #21781 (publiée) | 825 | 0,329 | 6,977 % | 10,80 % |
| 2018-01 → 2025-01 | corrigée | 831 | 0,325 | 6,939 % | 10,60 % |
| 2023-11 → 2026-07-23 | #21781 (publiée) | 291 | 0,238 | 9,057 % | 10,30 % |
| 2023-11 → 2026-07-23 | corrigée | 276 | 0,269 | 9,418 % | 10,30 % |
| 2023-11 → 2026-07-23 | `rv21` | 274 | 0,299 | 9,766 % | 10,30 % |

Sharpe annualisé à taux nul, sur les traces `shadow` coupées à la première séance de 2025, soit 388 séances du 2025-01-02 au 2026-07-23 :

| Version | Sharpe à taux nul | Rendement annualisé | Volatilité | Corrélation à `rv21` |
|---|---|---|---|---|
| #21781 (publiée) | 1,575 | 19,4 % | 11,8 % | 0,999 |
| corrigée | 1,617 | 20,1 % | 11,8 % | 0,999 |
| `rv21` | 1,661 | 20,8 % | 11,8 % | — |

La ligne #21781 reproduit le 1,580 publié et la ligne `rv21` le 1,666 publié, aux arrondis et à la convention de découpe près.

**Prédiction et verdict.** La prédiction écrite avant la mesure annonçait moins de 5 % d'écart sur le nombre d'ordres, un mouvement de Sharpe inférieur à ±0,05, et un `rv21` qui garde l'avantage en voyant l'écart se réduire sans changer de signe. Il en va ainsi, sauf sur le premier point, dépassé de peu : 291 → 276 ordres, soit −5,2 % sur la seconde fenêtre, et +0,7 % sur la fenêtre codée. Le Sharpe à taux nul gagne 0,042, l'écart à `rv21` passe de 0,086 à 0,044 sans changer de signe : la correction rapproche GARCH de la volatilité réalisée, elle ne le fait pas passer devant.

### Significativité de la version corrigée

Les tests du protocole #21778 sont rejoués sur le `main.py` corrigé, avec le même instrument (`Paradox46Benchmarks/significance.py`, taux sans risque nul) et les mêmes séances que #21781 : 1761 sur la fenêtre codée, 389 du 2025-01-02 au 2026-07-23 après elle. Huit backtests QC Cloud (quatre modes, deux fenêtres), lus à `completed: true`. La prédiction a été écrite sur #21782 avant le premier backtest.

**Les références n'ont pas bougé.** Les traces `spy` et `6040` reproduisent celles de #21781 à l'identique sur les deux fenêtres (écart relatif maximal nul). Seul le code corrigé par #22013 diffère entre les deux mesures, et les modes `spy` et `6040` n'y passent pas.

**Verdict.** Il reste `INCONCLUSIVE` sur les deux fenêtres. Les six p de Holm valent 1,0 sur chacune.

| Fenêtre | Séances | Stratégie | SPY détenu (écart, p LW) | 60/40 (écart, p LW) | Verdict |
|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | 1761 | 0,803 | 0,758 (+0,045 ; 0,905) | 0,751 (+0,053 ; 0,890) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-07-23 | 389 | 1,622 | 1,047 (+0,575 ; 0,371) | 1,164 (+0,459 ; 0,462) | `INCONCLUSIVE` |

**Diagnostic contre `rv21`.** L'écart significatif d'avant la correction disparaît.

| Fenêtre | Version | Stratégie | `rv21` | Corrélation | Écart | p LW | IC 95 % bootstrap | p Holm (3 tests) |
|---|---|---|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | #21781 | 0,809 | 0,787 | 0,998 | +0,021 | 0,339 | — | 0,678 |
| 2018-01-02 → 2024-12-31 | corrigée | 0,803 | 0,783 | 0,998 | +0,020 | 0,299 | [−0,010 ; +0,052] | 0,598 |
| 2025-01-02 → 2026-07-23 | #21781 | 1,580 | 1,666 | 0,999 | −0,086 | 0,021 | sous zéro | 0,059 |
| 2025-01-02 → 2026-07-23 | corrigée | 1,622 | 1,666 | 0,999 | −0,044 | 0,160 | [−0,120 ; +0,033] | 0,479 |

Après la fenêtre codée, les trois p brutes (Ledoit-Wolf, écart moyen, bootstrap) valent 0,160, 0,176 et 0,288. Holm multiplie la plus petite par 3, ce qui donne 0,479 ; ce maximum s'impose aux deux autres. Sur la fenêtre codée, les p brutes valent 0,299, 0,573 et 0,189, et les p de Holm 0,598, 0,598 et 0,567.

**Ce que la correction touche.** Sur la seconde fenêtre, la trace `rv21` est identique à celle de #21781 : la correction n'y déplace que la stratégie. Sur la fenêtre codée, elle déplace aussi `rv21`, dont le Sharpe à taux nul passe de 0,787 à 0,783 : le calcul du rendement journalier (`_daily_log_return`) est commun aux deux modes, et 1510 des 1761 séances diffèrent, d'au plus 0,8 % ; son backtest passe de 817 à 824 ordres. Le diagnostic de la fenêtre codée compare donc deux séries modifiées, celui de la seconde fenêtre une série modifiée à une série inchangée.

**Prédiction et mesure.** Les quatre points écrits avant la mesure tiennent. Après la fenêtre codée, la p de Ledoit-Wolf passe au-dessus de 0,05 et la p de Holm au-dessus de 0,10, l'intervalle bootstrap contient zéro et la corrélation reste au-dessus de 0,99. Sur la fenêtre codée, l'écart garde son signe et sa p de Holm dépasse 0,5. Le verdict reste `INCONCLUSIVE`, et les références ne bougent pas. Le déplacement de `rv21` sur la fenêtre codée n'était pas prédit.

**Lecture.** L'avantage de `rv21` sur la seconde fenêtre tenait en partie au défaut de récursion. Une fois celle-ci corrigée, la prévision GARCH et la volatilité réalisée sur 21 séances ne se distinguent plus, sur aucune des deux fenêtres : le diagnostic ne permet pas de dire que la prévision GARCH apporte quelque chose, ni qu'elle coûte quelque chose.

**Statistiques QC des huit backtests.** Les nœuds QC coupent un backtest 90 jours avant la date du jour. Les backtests de la seconde fenêtre s'arrêtent donc au 2026-07-28, trois séances plus tard que ceux de #22013 (2026-07-23). Leurs statistiques QC portent sur ces trois séances de plus et ne se comparent pas à celles du tableau précédent. Les traces, elles, sont coupées au 2026-07-23 dans les deux mesures. Sur la fenêtre codée, la stratégie reproduit exactement la ligne « corrigée » du tableau précédent.

| Mode | Backtest | Sharpe QC | CAGR | Drawdown max | Ordres |
|---|---|---|---|---|---|
| stratégie | 2018-01 → 2025-01 | 0,325 | 6,94 % | 10,6 % | 831 |
| SPY détenu | 2018-01 → 2025-01 | 0,496 | 13,58 % | 33,7 % | 3 |
| 60/40 | 2018-01 → 2025-01 | 0,378 | 8,66 % | 21,7 % | 147 |
| `rv21` | 2018-01 → 2025-01 | 0,312 | 6,83 % | 11,1 % | 824 |
| stratégie | 2023-11 → 2026-07-28 | 0,195 | 8,57 % | 10,3 % | 280 |
| SPY détenu | 2023-11 → 2026-07-28 | 0,969 | 24,15 % | 18,7 % | 2 |
| 60/40 | 2023-11 → 2026-07-28 | 0,855 | 16,61 % | 11,2 % | 56 |
| `rv21` | 2023-11 → 2026-07-28 | 0,225 | 8,91 % | 10,3 % | 276 |

Sur la seconde fenêtre, le Sharpe QC de la stratégie passe de 0,269 à 0,195 avec ces trois séances, qui lui font perdre 1,6 %. Avec un taux sans risque déduit et une volatilité d'environ 11 %, un écart de CAGR de 0,85 point suffit à le déplacer de 0,07. Ce chiffre tient à la date de fin du backtest, pas à un écart de performance de la stratégie.


## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Vol-targeting GARCH(1,1) avec filtre de tendance SMA200 sur 6 ETF multi-actifs |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec analyse du modèle GARCH et exploration des paramètres |

## Références

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
