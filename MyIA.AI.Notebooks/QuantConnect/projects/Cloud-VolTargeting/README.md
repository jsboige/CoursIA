# Cloud-VolTargeting

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** 30823587

## Description

Stratégie de ciblage de volatilité avec trois variantes. v1 cible 12 % de volatilité annualisée sur SPY seul via une mise à l'échelle par volatilité réalisée (log-returns × √252 sur 21 jours). v2 étend à un portefeuille multi-actifs (SPY, QQQ, IEF, GLD) avec une contribution en risque égale ciblant 10 % de volatilité annualisée. v3 ajoute un filtre de momentum sur 126 jours à l'approche multi-actifs, avec repli défensif sur IEF. Rebalance mensuelle pour toutes les variantes. Brokerage Interactive Brokers (frais réels), benchmark SPY.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-VolTargeting/main.py
```

### QC Cloud
Projet 30823587. Téléverser `main.py`, compiler et lancer un backtest. Période codée en dur : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630). La variante par défaut (`version=1`, SPY seul) est backtestée ci-dessous ; passer `version=2` ou `3` pour les variantes multi-actifs.

## Métriques de backtest

Run le plus récent via QC Cloud MCP, 2026-10-20 (`main.py` tel que committé, projet 30823587, compile `BuildSuccess`, backtest `21585-v1-warmup-2018-2025` = `cc01cc58067e2021aadfa3c1dbb3fb1c`, 1761 dates négociables, 84 ordres) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **0,438** | faible positif |
| CAGR | **10,845 %** | sous le buy-hold SPY, dividendes réinvestis (13,731 % sur la même fenêtre) |
| Drawdown max | **21,000 %** | sous SPY (33,717 % au krach COVID 2020) |
| Profit net total | **105,691 %** (+105 691,36 $) | equity finale 205 691,36 $ ; la part réalisée seule est de 77 750,40 $ |
| PSR (Probabilistic Sharpe Ratio) | **3,263 %** | indistinguable du bruit |
| Ordres | 84 | turnover très faible (mensuel) |

**Verdict : NO-BEATS.** Le vol targeting sur SPY seul ne bat pas le buy-and-hold SPY : CAGR 10,8 % contre 13,7 %, Sharpe sous celui du benchmark, PSR 3,3 % — indistinguable du bruit. Ce qu'il achète en échange n'est pas le rendement ajusté du risque mais le drawdown (21,0 % contre 33,7 %).

Sous-performance et significativité sont mesurées séparément, pas confondues :

- **Rendements excédentaires** — test apparié des 1756 séances où les deux jambes sont observées (bootstrap circulaire par blocs de 21 séances, 10 000 tirages, graine 18921, instrument `voltarget_strategy_verdict.circular_block_diff` du dépôt) : différence de Sharpe **-0,015**, **p unilatérale 0,556**, IC 95 % [-0,374 ; +0,307]. La sous-performance cumulée est réelle (+106,5 % contre +146,9 % pour SPY sur la fenêtre) ; la différence de Sharpe, elle, est du bruit.
- **PSR de QC** — 3,263 % : le Sharpe 0,438 n'est pas distinguable du bruit.

Fenêtre longue 2007-2026 (`21585-v1-warmup-oos` = `f3839e9e82a78d83bb45d37045864c6e`, 4946 dates négociables, 235 ordres) : Sharpe 0,488, CAGR 10,630 %, drawdown max 31,300 %, profit net 630,024 % (+630 024,26 $), PSR 0,229 % — même verdict. Aucune jambe SPY n'y est disponible (le run frère qui expose `set_benchmark("SPY")` porte la fenêtre alignée 2018-2025), donc le test apparié n'y est pas calculé et la PSR de QC y reste le seul instrument de significativité.

### Effet des correctifs sur ces chiffres (#18941 puis #21585)

Les deux runs ci-dessous ne diffèrent que par `set_warm_up(21, Resolution.DAILY)` et la garde `is_warming_up` dans `rebalance()` :

| Fenêtre | Run | Ordres | Sharpe | CAGR | Drawdown max | Profit net | PSR |
|---|---|---|---|---|---|---|---|
| 2018-2025, avant | `18941-v1-after-2018-2025` (`695126a305a6fc3e52191c81733958f3`) | 83 | 0,382 | 9,761 % | 20,900 % | 92,011 % (+92 010,66 $) | 2,227 % |
| 2018-2025, après | `21585-v1-warmup-2018-2025` (`cc01cc58067e2021aadfa3c1dbb3fb1c`) | **84** | 0,438 | 10,845 % | 21,000 % | 105,691 % (+105 691,36 $) | 3,263 % |
| 2007-2026, avant | `18941-v1-after-oos` (`eea534fd4d223287fd446db6b56befb8`) | 234 | 0,478 | 10,448 % | 31,200 % | 606,809 % (+606 809,12 $) | 0,197 % |
| 2007-2026, après | `21585-v1-warmup-oos` (`f3839e9e82a78d83bb45d37045864c6e`) | **235** | 0,488 | 10,630 % | 31,300 % | 630,024 % (+630 024,26 $) | 0,229 % |

Le montant en dollars est la variation d'equity (part réalisée + latente), homologue du pourcentage de profit net **total**. QC publie par ailleurs « Net Profit », qui ne compte que la part **réalisée** (65 999,11 $ et 77 750,40 $ pour les deux runs 2018-2025, l'écart valant exactement l'« Unrealized » publié) : les deux ne se mélangent pas dans une même ligne.

Le correctif récupère **un rééquilibrage par fenêtre** (83 → 84 et 234 → 235 ordres) : la première séance du run déclenchait le rééquilibrage mensuel (`date_rules.month_start("SPY")`, correctif #18941) avant que SPY n'ait reçu sa première barre ; l'ordre partait à un prix nul et QuantConnect le rejetait, la courbe restait plate jusqu'au mois suivant. Sans warm-up, janvier 2018 se passait donc en liquidités — mois où SPY a rendu 5,5 % — et l'equity finale porte cet écart composé sur sept ans (192 010,66 $ contre 205 691,36 $).

Le tableau publié ici jusqu'au 2026-10-20 (Sharpe 0,207, CAGR 6,717 %, drawdown 38,200 %, profit net 57,671 %, PSR 0,557 %, 54 ordres, run `VolTargeting-v1-honest-read-2026-08` du 2026-08-07) datait d'**avant ces deux correctifs** : #18941 d'abord (le rééquilibrage mensuel sautait les mois dont le 1er n'est pas un jour de bourse : 54 → 83 ordres), #21585 ensuite. L'écart est attribué aux correctifs, non à un re-tuning : les paramètres de la stratégie sont inchangés et le verdict honnête reste le même.

Les runs `18941-v1-after-*` (avant warm-up) portaient en outre le test de significativité des rendements excédentaires de QuantConnect : p = 0,0594 sur 2018-2025 et p = 0,298 sur 2007-2026, tous deux > 0,05 — le verdict NO-BEATS tenait déjà avant ce correctif.

## Lecture honnête (variante v1)

Le v1 ajuste l'allocation SPY en fonction de la volatilité réalisée : `allocation = vol_target / realized_vol`, clampée entre 30 % et 150 %. Les faiblesses observées sur 2018-2025 :

- **Signal retardé (lag de volatilité).** La volatilité réalisée augmente typiquement **après** le début d'un drawdown (krach COVID 2020, bear 2022). La réduction d'allocation arrive donc trop tard pour éviter la queue de perte, mais à temps pour rater le rebond qui suit.
- **Plancher d'exposition à 30 %.** Même en forte volatilité, la stratégie reste au moins 30 % investie — la protection à la baisse est donc partielle, tandis que le rendement est amputé côté hausse.
- **Levier en période calme.** `max_allocation = 1,50` ajoute du levier quand la vol est basse (bull markets), ce qui accrît le risque sans amélioration proportionnelle du Sharpe.
- **PSR ≈ 3 %.** Le Sharpe 0,438 n'est pas statistiquement significatif : indistinguable du bruit. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

Les variants v2 (diversification multi-actifs + contribution en risque égale) et v3 (+ momentum + défensif IEF) visent à corriger ces faiblesses (diversifier réduit le drawdown, le momentum filtre les actifs en baisse), mais ne sont pas backtestés ici : un honest-read documente le variant baseline et son verdict honnête, sans re-tuning. Ré-optimiser la cible de vol, le lookback ou les bornes d'allocation pour récupérer un Sharpe positif sur cette seule fenêtre serait du surapprentissage jusqu'à preuve du contraire (EPIC #9768, D2 « fenêtre non figée »). La stratégie est livrée avec ses paramètres codés tels quels, verdict honnête rendu.

## Noyau de risque déterministe (#24698)

Le paramètre `kernel` ajoute à la variante v1 le noyau de risque déterministe de Steward (arXiv 2610.30557), dont le projet `DeterministicRiskKernel-QC` est le portage de référence dans ce dépôt. Il ne s'applique qu'à `version=1`. Avec la valeur par défaut, `kernel=off`, le code de la stratégie est inchangé.

| `kernel` | Plafond d'exposition à 90 % | Stop à 2 ATR(14) | Coupe-circuit à −3 % |
|---|---|---|---|
| `off` (défaut) | non | non | non |
| `cap90` | oui | non | non |
| `kernel_nocb` | oui | oui | non |
| `kernel` | oui | oui | oui |

Sur une stratégie à une seule ligne et à rééquilibrage mensuel, le noyau prend la forme suivante :

- **le plafond** borne l'allocation maximale à 0,90 au lieu de 1,50. Il s'applique à l'ordre : entre deux rééquilibrages, la hausse du prix porte l'exposition mesurée jusqu'à 0,906-0,920 (colonne « Exposition max ») ;
- **le stop** est un ordre `StopMarket` à 2 ATR(14) sous le prix du moment de l'ordre, reposé à chaque rééquilibrage. Une ligne stoppée reste à plat jusqu'au rééquilibrage suivant ;
- **le coupe-circuit** lit la clôture : si la valeur du portefeuille perd 3 % ou plus sur la séance, la ligne est vendue à l'ouverture suivante (`MarketOnOpen`) et reprend son allocation du mois à l'ouverture d'après ;
- **la règle de dimensionnement de Steward** (0,5 % du capital au stop) n'est pas implémentée : la taille de la ligne reste celle du ciblage de volatilité, bornée par le plafond.

Le paramètre `reentry` règle le retour d'une ligne stoppée. Avec `month` (défaut), elle attend le rééquilibrage mensuel. Avec `week`, elle revient au début de la semaine suivante, avec l'allocation du mois en cours. Cette seconde valeur est une variante diagnostique, réservée aux modes avec stop : elle mesure ce que coûte la durée passée à plat après un stop.

### Mesures

Douze backtests du 2026-11-09, projet QC 39144431 (espace de backtest du cours). Les huit runs d'ablation viennent de la compile `b4d8178a895d808ac50bddbeb4532c37-88b7c84ed7d03b2e16eb8f58353894be`, les quatre runs de re-entrée de la compile `4e7079a1fe14ff4974657dff33bbbfc0-08b43aaf8927e0b487cb8caaf234769d`, qui ajoute le paramètre `reentry` et le compteur de séances à plat. Les deux sont `BuildSuccess`. Fenêtre courte : `start`/`end` par défaut (2018-01-01 → 2025-01-01, 1761 dates négociables). Fenêtre longue : `start=2007-01-01`, `end=2026-07-31` (4925 dates négociables). Le modèle de frais de la stratégie est inchangé.

Ablation du noyau (`reentry=month`) :

| Fenêtre | `kernel` | Backtest | Ordres | Sharpe | CAGR | Drawdown max | Profit net | PSR | Stops | Coupures | Exposition max |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2018-2025 | `off` | `d7aa7926dd36cb908c6a101c7ff7b432` | 84 | 0,438 | 10,845 % | 21,0 % | 105,691 % | 3,263 % | — | — | — |
| 2018-2025 | `cap90` | `e910e8e33a2f8b2246ec438e77e36128` | 71 | 0,489 | 10,461 % | 20,2 % | 100,750 % | 4,523 % | — | — | 0,9092 |
| 2018-2025 | `kernel_nocb` | `366d47e7c1db4178a01271e7f97fda8d` | 160 | 0,482 | 8,548 % | 14,9 % | 77,632 % | 4,389 % | 38 | — | 0,9105 |
| 2018-2025 | `kernel` | `c0887f433054d45a7d98a0ff631d7da5` | 161 | 0,484 | 8,578 % | 14,9 % | 77,978 % | 4,452 % | 38 | 1 | 0,9113 |
| 2007-2026 | `off` | `b441bfaae4140d22bacbe54943439dda` | 234 | 0,484 | 10,557 % | 31,3 % | 614,527 % | 0,220 % | — | — | — |
| 2007-2026 | `cap90` | `ba5c79b46623cd4ce63cba6179c2108b` | 196 | 0,443 | 8,828 % | 31,1 % | 424,642 % | 0,113 % | — | — | 0,9063 |
| 2007-2026 | `kernel_nocb` | `c1541a65d919a07d9f3846cc30dd28c3` | 446 | 0,224 | 4,904 % | 24,9 % | 155,499 % | 0,002 % | 113 | — | 0,9113 |
| 2007-2026 | `kernel` | `f9ef53eb3014eb4a7385be5c28334d08` | 449 | 0,225 | 4,916 % | 24,9 % | 156,084 % | 0,002 % | 113 | 1 | 0,9114 |

Re-entrée après un stop (`kernel=kernel_nocb`). Les séances à plat sont les séances closes sans position. Le dénominateur compte les séances vues par `on_data` (1789 et 5003), un peu plus que les dates négociables ; la cause de cet écart n'est pas vérifiée.

| Fenêtre | `reentry` | Backtest | Ordres | Sharpe | CAGR | Drawdown max | Profit net | PSR | Stops | Séances à plat |
|---|---|---|---|---|---|---|---|---|---|---|
| 2018-2025 | `month` | `5a16563dfdb17b1c4387b6174fcbdd3c` | 160 | 0,482 | 8,548 % | 14,9 % | 77,632 % | 4,389 % | 38 | 549 / 1789 (31 %) |
| 2018-2025 | `week` | `dbaeecb82b62326152d7c6434bcd64c0` | 266 | 0,668 | 11,966 % | 11,6 % | 120,714 % | 12,032 % | 62 | 179 / 1789 (10 %) |
| 2007-2026 | `month` | `851ca512f0a435e836a8d8e1f895bbb5` | 446 | 0,224 | 4,904 % | 24,9 % | 155,499 % | 0,002 % | 113 | 1622 / 5003 (32 %) |
| 2007-2026 | `week` | `4c6260c64469e230ad65fb308d3f5d84` | 746 | 0,375 | 7,343 % | 31,0 % | 300,845 % | 0,033 % | 170 | 447 / 5003 (9 %) |

**Témoins.** Le run `off` de 2018-2025 reproduit le run `21585-v1-warmup-2018-2025` du tableau principal (84 ordres, Sharpe 0,438, CAGR 10,845 %, drawdown 21,0 %) : le code du noyau ne change rien quand il est désactivé. Le run `off` de 2007-2026 compte 4925 dates et 234 ordres, contre 4946 et 235 pour `21585-v1-warmup-oos` : la fin des données disponibles dans l'espace de backtest du cours arrive plus tôt que la date `end` demandée, et les deux fenêtres longues ne sont donc pas identiques. Les runs `month` de la seconde compile reproduisent à l'identique les runs `kernel_nocb` de la première : le paramètre `reentry` ne change pas le comportement par défaut.

### Lecture

- **Sur 2018-2025, le noyau échange du rendement contre du drawdown.** Le drawdown passe de 21,0 % à 14,9 % et le CAGR de 10,8 % à 8,6 %. Le Sharpe monte de 0,438 à 0,484, mais le plafond seul (`cap90`) en fait autant (0,489) : ce gain vient du retrait du levier de 1,50, pas du stop.
- **Sur 2007-2026, ce compromis ne tient pas.** Ajouté au plafond, le stop divise par deux le CAGR (4,9 % contre 10,6 %) et le Sharpe (0,224 contre 0,484), pour 6,4 points de drawdown en moins. Le plafond seul y fait baisser le Sharpe (0,443).
- **Une bonne part du coût vient de la durée passée à plat.** Avec le rééquilibrage mensuel, une ligne stoppée reste hors du marché jusqu'au mois suivant : 31 à 32 % des séances se passent sans position. Si elle revient à la semaine, cette part tombe à 9-10 %. Sur 2018-2025, la variante `week` est alors meilleure que `off` sur les trois mesures (Sharpe 0,668, CAGR 12,0 %, drawdown 11,6 %).
- **Mais le gain de drawdown venait de ce temps hors marché.** Sur 2007-2026, la variante `week` récupère à peu près la moitié de l'écart de Sharpe et de CAGR (0,375 et 7,3 %), et son drawdown remonte à 31,0 %, le niveau sans noyau. Ses 170 stops en dix-neuf ans sont autant d'allers-retours, dont le coût n'est pas isolé ici. La variante `week` a en outre été conçue après lecture des résultats de 2018-2025 : c'est un diagnostic, pas une candidate.
- **Le coupe-circuit est presque inerte** : une coupure par fenêtre, sans effet mesurable.

**Verdict : NO BEATS.** Sous la stratégie v1, le noyau ne bat pas la stratégie sans noyau sur la fenêtre longue. Les backtests sont déterministes (aucune graine) ; aucun test apparié n'est calculé ici, et la lecture favorable de 2018-2025 ne survit pas à la fenêtre 2007-2026.

**Contraste avec `DeterministicRiskKernel-QC`.** Sur un portefeuille de 10 ETF rééquilibré chaque semaine, l'ablation à 50 graines de #25221 trouve au contraire un gain de drawdown net à CAGR presque inchangé, le coupe-circuit n'y apportant rien non plus. La différence tient à la structure du portefeuille : avec une seule ligne et un rééquilibrage mensuel, un stop vide tout le portefeuille pendant des semaines. Avec dix lignes revues chaque semaine, il n'en sort qu'une, et au plus jusqu'au rééquilibrage de la semaine suivante.

Suites possibles, non mesurées : le dimensionnement à risque fixe de Steward, un stop plus large, une re-entrée sur signal plutôt qu'au calendrier, et un test apparié des rendements entre `off` et `kernel`.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Ciblage de volatilité avec 3 variantes (v1 SPY seul, v2 multi-actifs equal-risk, v3 +momentum +défensif IEF), et noyau de risque déterministe optionnel sur v1 (paramètres `kernel` et `reentry`) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
