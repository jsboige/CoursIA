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

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Ciblage de volatilité avec 3 variantes (v1 SPY seul, v2 multi-actifs equal-risk, v3 +momentum +défensif IEF) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
