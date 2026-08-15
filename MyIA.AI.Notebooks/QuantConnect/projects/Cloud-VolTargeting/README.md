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

Backtest frais via QC Cloud MCP, 2026-08-07 (`VolTargeting-v1-honest-read-2026-08`, projet 30823587, compile `BuildSuccess`, 1761 dates négociables, 54 ordres) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **0,207** | faible positif |
| CAGR | **6,717 %** | sous le buy-hold SPY (~13-15 % sur la période) |
| Drawdown max | **38,200 %** | élevé (proche de SPY ~34 %, sans le rendement) |
| Profit net total | **57,671 %** (+32 854 $) | sur la période |
| PSR (Probabilistic Sharpe Ratio) | **0,557 %** | non distinguable du bruit |
| Ordres | 54 | turnover très faible (mensuel) |

**Verdict : NO-BEATS.** Le vol targeting sur SPY seul sous-performe le buy-and-hold SPY : CAGR 6,7 % pour un drawdown de 38,2 %, Sharpe 0,207.

## Lecture honnête (variante v1)

Le v1 ajuste l'allocation SPY en fonction de la volatilité réalisée : `allocation = vol_target / realized_vol`, clampée entre 30 % et 150 %. Les faiblesses observées sur 2018-2025 :

- **Signal retardé (lag de volatilité).** La volatilité réalisée augmente typiquement **après** le début d'un drawdown (krach COVID 2020, bear 2022). La réduction d'allocation arrive donc trop tard pour éviter la queue de perte, mais à temps pour rater le rebond qui suit.
- **Plancher d'exposition à 30 %.** Même en forte volatilité, la stratégie reste au moins 30 % investie — la protection à la baisse est donc partielle, tandis que le rendement est amputé côté hausse.
- **Levier en période calme.** `max_allocation = 1,50` ajoute du levier quand la vol est basse (bull markets), ce qui accrît le risque sans amélioration proportionnelle du Sharpe.
- **PSR ≈ 0.** Le Sharpe 0,207 n'est pas statistiquement significatif : indistinguable du bruit. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

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
