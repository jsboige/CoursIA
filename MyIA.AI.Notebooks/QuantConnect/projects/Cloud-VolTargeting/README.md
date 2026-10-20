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
Projet 30823587. Téléverser `main.py`, compiler et lancer un backtest. Période par défaut : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630), surchargeable par les paramètres `start` / `end` (l'expérience #18921 tourne sur 2007-01-01 → 2026-08-31). La variante par défaut (`version=1`, SPY seul) est backtestée ci-dessous ; passer `version=2` ou `3` pour les variantes multi-actifs.

## Métriques de backtest

Re-backtest de la variante v1 après les deux correctifs de code déjà fusionnés, 2026-10-20 — run QC `18941-v1-after-2018-2025` (projet 30823587, compile `BuildSuccess`, fenêtre **2018-01-01 → 2025-01-01** — la fenêtre publiée, 1761 dates négociables, 83 ordres, paramètres `version=1`) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **0,382** | faible positif, non significatif face au benchmark |
| CAGR | **9,761 %** | sous le buy-hold SPY (~13-15 % sur la période) |
| Drawdown max | **20,900 %** | nettement sous SPY (~34 %) |
| Profit net total | **92,011 %** (+92 010,66 $) | sur la période |
| PSR (Probabilistic Sharpe Ratio) | **2,227 %** | ~2 % de chance que le Sharpe annualisé **dépasse le seuil ≈ 1** — **pas** une probabilité de battre SPY |
| Ordres | 83 | un rééquilibrage par mois (84 mois, le premier rejeté — voir « limite connue ») |

**Ce que les correctifs ont changé**, comparaison au run publié du 2026-08-07 (`VolTargeting-v1-honest-read-2026-08`, **même fenêtre**, 54 ordres) :

| Indicateur | 2026-08-07 (publié) | 2026-10-20 (re-backtest) | Écart |
|---|---|---|---|
| Ratio de Sharpe | 0,207 | **0,382** | ×1,85 |
| CAGR | 6,717 % | **9,761 %** | +3,04 pts |
| Drawdown max | 38,200 % | **20,900 %** | −17,30 pts |
| Profit net total | 57,671 % (+57 671,45 $) | **92,011 %** (+92 010,66 $) | +34,34 pts |
| PSR | 0,557 % | **2,227 %** | ×4 |
| Ordres | 54 | **83** | +29 rééquilibrages |
| p-value (excédent face au benchmark) | 0,0706 | **0,0594** | > 0,05 dans les deux cas |

Les deux causes sont des correctifs de code fusionnés, pas un réglage de paramètres :

- **calendrier de rééquilibrage (#18967)** — `date_rules.month_start()` sans symbole vise le 1er du mois **calendaire** ; les mois dont le 1er n'est pas un jour de bourse (week-ends, jours fériés) ne déclenchaient rien. Le code cible désormais la première séance du mois (`month_start("SPY")`), d'où 83 ordres contre 54.
- **fenêtre d'historique (#20286)** — sur une demi-séance (clôture à 13:00), `history(symbol, 21, Resolution.DAILY)` rend moins de barres que demandé et le titre était écarté. La stratégie demande le double et garde les 21 dernières barres.

**Verdict : NO-BEATS (inchangé).** QC compare la stratégie au benchmark SPY : « the strategy has a lower Sharpe ratio than the benchmark », et le test de significativité des rendements excédentaires donne **p = 0,0594 > 0,05** — l'hypothèse nulle (excédent moyen nul ou négatif face au benchmark) n'est pas rejetée. (Le PSR 2,2 % mesure la probabilité que le Sharpe annualisé dépasse le seuil ≈ 1, **pas** la probabilité de battre SPY.) Le vol targeting sur SPY seul reste sous le buy-and-hold : CAGR 9,8 % pour un drawdown de 20,9 %.

**Extension historique (2007-01-01 → 2026-08-31)** — run QC `18941-v1-after-oos`, même code, même variante `version=1`, 4946 dates négociables, 234 ordres : Sharpe **0,478** · CAGR **10,448 %** · drawdown max **31,200 %** · profit net **606,809 %** (+606 809,12 $) · PSR **0,197 %** · p-value **0,298**. Cette fenêtre **englobe** la fenêtre publiée 2018-01-01 → 2025-01-01 : ce n'est **pas** une validation hors échantillon indépendante, mais une extension de l'historique — les deux runs partagent intégralement leur tronc commun 2018-2025. Sur 19,7 ans le Sharpe 0,478 se distingue de zéro (t ≈ 2,1, p ≈ 0,03) mais **pas** du benchmark (p = 0,298) : la constance du profil ne se transforme pas en edge.

**Limite connue, mesurée et non cachée.** Le re-backtest a fait apparaître un défaut de bord : le premier rééquilibrage de chaque run (2018-01-02, 2007-01-03) est **rejeté** par QuantConnect, SPY n'ayant pas encore reçu de barre de prix sur la toute première séance (`SecurityPriceZeroOrderResponseErrorAnalysis`) ; la courbe d'équité reste plate pendant les ~21 premières séances. Un rééquilibrage sur 83 est donc perdu dans la fenêtre publiée. Le correctif (warm-up de 21 barres) et les re-backtests qu'il imposera font l'objet de #21585 ; les chiffres ci-dessus incluent ce défaut, tel que mesuré.

## Lecture honnête (variante v1)

Le v1 ajuste l'allocation SPY en fonction de la volatilité réalisée : `allocation = vol_target / realized_vol`, clampée entre 30 % et 150 %. Les faiblesses observées sur 2018-2025 :

- **Signal retardé (lag de volatilité).** La volatilité réalisée augmente typiquement **après** le début d'un drawdown (krach COVID 2020, bear 2022). La réduction d'allocation arrive donc trop tard pour éviter la queue de perte, mais à temps pour rater le rebond qui suit.
- **Plancher d'exposition à 30 %.** Même en forte volatilité, la stratégie reste au moins 30 % investie — la protection à la baisse est donc partielle, tandis que le rendement est amputé côté hausse.
- **Levier en période calme.** `max_allocation = 1,50` ajoute du levier quand la vol est basse (bull markets), ce qui accrît le risque sans amélioration proportionnelle du Sharpe.
- **PSR ≈ 2 %.** Probabilité que le Sharpe annualisé dépasse le seuil (≈ 1) — ce n'est **pas** une probabilité de battre SPY. Le test de significativité des rendements excédentaires face au benchmark donne p = 0,0594 > 0,05 : aucun excédent de rendement significatif n'est établi. Le re-backtest a amélioré le profil de risque, pas le verdict — tout claim de bord serait trompeur (règle C, PR-review-discipline §C).
- **Premier rééquilibrage rejeté (défaut de bord).** Sur la toute première séance du backtest, SPY n'a pas encore de barre de prix : l'ordre de rééquilibrage est rejeté par QC et la courbe d'équité reste plate pendant ~21 séances. Le warm-up de 21 barres — la même longueur que la fenêtre de volatilité — est le correctif attendu ; il est suivi en #21585, car il touche l'algorithme et impose de nouveaux backtests.

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
