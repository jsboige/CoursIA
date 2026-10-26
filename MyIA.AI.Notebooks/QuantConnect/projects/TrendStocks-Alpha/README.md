# TrendStocks-Alpha

**Asset class:** US Equities (Large-cap diversified)
**Cloud project ID:** 28885507

## Description

Framework-based trend-following alpha strategy on 15 large-cap stocks across sectors.
Uses `TrendStocksAlpha` with EMA(20/50) for signal and SMA(200) as trend confirmation.
Weekly rebalance via `MultiStrategyPCM`.

The strategy enters long positions when short-term EMA is above long-term EMA AND the price is above the 200-day SMA, confirming the secular uptrend.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/TrendStocks-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud :** créer un projet, y copier `main.py` et `alpha_models.py`, attacher le projet `SharedPCM` en bibliothèque (geste « Add Library », cf. README de `SharedPCM`), puis lancer le backtest. Le projet cloud 28885507 porte un autre code que celui du dépôt ([#22654](https://github.com/jsboige/CoursIA/issues/22654)) : ses résultats ne décrivent pas cette version.

## Métriques de backtest (2015-2024)

Backtests QC Cloud du 2026-10-26, du 2015-01-01 au 2024-12-31, avec le capital de départ et le modèle de courtage déclarés dans `main.py`. Le code mesuré est celui du dépôt (`main.py`, `alpha_models.py`, `SharedPCM/pouches_pcm.py`), sans modification. Deux contrôles partagent la fenêtre, le capital et les frais : les quinze mêmes actions détenues à poids égaux et rééquilibrées le premier jour de bourse de chaque mois, puis SPY seul. La règle de lecture a été fixée avant le lancement ([#22654](https://github.com/jsboige/CoursIA/issues/22654#issuecomment-6416680701)).

| Métrique | Stratégie | Mêmes titres, détention passive | SPY |
|----------|-----------|---------------------------------|-----|
| Sharpe (QC) | 0,842 | 0,905 | 0,536 |
| CAGR | 20,7 % | 21,9 % | 13,0 % |
| Pire baisse | 33,7 % | 33,8 % | 33,7 % |
| Ordres | 4883 | 985 | 2 |

Backtests : `a275a2974bce9f0503ae969ec3adc611` (stratégie), `d937f2dcbb0d88f931e5ee19f16a327f` (détention passive), `c0967e1598a659a37a50aaff8006b02a` (SPY). Le Sharpe est celui qu'affiche QC, qui retranche un taux sans risque.

**Lecture** : le Sharpe de la stratégie (0,842) ne dépasse pas celui de la détention passive des mêmes titres (0,905), et la pire baisse est la même. Sur cette fenêtre, le résultat vient donc du choix des titres, et le double filtre de tendance (EMA puis SMA200) n'apporte rien de mesurable. La liste est faite de grandes capitalisations d'aujourd'hui : c'est un biais de survie que ce contrôle ne retire pas, puisque la stratégie et la détention utilisent la même liste.

**Anciens chiffres** : la version précédente de cette section annonçait un Sharpe d'environ 0,61 sur 2020-2025, attribué au carnet `quantbook.ipynb` (attribution inscrite le 2026-10-07, #19570), et citait un run cloud à 0,512, relevé au registre `docs/qc/qc-strategies-status.md` le 2026-07-18 (tranche 8 de #1621). Le carnet ne calcule pas ce 0,61 : pour la configuration du dépôt (EMA20/50, rééquilibrage hebdomadaire), sa sortie donne 0,281, sur d'autres dates. Le run à 0,512 portait sur 2516 séances, comme la mesure ci-dessus qui donne 0,842 : il ne décrivait pas le code du dépôt.

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - TrendStocksAlpha implementation
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1, tranche dedup)
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
