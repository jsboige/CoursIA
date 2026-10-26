# EMA-Cross-Alpha

**Classe d'actifs :** Actions US (Grandes capitalisations tech)
**ID projet Cloud :** 28885488

## Description

Stratégie alpha de croisement EMA basée sur le framework, sur 5 grandes valeurs tech (AAPL, MSFT, GOOGL, AMZN, NVDA).
Utilise le framework QuantConnect Alpha Model avec `EMACrossAlpha` (fast=20, slow=50) et un rebalancement quotidien du portefeuille via `MultiStrategyPCM`.

Chaque jour, le modèle alpha émet pour chaque action un insight UP valable un jour de bourse tant que l'EMA rapide reste au-dessus de l'EMA lente, et un insight FLAT sinon. La ligne est donc détenue pendant toute la durée de la tendance, pas seulement le jour du croisement. Le module de construction de portefeuille répartit le capital entre les actions en tendance.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud :** créer un projet, y copier `main.py` et `alpha_models.py`, attacher le projet `SharedPCM` en bibliothèque (geste « Add Library », cf. README de `SharedPCM`), puis lancer le backtest. Le projet cloud 28885488 porte un autre code que celui du dépôt ([#22654](https://github.com/jsboige/CoursIA/issues/22654)) : ses résultats ne décrivent pas cette version.

## Métriques de backtest (2015-2024)

Backtests QC Cloud du 2026-10-26, du 2015-01-01 au 2024-12-31, avec le capital de départ et le modèle de courtage déclarés dans `main.py`. Le code mesuré est celui du dépôt (`main.py`, `alpha_models.py`, `SharedPCM/pouches_pcm.py`), sans modification. Deux contrôles partagent la fenêtre, le capital et les frais : les cinq mêmes actions détenues à poids égaux et rééquilibrées le premier jour de bourse de chaque mois, puis SPY seul. La règle de lecture a été fixée avant le lancement ([#22654](https://github.com/jsboige/CoursIA/issues/22654#issuecomment-6416680701)).

| Métrique | Stratégie | Mêmes titres, détention passive | SPY |
|----------|-----------|---------------------------------|-----|
| Sharpe (QC) | 1,12 | 1,134 | 0,536 |
| CAGR | 35,7 % | 37,3 % | 13,0 % |
| Pire baisse | 37,4 % | 41,7 % | 33,7 % |
| Ordres | 3812 | 500 | 2 |

Backtests : `53725277efdb46e58d4d04f3083c2d78` (stratégie), `16ff085263bd75e752f8f6e915da3da0` (détention passive), `c0967e1598a659a37a50aaff8006b02a` (SPY). Le Sharpe est celui qu'affiche QC, qui retranche un taux sans risque.

> **Lecture honnête** : le Sharpe de la stratégie (1,12) ne dépasse pas celui de la détention passive des mêmes titres (1,134). Sur cette fenêtre, le résultat vient donc du choix des titres, et le filtre EMA n'apporte rien de mesurable. Ce choix est rétrospectif : la liste AAPL, MSFT, GOOGL, AMZN, NVDA a été écrite après coup, parmi des valeurs dont la hausse sur 2015-2024 était connue. La détention passive bat SPY pour cette seule raison, sans aucun signal. Le filtre réduit la pire baisse (37,4 % contre 41,7 %) avec plus de sept fois plus d'ordres ; ce n'est pas le critère de la règle de lecture, et un écart sur une seule fenêtre ne suffit pas à en faire une propriété du filtre.
>
> **Anciens chiffres** : la version précédente de ce README annonçait un Sharpe de -0,01 pour 314 ordres (backtest `8119728de11270cec45b8db81ed30a0b` du 2026-08-05). Ce backtest venait du projet cloud 28885488, dont le code diffère de celui du dépôt : il ne décrivait pas cette version.

## Fichiers

- `main.py` - Point d'entrée de la stratégie (modèle alpha du framework)
- `alpha_models.py` - Implémentation de EMACrossAlpha
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1, tranche dedup)
- `quantbook.ipynb` - Notebook de recherche

## Références

- Framework QC : pattern Alpha Model + Portfolio Construction
- Réf : Brock et al. (1992), moving average trading rules
