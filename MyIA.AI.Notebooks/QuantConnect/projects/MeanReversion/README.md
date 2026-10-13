# MeanReversion

**Classe d'actifs :** ETF sectoriels américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de retour à la moyenne à court terme sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Chaque jour à 10:00 (New York), elle achète les ETF les plus survendus (RSI(14) < 40) dont le rendement sur trois mois n'est pas inférieur de plus de 10 points à celui de SPY. Au plus 4 positions à 25 % chacune.
Sortie : RSI > 65, 15 jours de détention, ou stop-loss à −10 %.

Filtre de régime SMA200 sur SPY : en marché baissier, les nouvelles positions prennent 12,5 % au lieu de 25 % ; les positions ouvertes ne sont pas soldées.
Un ETF qui a moins de 63 séances d'historique (XLRE fin 2015, XLC en 2018) reçoit un rendement nul sur trois mois.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud :** pas de projet cloud persistant. Le backtest ci-dessous a tourné dans un projet de mesure (37661669) ; copier `main.py` dans un nouveau projet QC Cloud pour relancer.

## Métriques (backtest QC Cloud, 2015-01-01 → 2024-12-31, #20346)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0,675 |
| CAGR | 10,42 % |
| Max Drawdown | 11,1 % |
| PSR | 8,7 % |
| Ordres | 704 |
| Rendement net | +169,6 % |

Backtest `ad190cab96bc` (projet 37661669, `main.py` sha256 `0b28658c42c7`, le code de ce dossier). **Pas de verdict** : les paramètres v5.x ont été choisis sur cette même période (historique du docstring de `main.py`), et un seul backtest ne dit rien d'un avantage hors échantillon. Le Sharpe QC inclut un taux sans risque. Ce backtest ne reproduit pas les chiffres que le docstring donne pour la v5.2 (Sharpe 0,810).

Avant #20346, le code plantait le 2018-09-11 sur une erreur d'index (XLC, trop jeune pour la garde d'historique) : il ne pouvait produire aucune métrique sur sa fenêtre codée. Les chiffres que ce README citait auparavant (sweep #1621, Sharpe −0,082, verdict BROKEN ; reproduction QuantBook du code v4.0, Sharpe 0,365) ne portent pas sur le code v5.2.

## Fichiers

- `main.py` - Stratégie (v5.2, retour à la moyenne sur ETF sectoriels)
- `research.ipynb` - Recherche : pivot stocks -> ETF sectoriels, hypothèses H1-H8 (RSI, stop-loss, période de détention...)
- `quantbook.ipynb` - Reproduction QuantBook de l'analyse exploratoire sur les ETF sectoriels (données natives QC)

## Références

- Jegadeesh (1990), « Evidence of Predictable Behavior of Security Returns »
- De Bondt & Thaler (1985), « Does the Stock Market Overreact? »
