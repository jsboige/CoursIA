# Sector ETF Momentum Rotation (ARCHIVÉE)

> **Stratégie ARCHIVÉE** (2026-04-21, cf `ARCHIVE.md`) — plafond de Sharpe mesuré **~0.48** : après 8 itérations (v1.0 → v6.2), la rotation mensuelle d'ETF sectoriels ne dépasse pas ce plafond. Statut registre : [status doc l.885](../../../../docs/qc/qc-strategies-status.md) — reclassée hors bucket Vivant (c.570).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Rotation ETF sectoriels, long-only |
| **Univers** | 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC) |
| **Signal** | Momentum skip-month (21 j) ajusté volatilité, lookback 252 j |
| **Filtre de régime** | Double SMA SPY (200 j + 20 j) ; défensif = XLP/XLU 50/50 |
| **Positions** | Top 4 (le grid `research.ipynb` montre top 2 meilleur mais surajusté) |
| **Rebalancement** | Mensuel |
| **Stop-loss** | -10 % par position |
| **Brokerage** | IBKR margin (frais réels) |

## Historique d'itérations mesuré (2015-2024)

Toutes les valeurs ci-dessous proviennent de l'historique d'itérations mesuré dans `main.py` (docstring) et `ARCHIVE.md` (exécutions Lean locales, IBKR margin). **Aucun run cloud n'est enregistré au status doc pour cette stratégie.** Les fourchettes « Sharpe ~0.8-1.0, CAGR ~11-14 % (2018-2023), univers US Large Caps Top-20 » citées par une version antérieure de ce README décrivaient une **autre stratégie** (sélection d'univers actions, cf `QC-Py-05-Universe-Selection`) : **aucun paramètre ni exécution de ce projet** ne les porte — le filtrage `num_coarse=500` / `num_fine=20` cité alors n'existe pas dans ce code.

| Version | Sharpe | CAGR | MaxDD | Changement | Verdict |
|---------|--------|------|-------|------------|---------|
| v1.0 | 0.216 | 6.5 % | 29.9 % | Rotation mensuelle baseline | |
| v2.1 | 0.411 | 10.8 % | 30.1 % | Skip-month + scores ajustés vol | Improved |
| v3.0 | 0.459 | 11.5 % | 30.0 % | Filtre double régime SMA200+SMA20 | Improved |
| **v4.0** | **0.472** | **11.1 %** | **25.8 %** | + stop-loss -10 % | **BEST** |
| v5.0 | 0.398 | — | — | Poids proportionnels | REJECTED |
| v6.0 | 0.441 | — | — | Trailing stop coupe les gagnants | REJECTED |
| v6.1 | 0.460 | — | — | TLT risk-off (MaxDD pire) | REJECTED |
| v6.2 | 0.395 | — | — | Target vol + filtre SMA50 | REJECTED |

**Conclusion mesurée** : plafond ~0.48 pour la rotation mensuelle d'ETF sectoriels (`main.py`, docstring). Cf « Why Expansion Doesn't Improve » dans `ARCHIVE.md` (plafond d'univers : 11 ETF corrélés ; alternatives risk-off épuisées ; top_n=2 surajusté).

## Demi-séances (#20286)

Quand le 3 juillet tombe un lundi, c'est à la fois le premier jour de cotation du mois et une demi-séance qui ferme à 13:00, heure de New York. Sur la fenêtre 2015-2024, c'est le cas en 2017 et en 2023. Sur la tranche de clôture d'une demi-séance, `history()` rend environ 21 barres journalières de moins que demandé (mesuré dans #20286 sur un autre projet). `_momentum_score` demandait `lookback + 5` barres et rejetait le titre sous `lookback`. Il restait moins de `top_n` scores, et `rebalance` sortait sans rien écrire dans le journal. Juillet 2017 et juillet 2023 passaient sans rééquilibrage : 118 mois sur 120.

Correctif dans `main.py` : `_momentum_score` demande le double de barres et garde les `lookback + 5` dernières. Sur une séance pleine, ce sont les mêmes barres qu'avant. Aucune ligne du journal ne montre l'historique court : la cause se déduit du code, et le retour des mois manquants avec ce seul changement la confirme.

Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20286, c.6115594357](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6115594357)) :

| Fenêtre | Variante | Mois rééquilibrés | Sharpe | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 | avant | 118 / 120 | 0.501 | 11.177 % | 25.8 % | 460 | `b583034cbc894ea49c2a1731cc957676` |
| | après | 120 / 120 | 0.516 | 11.471 % | 25.8 % | 471 | `0037e172a9db4f2df5e400c71ce3add3` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 19 / 19 | 0.050 | 5.961 % | 12.6 % | 85 | `c37efdbb5015a261ee967300dff55a0d` |
| | après | 19 / 19 | 0.050 | 5.961 % | 12.6 % | 85 | `8393d375f5277864dbe2e8ad386bae2b` |

Sharpe calculé par QC, taux sans risque inclus. Les quatre prédictions fixées d'avance ont tenu :

- les rééquilibrages du 2017-07-03 et du 2023-07-03 reviennent, et leurs ordres partent à la clôture de 13:00 ;
- avant le 2017-07-03, les ordres sont identiques (date, titre, quantité) ;
- les dates de rééquilibrage sont celles d'avant, plus les deux lundis ;
- hors échantillon, aucun mois ne commence par une demi-séance, et les deux variantes sont identiques au centime.

À partir de juillet 2017, la trajectoire diverge : les mois suivants rééquilibrent depuis d'autres positions. L'écart de Sharpe (+0.015) reste sous le seuil de 0.05 fixé d'avance, et le chiffre de v4.0 du tableau ci-dessus n'est pas réécrit. Ce n'est pas un verdict : la stratégie reste archivée.

## Logique (implémentée dans `main.py`)

1. **Univers** : 11 ETF sectoriels — pas de coarse/fine filter actions
2. **Signal** : momentum skip-month (prix J-21 vs J-252), ajusté par la volatilité sectorielle
3. **Régime** : SPY < SMA200 ou < SMA20 → portefeuille défensif XLP/XLU 50/50
4. **Sélection** : top 4 par score, equal-weight
5. **Stop-loss** : -10 % par position

## Paramètres configurables (`main.py:53-57`)

```python
self.top_n = 4           # Nombre de positions
self.lookback = 252      # Lookback momentum (12 mois)
self.skip_days = 21      # Skip-month (évite le momentum 1M inversé)
self.stop_loss_pct = -0.10
```

## Fichiers

```
MomentumStrategy/
├── main.py              # SectorMomentumETFRotation (v4.0)
├── alpha_model.py       # Alpha model framework
├── config.json          # Config cloud
├── config_framework.json
├── research.ipynb       # Grid search (top_n, lookback, risk-off)
├── quantbook.ipynb
├── ARCHIVE.md           # Rapport d'archivage (plafond ~0.48)
└── README.md            # Ce fichier
```

## Risques documentés (`ARCHIVE.md`)

- **Plafond d'univers** : 11 ETF sectoriels fortement corrélés limitent la diversification
- **Sensibilité paramétrique** : top_n=2 maximise le backtest mais surajuste ; top_n=4 retenu pour la robustesse
- **Ajustement vol** : pénalise les secteurs haute vol (XLE, XLF) souvent les plus forts en momentum absolu

## Références

- Jegadeesh & Titman (1993) : « Returns to Buying Winners and Selling Losers »
- Faber (2007), Asness (2013) — cf `main.py` (docstring)
