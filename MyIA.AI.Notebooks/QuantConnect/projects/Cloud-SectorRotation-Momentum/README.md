# Cloud-SectorRotation-Momentum

**Classe d'actifs :** Actions, Obligations, Matières premières (rotation d'ETF)

**ID projet Cloud :** 30821748

## Description

Trend-following pondéré par momentum sur un univers de 5 ETF (QQQ, SPY, EFA, GLD, IWM) avec SHY comme équivalent cash défensif. Utilise un double filtre (prix au-dessus du SMA200 **et** momentum positif sur 6 mois / 126 jours de cotation) pour sélectionner les actifs en tendance, puis alloue proportionnellement à leurs scores de momentum mesurés par taux de variation (ROC). Rebalance tous les 21 jours de bourse. Brokerage Interactive Brokers (frais réels), benchmark SPY.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-SectorRotation-Momentum/main.py
```

### QC Cloud
Projet 30821748. Téléverser `main.py`, compiler et lancer un backtest. Période codée en dur : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630 ; le code ne fixe pas de date de fin mobile, donc la fenêtre est figée par les dates du source).

## Métriques de backtest

Backtest frais via QC Cloud MCP, 2026-08-07 (`SectorRotation-honest-read-2026-08`, 1761 dates négociables, 345 ordres) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **−0,029** | quasi nul, légèrement négatif |
| CAGR | **2,118 %** | sous le risque-free sur la période |
| Drawdown max | **42,700 %** | catastrophique |
| Profit net total | **15,812 %** (≈ +12 369 $ sur 100 k $) | sur ~7 ans |
| PSR (Probabilistic Sharpe Ratio) | **0,050 %** | performance non distinguable du bruit |
| Ordres | 345 (~49/an) | turnover modéré |

**Verdict : NO-BEATS.** La stratégie ne bat pas le benchmark buy-and-hold SPY, avec un risque bien supérieur. Sur 2018-2025, SPY buy-and-hold ressort à un CAGR à deux chiffres pour un drawdown max de l'ordre de 25-34 % (krach COVID 2020 + bear market 2022) ; ici le CAGR tombe à ~2 % pour un drawdown de 42,7 %. Ajusté au risque (Sharpe), la stratégie détruit de la valeur.

## Lecture honnête

Le double filtre (SMA200 + momentum 126 j positif) et la pondération proportionnelle au momentum ne protègent pas dans les régimes adverses du 2018-2025 :

- **Concentration sur le momentum haussier.** L'allocation proportionnelle au ROC surexpose les actifs les plus volatils en hausse ; lorsque le momentum s'inverse (Q4 2018, COVID 2020, bear 2022), ces positions amplifient le drawdown. Le filtre SMA200 est réactif (il ne se déclenche qu'après cassure), donc le passage en défensif SHY arrive trop tard.
- **SHY défensif = trop tardif.** Le repli sur SHY ne se produit que lorsqu'**aucun** actif ne passe le double filtre, un signal retardé qui laisse la stratégie pleinement investie au début des drawdowns.
- **PSR ≈ 0.** Avec un PSR de 0,05 %, le Sharpe observé n'est pas statistiquement significatif : on ne peut pas distinguer ce résultat d'un tirage aléatoire. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

**Pas de re-tuning.** Re-optimiser les paramètres (lookback momentum, période de rebalancement, univers) pour récupérer un Sharpe positif sur cette seule fenêtre serait du surapprentissage jusqu'à preuve du contraire, le biais dénoncé dans l'EPIC #9768 (D2 « fenêtre non figée »). La stratégie est livrée avec ses paramètres codés tels quels, verdict honnête rendu.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation sectorielle avec allocation pondérée par momentum et double filtre de tendance (v4) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
