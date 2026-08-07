# BTC MACD + ADX Adaptive (C#) (ID: 30751067)

Stratégie momentum BTCUSDT combinant MACD (tendance) et ADX (force) avec seuils adaptatifs par percentile (implémentation C#).

## Performance (fenêtre figée reproductible — NO-BEATS, edge non-stationnaire)

**Fix #9803 (EPIC #9768, D2 fondateur).** `Main.cs` ne fixait **aucun `SetEndDate`** : la fenêtre s'allongeait à chaque exécution (Sharpe 0.225 → 0.123 d'avril à août 2026 par le seul ajout de 101 jours de bourse). Désormais `SetEndDate(2025, 12, 31)` — borne « dernière année civile complète », défendable par sa **règle** (pas par son résultat). Le backtest est **reproductible**.

### Mesure à deux bornes (frais Binance réels, params committés Window=40 / percentiles 10/90)

| Fenêtre | Sharpe | CAGR | Profit net | MaxDD | PSR | Ordres | Jours |
|---------|--------|------|------------|-------|-----|--------|-------|
| 2019-04-01 → **2024-12-31** (sensibilité) | **0.611** | 17.54 % | 153.7 % | 72.7 % | 12.9 % | 40 | 2102 |
| 2019-04-01 → **2025-12-31** (figée, canonical) | **0.238** | 3.96 % | 30.0 % | 72.7 % | 2.1 % | 47 | 2467 |

**La trouvaille = la non-stationnarité, chiffrée.** Une seule année (2025) fait chuter le Sharpe de **0.611 à 0.238 (−61 %)**, le profit net de 154 % à 30 %, le PSR de 12.9 % à 2.1 %. L'edge était **concentré sur 2019-2024** ; 2025 le détruit. C'est la quantification concrète du verdict non-stationnaire que l'EPIC #9768 nommait sans encore le mesurer (addendum user 2026-08-07 : « l'edge était concentré et non-stationnaire »). Le choix de borne n'est **pas neutre** — d'où la mesure aux deux.

**Verdict : NO-BEATS, confirmé et désormais reproductible.** Sharpe 0.238 sur la fenêtre figée — PSR 2.1 %, statistiquement indissociable du bruit, sous-performe massivement le buy & hold BTC sur la même période, drawdown catastrophique de 72.7 %. Geler la fenêtre n'a pas sauvé la stratégie : elle reste non robuste, et la chute 2025 prouve qu'elle ne l'était pas davantage avant.

**D'où vient le 0.787 du catalogue ?** Le modèle Binance (`SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)`) est présent depuis la **première révision**. Le 0.787 est le **maximum d'un balayage à 8 variantes** lancé le 2026-04-27 sur le projet Cloud `30751067`, dont les paramètres gagnants (`adx-period=35`, `window=60`, percentiles 15/85) **n'ont jamais été réécrits dans `Main.cs`**. Le catalogue publie donc un nombre qui n'a jamais décrit ce code. Forensic complet : [#9768](https://github.com/jsboige/CoursIA/issues/9768).

Ce verdict corrobore [`RESEARCH_FINDINGS.md`](RESEARCH_FINDINGS.md) (2026-02-17) : l'approche adaptative à seuils percentile ne tient pas ses promesses — toutes les hypothèses H1-H5 rejetées, Sharpe -0.035 pour les paramètres originaux (Window=140). Les paramètres optimisés actuels (`Main.cs` : Window=40, percentiles 10/90) n'inversent pas la conclusion : 0.238 reste non robuste.

## Stratégie

- **MACD** : direction et momentum de tendance (fast 12 / slow 26 / signal 9, EMA)
- **ADX** : filtre de force de tendance (période 25) pour éviter les marchés sans direction
- **Seuils adaptatifs** : entrée long si ADX ≥ percentile 90 ET MACD haussier ; sortie si ADX < percentile 10 ET MACD baissier (fenêtre glissante 40 jours)
- **Univers / brokerage** : BTCUSDT daily, Binance compte Cash, capital 5000 USDT

## Fichiers

| Fichier | Description |
|---------|-------------|
| `Main.cs` | Implémentation C# (paramètres optimisés Window=40, percentiles 10/90) |
| `Research.ipynb` | Notebook de recherche principal |
| `research_robustness.ipynb` | Analyse de robustesse (grid search 2019-2025) |
| `RESEARCH_FINDINGS.md` | Conclusions de recherche (hypothèses H1-H5 rejetées) |
| `RESEARCH_SUMMARY.md` | Résumé exécutif |

## Source

partner-course-quant-trading/examples/CSharp-BTC-MACD-ADX (archivé après standardisation).

---

*Performance vérifiée sous frais Binance réels, fenêtre figée 2019-04-01 → 2025-12-31 (reproductible, #9803). Le Sharpe 0.787 du catalogue ne décrit pas ce code : c'est le maximum d'un balayage de paramètres jamais committé ([#9768](https://github.com/jsboige/CoursIA/issues/9768)). La lecture du code committé (Sharpe **0.238**, PSR **2.1 %**, MaxDD 72.7 %) est non robuste et ne bat pas le buy & hold — voir la section Performance ci-dessus pour la mesure de sensibilité au choix de borne (Sharpe 0.611 si la fenêtre s'arrête fin 2024). Version anglaise préservée dans [`README.en.md`](README.en.md).*
