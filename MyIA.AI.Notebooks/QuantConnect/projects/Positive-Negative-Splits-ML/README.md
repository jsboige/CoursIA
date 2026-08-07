# Positive-Negative-Splits-ML (HandsOn Ex07) (ID: 30317350)

Stratégie ML d'événements de split sur actions du secteur technologie (US Tech). Régression linéaire entraînée mensuellement qui prédit le rendement post-split à partir du facteur de split et du momentum sectoriel (XLK ROC 22-j), puis ouvre une position dans le sens prédit avec sortie temporisée (3 jours par défaut).

## Performance (lecture vérifiée frais réels — robuste mais window-sensitive)

Frais IBKR réels (MARGIN), projet de vérification QC Cloud `Positive-Negative-Splits-ML-verify` (34902226). Backtest frais sur la fenêtre **complète du code 2015-01 → 2024-04** (9.2 ans, 2326 jours tradeables, 295 ordres) :

| Métrique | Vérifié frais réels (2015-2024) | Aligné #1630 (2018-2024) | Catalogue (stale) |
|----------|--------------------------------|--------------------------|-------------------|
| **Sharpe** | **1.066** | 1.51 | 1.736 |
| **CAGR** | **41.11 %** | 75.7 % | 90.83 % |
| **Max Drawdown** | **34.10 %** | 37.6 % | 42.4 % |
| **PSR** | **34.9 %** | 82.3 % | — |
| **Net Profit** | **+2324 %** | — | — |

**Verdict : robuste mais sensible à la fenêtre.** La stratégie tient sous frais réels IBKR (Sharpe > 1.0 sur 9 ans, edge réel confirmé), MAIS l'amplitude dépend fortement de la fenêtre : **Sharpe 1.066 / PSR 34.9 %** sur la fenêtre complète 2015-2024 vs **Sharpe 1.51 / PSR 82.3 %** sur la sous-fenêtre alignée 2018-2024 ([docs/qc/qc-comparative-backtests.md](../../../../docs/qc/qc-comparative-backtests.md) L39/L87, ✓post-#2801). Le README d'origine citait **1.736 / 90.83 %** en flat, sans caveat — valeur **non reproduite** : c'est le Sharpe catalogue pré-alignement, surestimé de +63 % vs la lecture frais-réels long-terme (1.066).

Diagnostic de la sensibilité : étendre la fenêtre de 6→9 ans fait chuter le PSR de 82.3 % → 34.9 % — l'edge est concentré sur le régime 2018-2024 (tech bull market) et s'amenuise sur la période incluant 2015-2017. Le label **« top ML leader »** du comparatif tient sur la fenêtre 6 ans, mais **ne se généralise pas** à la décennie complète. Hors période d'entraînement (premier `train` mensuel non encore prêt), `totalOrders=0` jusqu'au premier split WARNING éligible.

## Stratégie

- **Univers** : actions secteur Technologie (Morningstar sector code), résolution HOUR, RAW normalization
- **Brokerage / capital** : Interactive Brokers MARGIN, 100 000 USD
- **Modèle** : `LinearRegression` (scikit-learn), réentraîné mensuellement (lookback 4 ans), features = facteur de split + ROC sectoriel XLK 22-j
- **Exécution** : event-driven sur `SplitType.WARNING`, max 4 trades ouverts simultanément (25 % exposition cible par trade), sortie à `hold_duration=3` jours via `market_on_open_order`
- **Période de chauffe** : histoire XLK + ROC (lookback entraînement)

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Stratégie `SplitEventsAlgorithm` (LinearRegression, réentraînement mensuel) |
| `research.ipynb` | Analyse d'événements de split |

## Références

- *Hands-On AI Trading* (Jared Broad), Section 06, Example 07

---

*Performance vérifiée sous frais réels IBKR (See #1621 Phase 4 / #1630). Le Sharpe 1.736 du catalogue est une valeur **pré-alignement de fenêtre** (cf. verdict ci-dessus), pas un chiffre hors frais : ce qui change entre 1.736 et 1.066 est la période de mesure. Il surestime la stratégie de +63 % ; la lecture frais-réels long-terme (Sharpe 1.066, PSR 34.9 %) est robuste mais window-sensitive — ne se généralise pas de la sous-fenêtre 2018-2024 (PSR 82.3 %) à la décennie complète. Version anglaise préservée dans [`README.en.md`](README.en.md).*
