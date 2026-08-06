# Multi-Layer-EMA — Stratégie crypto multi-indicateurs (EMA + RSI + Bollinger + ATR)

**Classe d'actifs :** Crypto (BTCUSDT, ETHUSDT, LTCUSDT sur Binance)
**Résolution :** Quotidienne
**Cloud project ID :** 28433748
**Période backtestée :** 2018-01-01 → 2024-12-31

## Description

Stratégie crypto multi-indicateurs combinant tendance EMA, RSI, bandes de Bollinger et filtre de volatilité ATR. L'entrée exige un croisement EMA (rapide/lente) **confirmé** par les conditions RSI et Bollinger, avec un **gate de volatilité ATR** (on ne trade pas quand la volatilité annualisée du BTC dépasse 60 %).

**Note** : malgré le nom du répertoire, cette stratégie **n'est pas** un simple alignement multi-couches EMA sur actions US. C'est une stratégie crypto complète à plusieurs indicateurs techniques — le nom reflète l'historique du répertoire, pas la stratégie déployée.

**Version anglaise préservée** : [README.en.md](README.en.md).

## Logique de la stratégie

| Composant | Paramètres | Rôle |
|-----------|------------|------|
| Croisement EMA | Rapide 10 / Lente 50 (quotidien) | Direction de tendance |
| RSI | 14 périodes (Wilder) | Filtre surachat/survente |
| Bandes de Bollinger | 20 périodes, 2σ | Contexte de mean-reversion |
| Filtre volatilité ATR | 14 périodes, seuil 60 % (annualisé quotidien) | Sauter les régimes haute-volatilité |
| Trailing stop | 92 % | Sécuriser les gains |
| Stop fixe | 88 % | Protection du capital |
| Take profit | 125 % | Objectif de sortie |

## Backtest réel (QC Cloud, frais IBKR crypto inclus)

Vérifié sur QC Cloud (project 28433748, 2018-01-01 → 2024-12-31). Backtest de confirmation frais 2026-08-06 : **les métriques documentées sont confirmées**.

| Métrique | Valeur | (backtest frais 2026-08-06) |
|----------|--------|------------------------------|
| Sharpe ratio | 0.798 | **0.799** (confirme) |
| CAGR | 24.99 % | **24.99 %** (confirme) |
| Drawdown max | 57.1 % | **57.1 %** (confirme) |
| Ordres exécutés | 196 | **196** (confirme) |
| PSR | — | **19.26 %** |
| Rendement total net | — | 377.4 % |

| Configuration | Valeur |
|---------------|-------|
| Actifs | BTCUSDT, ETHUSDT, LTCUSDT (Binance) |
| Résolution | Quotidienne |
| Positions max | 3 |
| Stop loss | Trailing 92 %, Fixe 88 % |
| Take profit | 125 % |

### Lecture honnête — CAGR élevé, drawdown à capitulation, skill faible-moderée

- **CAGR 24.99 %** sur 2018-2024 — rendement absolu élevé, mais largement porté par l'ascendance structurelle de BTC/ETH sur cette période (BTC a fait ~5x sur la fenêtre). La stratégie **sur-performe** le buy-and-hold BTC en drawdown (elle sort pendant les crashs via le gate ATR) mais ne le bat pas forcément en rendement brut.
- **Drawdown max 57.1 %** — c'est la signature d'un actif crypto. Même avec trailing stop 92 % et filtre ATR, le drawdown atteint -57 % : les gaps de session crypto (24/7, pas de circuit-breaker) percent les stops. **C'est inacceptable pour un portefeuille réel** mais pédagogiquement honnête : un stop à 92 % ne protège pas contre un gap de -40 % en une bougie. À comparer au drawdown d'une action US (~15-34 %) pour mesurer le coût du risque crypto.
- **PSR 19.26 %** — supérieur au Trend-Following (0.66 %) et au DualMomentum (5.98 %) : la probabilité que le Sharpe soit statistiquement > 0 est modérée. **Mais** 19 % reste sous le seuil conventionnel de 50 % — le rendement n'est pas une preuve forte de skill ; une part substantielle vient de la dérive haussière crypto.
- **Gate ATR 60 %** : c'est l'innovation pédagogique principale — sauter les régimes de volatilité extrême (COVID mars 2020, crash Luna mai 2022, FTX nov 2022) évite de trader du bruit. Le filtre est **vérifiable** : comparer le drawdown avec/sans gate isole sa valeur défensive.

**Conclusion honnête** : ne PAS présenter le CAGR 24.99 % comme de l'alpha. C'est un **beta crypto filtré** (gate ATR + stops) qui réduit le drawdown vs buy-and-hold mais reste exposé à la dérive haussière de l'actif sous-jacent. Pédagogiquement : illustration des **limites des stops en marché gap-prone** (57 % de drawdown malgré stop 92 %) et du **filtrage par régime de volatilité**.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA"`
**QC Cloud :** Déployé comme project 28433748.

## Fichiers

- `main.py` — Stratégie (classe `OptimizedCryptoAlgorithm`).
- `config.json` — Configuration.
- `quantbook.ipynb`, `research.ipynb` — Recherche (analyse des signaux).
- `ml_ema_analysis.png` — Figure d'analyse.

## Concepts enseignés

- **Multi-indicateur avec confirmation** : un croisement EMA seul est bruité ; exiger RSI + Bollinger le filtre.
- **Gate de volatilité ATR** : ne pas trader quand la volatilité annualisée > seuil = filtrer les régimes non-informatifs.
- **Limites des stops en marché gap-prone** : un trailing stop 92 % ne vaut rien contre un gap de -40 % (drawdown 57 % malgré le stop) — leçon sur le risque crypto 24/7.
- **Probabilistic Sharpe Ratio (PSR)** : un CAGR élevé sur un actif à forte dérive haussière (crypto) ne prouve pas le skill (PSR 19 %).
- **Honnêteté métrique** : backtest frais de confirmation — les métriques documentées sont stables/reproductibles (Sharpe 0.798→0.799).
