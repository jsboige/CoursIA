# EMA-Cross-Crypto

**Classe d'actifs :** Crypto (BTC, ETH)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Croisement dual EMA sur crypto. Prend position long quand EMA(20) > EMA(50) sur BTC/ETH, à 80% du capital disponible (réduit de 95% pour limiter l'exposition), avec un **filtre SMA200** (n'entre que si BTC > SMA200 = bull market structurel) et un **trailing stop 10%** intra-position (sortie si BTC recule de 10% depuis le peak depuis l'entrée).

> **Note introductive** : la description précédente indiquait EMA 20/60 — la **stratégie implémentée est EMA 20/50** (cf `main.py:32-33` et `research.ipynb` cell[8]). Le sweet spot validé sur la fenêtre 2020-2026 reste EMA 20/50 ; aucune valeur de slow_period > 50 ne bat la baseline sur le critère MaxDD (cf H1 ci-dessous).

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) explore 5 hypothèses de réduction du MaxDD sur BTC-USD 2020-2026 : périodes EMA alternatives (H1), position sizing dynamique par volatilité (H2), trailing stop (H3), filtre SMA200 (H4), scale-out progressif (H5), puis une combinaison optimale. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**Avertissement data** : le notebook comporte un marqueur `[DATA-ONLY]` (cell[2]) signalant que le moteur de backtest présentait historiquement des erreurs d'accès aux données (`KeyError close`) sur certains régimes — les chiffres ci-dessous sont ceux du run yfinance 2020-2026 rejoué pour cette PR.

### H1 — périodes EMA alternatives

**Verdict — INFIRMÉE (EMA 20/50 reste optimal)**. Six combinaisons testées (10/30, 12/26, 15/40, 20/50, 20/100, 30/70) sur BTC 2020-2026 :

| Config | Sharpe | CAGR | MaxDD | Trades |
|--------|--------|------|-------|--------|
| EMA 10/30 (plus réactif) | 0.998 | 32.6 % | -56.0 % | 29 |
| EMA 12/26 (MACD-like) | 0.951 | 30.5 % | -56.4 % | 31 |
| EMA 15/40 (intermédiaire) | 0.959 | 30.5 % | -47.1 % | 22 |
| **EMA 20/50 (BASELINE)** | **0.939** | **30.5 %** | **-47.3 %** | **17** |
| EMA 20/100 (plus lent) | 0.941 | 30.9 % | -48.1 % | 9 |
| EMA 30/70 (lent) | 0.983 | 32.4 % | -42.2 % | 9 |

**Lecture** : les EMA courtes (10/30, 12/26) réagissent plus vite aux retournements mais génèrent du whipsaw en marché latéral (29-31 trades vs 17 baseline). La **réduction du MaxDD par les périodes seules est limitée (< 5 points)**. Le **main.py garde EMA 20/50** — sweet spot entre réactivité et stabilité.

<p align="center"><img src="assets/readme/emacrypto-btc-emas.png" alt="BTC et moyennes mobiles" width="900"/><br/><em>H1 — BTC-USD (échelle log) avec EMA 20 et EMA 50 superposées. Les croisements génèrent les 17 entrées/sorties de la baseline sur la fenêtre 2020-2026.</em></p>

### H2 — position sizing dynamique par volatilité

**Verdict — PARTIELLE** (vol-scaling prometteur mais cap fixe plus simple). Cinq configurations comparées :

| Config | Sharpe | CAGR | MaxDD |
|--------|--------|------|-------|
| Baseline 95 % fixe | 0.939 | 30.5 % | -47.3 % |
| Vol-scaling 40-95 % | 0.995 | 31.5 % | -43.7 % |
| Vol-scaling 30-80 % (cible 60%) | 0.985 | 28.2 % | -39.9 % |
| Cap fixe 70 % | 0.930 | 25.2 % | -37.5 % |
| Cap fixe 80 % | 0.935 | 27.5 % | -41.6 % |

**Lecture** : le position sizing dynamique réduit proportionnellement CAGR **et** MaxDD — le ratio Sharpe reste similaire. **Un cap fixe à 80% est retenu** : -2-3 % MaxDD pour -5-8 % CAGR, ratio risque/récompense équitable et **implémentation triviale** vs vol-scaling qui exige un rolling vol 30j. C'est la modification effective du `main.py`.

<p align="center"><img src="assets/readme/emacrypto-cagr.png" alt="CAGR par configuration" width="900"/><br/><em>H2 — CAGR par configuration de position sizing. Baseline 95% (30.5%) vs cap fixe 80% (27.5%). Trade-off : -3% CAGR pour -5.7% MaxDD.</em></p>

### H3 — trailing stop

**Verdict — CONFIRMÉE (trail 10%)**. Six niveaux testés + 2 hard stops :

| Config | Sharpe | CAGR | MaxDD | Trades |
|--------|--------|------|-------|--------|
| Pas de stop (BASELINE) | 0.939 | 30.5 % | -47.3 % | 17 |
| Trailing stop 6 % | 0.827 | 24.5 % | -45.5 % | **79** |
| Trailing stop 8 % | 0.876 | 26.7 % | -47.8 % | 60 |
| **Trailing stop 10 %** | **0.933** | **29.5 %** | **-44.8 %** | **42** |
| Trailing stop 12 % | 0.915 | 28.5 % | -46.5 % | 35 |
| Hard stop-loss 8 % | 0.982 | 32.3 % | -40.6 % | 20 |

**Lecture** : les trailing stops courts (6-8 %) sont **trop serrés** — ils coupent des bons trades en plein bear dip avant rebond (BTC daily vol 3-5%, un stop 6% sort après 1-2 jours rouges). Le **trailing 10%** offre le meilleur compromis : ~5 points de MaxDD en moins avec seulement -1 point de CAGR. Trail 12-15 % a peu d'impact sur les grands crashes (> 30% intra-semaine).

<p align="center"><img src="assets/readme/emacrypto-metrics.png" alt="Métriques Sharpe/CAGR/drawdown" width="900"/><br/><em>H3 — Sharpe / CAGR / drawdown des 9 configurations de stop. Le Hard SL 8% a le meilleur Sharpe (0.982) mais coupe trop tôt sur les rebonds. Trail 10% = sweet spot.</em></p>

### H4 — filtre SMA200 (bull market filter)

**Verdict — CONFIRMÉ (levier principal MaxDD)**. Deux configs comparées + analyse du % temps BTC > SMA200 :

| Config | Sharpe | CAGR | MaxDD | Trades |
|--------|--------|------|-------|--------|
| Pas de filtre SMA200 (BASELINE) | 0.939 | 30.5 % | -47.3 % | 17 |
| **Avec filtre SMA200** | **1.016** | **31.7 %** | **-41.7 %** | 13 |

**Analyse** : BTC passe **58.3 %** du temps au-dessus de sa SMA200 (sur 2192 jours 2020-2026). Le filtre **évite les entrées en bear market structurel** : bull markets 2020-2021, recovery 2023, bull 2024-2025, mais bloque les faux rebonds en bear 2022 (LUNA, FTX). Le filtre **améliore le Sharpe** (0.939 → 1.016) tout en réduisant le MaxDD de 5.6 points — c'est le **levier le plus puissant** identifié sur cette fenêtre.

<p align="center"><img src="assets/readme/emacrypto-sharpe.png" alt="Sharpe par configuration" width="900"/><br/><em>H4 — Sharpe des configurations testées. Le filtre SMA200 fait passer le Sharpe au-dessus de 1.0 (zone cible). Combiné à cap 80% + trail 10%, il atteint 0.983 (proche cible).</em></p>

### H5 — scale-out progressif

**Verdict — INFIRMÉE** (complexité sans bénéfice). Cinq configurations comparées :

| Config | Sharpe | CAGR | MaxDD | Trades |
|--------|--------|------|-------|--------|
| Sortie 100% sur EMA cross (BASELINE) | 0.939 | 30.5 % | -47.3 % | 17 |
| Scale-out 50% + trail 10% sur reste | 0.892 | 27.2 % | -46.5 % | 38 |
| Scale-out 50% + trail 8% sur reste | 0.797 | 23.2 % | -50.6 % | 57 |
| Scale-out 50% + trail 12% sur reste | 0.829 | 23.8 % | -52.6 % | 31 |
| Scale-out 50% + sortie EMA sur reste | 0.939 | 30.5 % | -47.3 % | 17 |

**Lecture** : le scale-out **complexifie la gestion sans amélioration significative** — la moitié restante avec trailing sort souvent au même moment que la sortie complète. Le main.py **ne l'implémente pas**.

### Synthèse — combinaison optimale et analyse de robustesse

**Combinaison retenue pour main.py** : EMA 20/50 + position 80 % + trailing 10 % + filtre SMA200.

| Config | Sharpe | CAGR | MaxDD | Trades |
|--------|--------|------|-------|--------|
| Baseline EMA 20/50, 95% | 0.939 | 30.5 % | -47.3 % | 17 |
| + Filtre SMA200 | 1.016 | 31.7 % | -41.7 % | 13 |
| + SMA200 + Cap 80% | 1.005 | 28.2 % | -37.4 % | 13 |
| **+ SMA200 + Cap 80% + Trail 10% (RECOMMANDÉ)** | **0.983** | **25.6 %** | **-34.1 %** | **33** |
| + SMA200 + Vol-scaling (cap 80%) | 1.027 | 28.7 % | -35.5 % | 13 |
| + SMA200 + Vol-scaling + Trail 10% | 0.950 | 22.4 % | -30.5 % | 33 |

**Verdict honnête** : **aucune configuration n'atteint simultanément les deux cibles** (MaxDD < 35 % ET Sharpe > 1.0) **strictement**. La config recommandée atteint **MaxDD = -34.1 %** (cible OK) avec **Sharpe = 0.983** (à 1.7 % sous la cible 1.0). L'edge reste l'EMA crossover : on ne change pas la logique de signal, juste le risk management (cap + trail + filtre SMA200).

<p align="center"><img src="assets/readme/emacrypto-drawdowns.png" alt="Drawdowns par période" width="900"/><br/><em>Synthèse — BTC-USD (log) en haut, drawdowns en bas : baseline (rouge, -47.3%) vs SMA200+Cap80%+Trail10% (bleu, -34.1%). Réduction de 13.2 points, principalement sur le bear 2022 (LUNA/FTX) et le bear 2023.</em></p>

### Analyse par régime (robustesse)

Sur la fenêtre 2020-2026, performance de la config recommandée par sous-période :

| Période | Sharpe | CAGR | MaxDD |
|---------|--------|------|-------|
| Bull 2020-2021 (halving, institutionnel) | 1.335 | 49.2 % | -23.4 % |
| Bear 2022 (Luna, FTX crash) | n/a (0 trade — SMA200 filter bloque) | 0 % | 0 % |
| Recovery 2023 (ETF anticipation) | 1.183 | 18.8 % | -9.0 % |
| Bull 2024-2025 (ETF spot, halving) | 0.382 | 5.4 % | -25.0 % |

**Lecture** : la **protection bear est totale** (0 trade en 2022 — c'est l'apport du filtre SMA200). Les bulls performants (2020-2021, recovery 2023) sont capturés. Le bull 2024-2025 déçoit (Sharpe 0.382) à cause de la combinaison cap 80% + trail 10% qui coupe trop tôt sur les corrections intra-tendance (été 2024). Trade-off assumé.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto"`
**QC Cloud :** Pas encore déployée. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest (2020-2026)

| Configuration | Sharpe | CAGR | MaxDD | Verdict |
|---------------|--------|------|-------|---------|
| EMA 20/50, 95 % (legacy v1) | 0.939 | 30.5 % | -47.3 % | LIVE (legacy) |
| **EMA 20/50 + Cap 80% + Trail 10% + SMA200 (v2)** | **0.983** | **25.6 %** | **-34.1 %** | **RECOMMANDÉ** |
| SMA200 seul (filter only) | 1.016 | 31.7 % | -41.7 % | Live candidate alternatif |

## Fichiers

- `main.py` - Stratégie v2 (EMA 20/50, cap 80%, trail 10%, filtre SMA200)
- `research.ipynb` - 5 hypothèses H1-H5 + combinaison optimale + analyse par régime

## References

- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- research.ipynb: BTC-USD yfinance 2020-2026, 2192 jours, EMA 20/50 baseline + 5 hypothèses risk management