# All-Weather Portfolio Strategy

Portfolio multi-asset inspiré de Ray Dalio (Bridgewater Associates).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Multi-Asset |
| **Rebalancement** | Trimestriel |
| **Classes d'actifs** | Actions, Bonds, Or, Commodities |
| **Objectif** | Stabilité dans tous les environnements |

## Allocation Standard

| Actif | Allocation | ETF | Rôle |
|-------|------------|-----|------|
| Actions US | 30% | SPY | Croissance |
| Bonds Long-terme | 40% | TLT | Déflation, récession |
| Bonds Intermédiaires | 15% | IEF | Stabilité |
| Or | 7.5% | GLD | Inflation, crise |
| Commodities | 7.5% | DBC | Inflation |

## Backtest Results (2015-2023)

| Métrique | Valeur |
|----------|--------|
| Total Return | ~80-100% |
| CAGR | ~8-10% |
| Sharpe Ratio | ~0.7-1.0 |
| Max Drawdown | ~-15% à -20% |
| Volatilité | ~8-10% |

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) déroule l'analyse complète : exploration des rendements et volatilités par actif, puis quatre hypothèses testées (static vs risk parity vs tactical, rôle de DBC, fréquence de rebalancement, overlay SMA200), synthèse par comparaison des configurations et exploration de la grille de paramètres. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**Exploration.** L'analyse commence par les rendements et volatilités annualisés de chaque actif — la base sur laquelle toute allocation se construit :

<p align="center">
  <img src="assets/readme/aw-exploration.png" alt="Matrice de corrélation 5×5 des sous-jacents AllWeather (SPY/TLT/IEF/GLD/DBC) — heatmap divergente bleu-rouge (-1,00 bleu → +1,00 rouge), valeurs cellulaires lisibles : TLT↔SPY -0,18 (décorrélation actions/obligations long-terme), TLT↔IEF +0,92 (corrélation fortes obligations long/mid-terme), DBC↔SPY +0,35 (matières premières/actions modérément corrélées)." width="420"/><br>
  <em>Exploration — rendements &amp; volatilité annualisés par actif.</em>
</p>

**H1 — Static vs Risk Parity vs Tactical.** Trois schémas d'allocation sont confrontés : poids fixes, parité de risque, et allocation tactique :

<p align="center">
  <img src="assets/readme/aw-h1-parity.png" alt="Dual-panel « H1: Static vs Risk Parity vs Tactical » — panel haut = equity 2016-2026 (Static Dalio trimestriel S=0,691 DD=-23,37% en bleu ; Risk Parity 60j rolling S=0,718 DD=-18,43% en orange ; Tactical SMA200 S=0,744 DD=-15,47% en vert — Tactical domine), panel bas = drawdowns superposés (-25% min en 2022 commun aux 3 stratégies)." width="420"/><br>
  <em>H1 — Static vs Risk Parity vs Tactical.</em>
</p>

**H3 — Fréquence de rebalancement.** L'impact de la fréquence (mensuelle, trimestrielle, annuelle) sur la performance et le coût de transaction :

<p align="center">
  <img src="assets/readme/aw-h3-rebalance.png" alt="Dual-panel « H3: Rebalancing Frequency Comparison » — panel haut = equity 2016-2026 avec 3 fréquences superposées (Monthly/Quarterly/Semi-Annual, toutes S=0,817 DD=-23,9% identiques, seul le vert Semi-Annual visible car courbes indiscernables), panel bas = drawdowns -25% min en 2022. Résultat : la fréquence de rebalancement n'a pas d'impact mesurable sur cette stratégie — invariance temporelle du Static Dalio." width="420"/><br>
  <em>H3 — fréquence de rebalancement.</em>
</p>

**H4 — Overlay tactique SMA200.** Un overlay SMA200 réduit l'exposition lors des tendances baissières :

<p align="center">
  <img src="assets/readme/aw-h4-sma200.png" alt="Dual-panel « H4: SMA200 Tactical Overlay – Reduction Factors » — panel haut = equity 2016-2026 avec 5 niveaux de réduction tactique (No overlay 0% S=0,817 DD=-23,9% en bleu ; red=25% S=0,846 DD=-20,1% en orange ; red=50% S=0,858 DD=-16,2% en vert OPTIMAL ; red=75% S=0,834 DD=-13,6% en rouge ; red=100% S=0,763 DD=-11,6% en violet), panel bas = drawdowns -25% min en 2022. Sweet-spot 50% maximise le Sharpe tout en divisant le DD par ~1,5×." width="420"/><br>
  <em>H4 — overlay tactique SMA200.</em>
</p>

**Synthèse.** La comparaison des configurations par Sharpe et drawdown résume les trade-offs entre rendement ajusté du risque et profondeur des replis :

<p align="center">
  <img src="assets/readme/aw-comparison.png" alt="Scatter Pareto « H4: Risk-Return Tradeoff by SMA200 Reduction Factor » — 5 points labellés axe X Max Drawdown % (axe inversé : better right = DD plus faible à droite) vs axe Y Sharpe Ratio : 100% violet (S=0,763 DD≈11%) bas-gauche, 75% rouge (S=0,834 DD≈13%) centre-gauche, 50% vert (S=0,858 DD≈16%) centre-haut OPTIMAL, 25% orange (S=0,846 DD≈20%) centre-droite, 0% bleu (S=0,817 DD≈24%) droite. Le 50% domine en Sharpe avec DD modéré — la reduction 100% minimise le DD mais avec Sharpe dégradé." width="420"/><br>
  <em>Comparaison — Sharpe &amp; drawdown par configuration.</em>
</p>

**Grille de paramètres.** Enfin, l'exploration de la grille des paramètres identifie la zone optimale :

<p align="center">
  <img src="assets/readme/aw-grid-optimal.png" alt="Rolling 1-Year Sharpe Ratio 2016-2026 — 3 stratégies (Original Static Dalio trimestriel bleu ; Optimized Static+Tactical orange ; RP+Tactical Combo vert) : 3 lignes fortement corrélées sur toute la période, pic commun ~3,5 en 2020, dip commun ~-2 en 2022-2023, recovery ~2,5 en 2025-2026, ligne pointillée horizontale Sharpe=0. Les 3 stratégies partagent les mêmes cycles macro (post-COVID recovery 2020, bear market 2022-2023) mais l'Optimized devance Original en fin de période post-2023." width="420"/><br>
  <em>Grille optimale — exploration des paramètres.</em>
</p>

## Fichiers

```
AllWeather/
├── main.py              # Portfolio standard + Risk Parity + Tactical
├── research.ipynb       # Analyse corrélations, backtest allocations
└── README.md            # Ce fichier
```

## Variantes Incluses

### 1. Standard All-Weather
- Allocation fixe (30/40/15/7.5/7.5)
- Rebalancement trimestriel
- Seuil de drift 5%

### 2. Risk Parity
- Pondération par volatilité inverse
- Contribution égale au risque
- Favorise les bonds (faible vol)

### 3. Tactical Overlay
- Réduit l'allocation si prix < SMA 200
- Augmente le cash en période de stress
- Trade-off: moins de drawdown, moins de return

## Configuration

```python
# Allocations cibles
self.target_allocations = {
    "SPY": 0.30,   # 30% Actions
    "TLT": 0.40,   # 40% Bonds long-terme
    "IEF": 0.15,   # 15% Bonds intermédiaires
    "GLD": 0.075,  # 7.5% Or
    "DBC": 0.075   # 7.5% Commodities
}

# Paramètres
self.rebalance_threshold = 0.05  # Rebalancer si drift > 5%
```

## Philosophie

L'All-Weather est conçu pour performer dans 4 environnements :

| Environnement | Actifs performants |
|---------------|-------------------|
| Croissance ↑ | Actions |
| Croissance ↓ | Bonds |
| Inflation ↑ | Or, Commodities |
| Inflation ↓ | Bonds |

## Risques

- **Sous-performance en bull market**: Trop de bonds dilue les gains
- **Sensibilité aux taux**: Bonds souffrent quand les taux montent
- **Corrélations instables**: En crise, tout peut baisser ensemble
- **Commodities roll yield**: Contango érode les returns long-terme

## Améliorations Possibles

- Ajouter TIPS (Treasury Inflation-Protected Securities)
- Diversification géographique (VEA, VWO)
- Dynamic risk targeting
- Factor tilts (Value, Momentum)

## Références

- Ray Dalio: "Principles" (chapitre sur l'All-Weather)
- Bridgewater Associates: "The All Weather Story"
- Notebook: QC-Py-08-Multi-Asset-Strategies.ipynb
