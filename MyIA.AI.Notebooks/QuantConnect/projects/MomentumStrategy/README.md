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

Quand le 3 juillet tombe un lundi, c'est à la fois le premier jour de cotation du mois et une demi-séance qui ferme à 13:00, heure de New York. Sur la fenêtre 2015-2024, c'est le cas en 2017 et en 2023. Sur la tranche de clôture d'une demi-séance, `history()` rend moins de barres journalières que demandé : 213 sur 257, soit 44 de moins, pour chacun des secteurs cotés le 2017-07-03 et le 2023-07-03 à 13:00 (lecture directe par une sonde de journal, [#20264](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6187771409) ; #20286 l'avait estimé à environ 21 d'après un autre projet). `_momentum_score` demandait `lookback + 5` barres et rejetait le titre sous `lookback`. Il restait moins de `top_n` scores, et `rebalance` sortait sans rien écrire dans le journal. Juillet 2017 et juillet 2023 passaient sans rééquilibrage : 118 mois sur 120.

Correctif dans `main.py` : `_momentum_score` demande le double de barres et garde les `lookback + 5` dernières. Sur une séance pleine, ce sont les mêmes barres qu'avant. Le journal de `main.py` ne montre pas l'historique court : la cause se déduisait du code, et le retour des mois manquants avec ce seul changement la confirmait. La sonde de #20264 l'a depuis lu directement.

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

## Variante Framework (#20264)

`main_framework.py` et `alpha_model.py` portent la même stratégie dans l'Algorithm Framework de QC. `SectorMomentumAlpha` émet la sélection mensuelle et l'arrêt quotidien, et `InsightWeightingPortfolioConstructionModel` en fait des cibles de portefeuille. Sur QC, `main_framework.py` s'envoie sous le nom `main.py`, à côté de `alpha_model.py`.

Un recensement de cette variante ([#20264, c.6187771409](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6187771409)) y a trouvé trois défauts :

- les `FLAT` partaient sans poids, et ce modèle de construction ignore un insight sans poids. Une ligne désélectionnée n'était jamais vendue : les cibles s'additionnaient, l'exposition montait à deux fois les fonds propres, et le compte sur marge refusait les achats suivants ;
- l'arrêt à -10 % ne s'armait que sur les lignes achetées dans le mois, et son `FLAT` d'un jour était ignoré lui aussi ;
- l'alpha gardait le défaut des demi-séances corrigé ci-dessus dans `main.py`.

Le correctif émet les `FLAT` avec `weight=0`, pour la même durée qu'un insight mensuel (30 séances). Il arme l'arrêt sur toute ligne retenue : au prix courant pour une ligne neuve, au prix moyen de la position pour une ligne déjà détenue sans prix d'entrée. Il demande l'historique en double, comme `main.py`, et fixe le type de compte explicitement. Les tests de `tests/test_alpha_model.py` couvrent ces points sans Lean (`python -m pytest tests/test_alpha_model.py`, depuis ce dossier) ; contre l'ancien alpha, 7 des 10 échouent.

Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20264, c.6215021287](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6215021287), résultat [c.6215340530](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6215340530)) :

| Fenêtre | Variante | Sharpe | CAGR | Pire baisse | Ordres | Achats refusés | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 | Framework avant correctif | 0.468 | 14.217 % | 45.0 % | 5051 | 2098 | `d1b3fbf68553744d02178e220d5cd97d` |
| | Framework corrigé (`main_framework.py`) | 0.511 | 11.388 % | 25.8 % | 2261 | 0 | `ed4ddbc7d41d175ded7d87bc2f67f2b9` |
| | Framework corrigé, rééquilibrage aux seuls changements d'insights | 0.514 | 11.436 % | 25.7 % | 743 | 0 | `16b787c2052b7910cd3a39124624c45c` |
| | autonome (`main.py`) | 0.516 | 11.471 % | 25.8 % | 471 | — | `0037e172a9db4f2df5e400c71ce3add3` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | Framework corrigé (`main_framework.py`) | 0.033 | 5.696 % | 12.6 % | 417 | 0 | `7eafc11c63cdaca93d1297d426360474` |
| | autonome (`main.py`) | 0.050 | 5.961 % | 12.6 % | 85 | — | `8393d375f5277864dbe2e8ad386bae2b` |

Sharpe calculé par QC, taux sans risque inclus. Après le correctif, l'exposition brute ne dépasse plus 1.003 fois les fonds propres, et aucun appel de marge ne survient (396 avant). La variante rejoint la version autonome en Sharpe et en pire baisse.

Elle passe toutefois près de cinq fois plus d'ordres, parce que le modèle de construction rééquilibre par défaut à chaque séance vers les poids cibles. Avec `InsightWeightingPortfolioConstructionModel(lambda t: None)`, il ne rééquilibre qu'aux changements d'insights : les ordres tombent à 743, les frais baissent d'un facteur 1,7, et le Sharpe ne bouge pas. Une expiration compte aussi comme un changement : un insight mensuel vit 30 séances, l'émission suivante le remplace environ 21 séances plus tard, et son expiration au milieu du mois suivant déclenche encore un petit rééquilibrage de dérive. `main_framework.py` garde le réglage par défaut, celui des mesures fixées d'avance.

Deux écarts de logique avec `main.py` sont voulus. Dans le repli défensif hors risk-off (aucun secteur du top 4 à momentum brut positif), l'alpha arme l'arrêt sur XLP et XLU, alors que `main.py` n'arme rien. Une ligne déjà détenue sans prix d'entrée prend le prix moyen de la position, alors que `main.py` la laisse sans arrêt.

Sur les sept prédictions fixées d'avance, cinq ont tenu. La prédiction sur l'arrêt est fausse telle qu'écrite : il se déclenche 16 fois, et chaque ligne sort à la séance suivante, mais une de ces sorties tombe 4 jours calendaires plus tard (lundi férié), pour 3 annoncés. La prédiction sur l'ablation est fausse sur le nombre d'ordres, 743 pour 610 annoncés : elle oubliait les rééquilibrages d'expiration. Comme pour les demi-séances, ce n'est pas un verdict : la stratégie reste archivée.

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
├── main_framework.py    # Variante Framework (à envoyer comme main.py)
├── alpha_model.py       # SectorMomentumAlpha, alpha de la variante Framework
├── config.json          # Config cloud
├── config_framework.json
├── tests/
│   └── test_alpha_model.py  # Tests CPU de l'alpha (sans Lean)
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
