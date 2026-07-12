# ETF-Pairs Strategy

**Statut** : ❌ BROKEN — contre-exemple à visée pédagogique.

## Performance

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | **-0.706** |
| CAGR | -4.7 % |
| Max Drawdown | 35.0 % |
| Période | 2020-2026 |

## Pourquoi cette stratégie a échoué

### Cause racine : le même problème fondamental que PairsTrading

Cette stratégie tentait le pairs trading avec **des ETF au lieu d'actions individuelles**, en faisant l'hypothèse que :
- les ETF seraient plus stables que les actions individuelles
- les ETF sectoriels pourraient présenter une meilleure cointégration
- la diversification interne des ETF réduirait le bruit

**Résultat** : la même rupture de cointégration, mais avec une performance **encore pire** :
- les paires d'ETF présentaient encore MOINS de cointégration que les paires d'actions
- une volatilité plus élevée a conduit à des pertes plus importantes
- le ratio de couverture était encore plus instable

### Ce qui rend cette stratégie pire que PairsTrading

| Facteur | PairsTrading | ETF-Pairs |
|---------|--------------|-----------|
| Sharpe | -0.361 | **-0.706** |
| CAGR | 0.9 % | **-4.7 %** (négatif !) |
| Max DD | 15.1 % | **35.0 %** |

### Pourquoi les ETF ont échoué ici

1. **La composition des ETF change** : les ETF rééquilibrent leurs positions, ce qui brise toute cointégration
2. **Corrélation sectorielle ≠ cointégration** : les secteurs peuvent bouger ensemble sans avoir de spreads mean-reverting
3. **Effets de décalage** : le rééquilibrage des ETF crée des déconnexions de prix artificielles
4. **Historique plus court** : la plupart des ETF sectoriels ont moins d'historique pour un test de cointégration robuste

### Leçons retenues

1. **Diversification ETF ≠ stabilité de cointégration** : le fait qu'un ETF détienne plusieurs actions ne signifie pas que la relation de prix est stable
2. **Ne pas s'entêter sur des hypothèses rompues** : si les paires d'actions ne fonctionnent pas, les paires d'ETF ne répareront pas magiquement le problème fondamental
3. **Un CAGR négatif est un signal d'alarme** : perdre de l'argent de façon consistante signifie que la stratégie n'a aucun avantage
4. **S'arrêter après 2-3 itérations** : nous avons testé plusieurs combinaisons de paires d'ETF — toutes ont échoué

## Quand le pairs trading peut fonctionner

Voir `PairsTrading/README.md` pour le contexte. Pour les ETF spécifiquement :
- **ETF de matières premières** (GLD/GSLV, USO/UCO) où la cointégration est structurelle
- **Paires d'ETF leveragés** où la relation de décroissance est prévisible
- **ETF obligataires** où les relations de courbe des taux créent une cointégration

**Pour les ETF sectoriels d'actions (2020-2026)** : cette approche a échoué de façon catastrophique.

## Valeur pédagogique

Cette stratégie sert de **double contre-exemple** :
- ❌ Même leçon que PairsTrading : corrélation ≠ cointégration
- ❌ Leçon supplémentaire : la « stabilité » des ETF est un mythe pour la cointégration
- ❌ Quand pivoter : si l'hypothèse fondamentale échoue, changer l'instrument (actions → ETF) n'aide pas

## Références

- **PairsTrading** : voir la version basée sur des actions pour comparaison
- **QuantBook** : `quantbook.ipynb` — analyse de cointégration ETF

---

**Note** : cette stratégie n'est PAS recommandée pour le trading en réel. Elle démontre que le choix de l'instrument ne peut pas corriger une hypothèse de stratégie fondamentalement défectueuse.
