# PairsTrading Strategy

**Statut** : BROKEN — contre-exemple à visée pédagogique

## Performance

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | **-0.361** |
| CAGR | 0.9 % |
| Max Drawdown | 15.1 % |
| Période | 2010-2026 |

## Pourquoi cette stratégie a échoué

### Cause racine : rupture structurelle de cointégration

L'hypothèse fondamentale du pairs trading est que les deux titres sont **cointégrés** — c'est-à-dire que leur spread de prix est stationnaire et mean-reverting. Cette stratégie suppose :

1. Que le ratio de couverture (hedge ratio) est stable dans le temps
2. Que le spread reviendra à sa moyenne
3. Qu'il existe des opportunités d'arbitrage statistique

**En réalité (2010-2026)** :

- Les paires d'actions US n'ont montré **aucune relation de cointégration stable**
- Le ratio de couverture (estimé par OLS) était instable
- Le spread a divergé de façon permanente au lieu de revenir
- Résultat : pertes constantes sans aucun avantage (edge)

### Ce qui a été testé

| Itération | Modification | Résultat |
|-----------|--------------|----------|
| v1.0 | Hedge ratio OLS basique + z-score | Sharpe -0.361 |
| v2.0 | Paires multiples (5 paires) + test de cointégration | Sharpe -0.420 |
| v3.0 | Combinaisons de paires différentes | Toutes négatives |

### Leçons retenues

1. **La cointégration est rare dans les actions US** : la plupart des actions qui paraissent corrélées ne sont PAS cointégrées
2. **Instabilité du hedge ratio** : même si des paires testent positif à la cointégration in-sample, la relation se dégrade souvent out-of-sample
3. **Coûts de transaction** : le spread trading nécessite des rééquilibrages fréquents, ce qui érode tout avantage théorique
4. **Changements de régime** : les mutations de structure de marché (2010-2026 inclut bull, bear, COVID, inflation) brisent la cointégration

## Quand le pairs trading PEUT fonctionner

Cette classe de stratégies peut fonctionner dans :

- **Des classes d'actifs différentes** : matières premières, futures, FX où la cointégration est plus fréquente
- **Des régimes de marché spécifiques** : certains environnements de volatilité
- **Des fenêtres temporelles plus courtes** : une cointégration in-sample peut exister sur des périodes limitées

**Pour les actions US (2010-2026)** : cette approche a échoué de façon constante.

## Valeur pédagogique

Cette stratégie est conservée comme **contre-exemple** pour illustrer :

- Le danger de supposer que corrélation = cointégration
- Pourquoi le backtesting doit couvrir la période complète (2010-2026, pas seulement 2015-2020)
- L'importance de la conscience du régime dans la conception de stratégies
- Quand abandonner une idée de stratégie (après 2-3 itérations ratées)

## Références

- **QuantBook** : `quantbook.ipynb` — notebook de recherche avec tests de cointégration
- **Research** : `research.ipynb` — analyse exploratoire

---

**Note** : cette stratégie n'est PAS recommandée pour le trading en live. Elle sert d'avertissement sur l'importance de valider les hypothèses fondamentales (cointégration) avant de déployer du capital.
