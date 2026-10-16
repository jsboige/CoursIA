# Congress-Trades-Copy

Port CoursIA du research note QuantConnect **« Copying Congress Trades »** (Derek Melchin, [research 17886](https://www.quantconnect.com/research/17886/copying-congress-trades/)) — grain #16372, Epic #11698 (qc-research).

## Mécanisme

- **Univers** : actions récemment achetées par des membres du Congrès US — dataset [Quiver Quantitative US Congress Trading](https://www.quantconnect.com/datasets/quiver-quantitative-congress-trading) (payant ; disclosures SEC via STOCK Act, publication ≤ 45 jours après la transaction). Seules les transactions **BUY** déclenchent l'inclusion (pas de signal SELL symétrique dans l'article).
- **Rebalancement** : hebdomadaire — premier jour ouvré, 30 min après l'open SPY.
- **Construction** : pondération **inverse-volatilité** (vol quotidienne trailing ~6 mois), levier cible **1,5×**, cap **10 % par actif** anti-concentration.
- **Exécution** : `set_holdings(targets, True)` — liquidation implicite des sorties d'univers.

Ce que l'article divulgue : **Sharpe algo 0,934 vs SPY 0,7**. Ce qu'il ne divulgue pas — et que ce port mesure : période, drawdown, turnover, sensibilité (levier, cap, fenêtre de volatilité), jambe OOS distincte.

## Fricition corrigée

Les commentaires de l'article rapportent `self._universe.selected` retournant `None` (L. Raducu, en live). Le port cache la sélection dans le sélecteur lui-même (`self._selected`), jamais lu depuis `universe.selected`.

## Paramètres (backtests)

| Paramètre | Défaut | Rôle |
|---|---|---|
| `leverage` | `1.5` | multiplicateur de buying power |
| `cap` | `0.10` | poids max par actif |
| `vol-window` | `180` | fenêtre de vol quotidienne (jours) |
| `start` / `end` | `2019` / `2024` | années de début/fin (jambe OOS : `2025`/`2026`) |

## Résultats

**Aucun résultat publié : le jeu de données n'est pas licencié.** Le port lit le jeu de données QuantConnect « Quiver US Congress Trading », vendu sous licence. Sans elle, la stratégie ne passe aucun ordre : aucun Sharpe, CAGR ou drawdown ne peut être produit, et aucun résultat n'est reproductible. La baseline 2019-2024, la jambe OOS et le balayage de sensibilité restent donc sans mesure, comme les axes non divulgués listés plus haut. Décision mainteneur du 16/10/2026 : la licence n'est pas acquise.

Mesure de référence, faite le 15/10/2026 dans les deux espaces QC où le dépôt lance ses backtests ([détail sur l'issue #16372](https://github.com/jsboige/CoursIA/issues/16372#issuecomment-6196837722)) :

- la souscription par titre au flux `QuiverCongress` est refusée : « The current user does not have a subscription ... Please license the dataset » ;
- l'univers `QuiverQuantCongressUniverse` ne lève aucune erreur, mais son sélecteur n'est jamais appelé (sonde avec SPY souscrit, 62 séances) ;
- `main.py` tourne sur 2023 sans passer un seul ordre.

Le second point est le piège : un univers non licencié reste vide en silence. Si la licence est acquise plus tard, la vérifier d'abord par une souscription par titre ou par le compteur d'appels du sélecteur, avant toute série de backtests.
