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

(À remplir par les backtests — baseline 2019-2024, OOS 2025-2026H1, sweep de sensibilité. Verdicts honnêtes, cf `research.ipynb`.)
