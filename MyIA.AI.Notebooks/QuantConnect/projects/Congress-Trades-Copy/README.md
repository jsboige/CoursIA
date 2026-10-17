# Congress-Trades-Copy

Port CoursIA du research note QuantConnect **« Copying Congress Trades »** (Derek Melchin, [research 17886](https://www.quantconnect.com/research/17886/copying-congress-trades/)) — grain #16372, Epic #11698 (qc-research). Consolidé par le grain **#20465** : port de la seconde construction du même dataset — **« Following the Stock Purchases of Senators »** ([research 21469](https://www.quantconnect.com/research/21469/following-the-stock-purchases-of-senators/)), verdict CONSOLIDATION (l'article est PARTIELLEMENT redondant : même dataset, même signal BUY, construction distincte — cf tableau ci-dessous).

## Mécanisme — deux constructions paramétrées (`rebalance`)

- **Univers commun** : actions récemment achetées par des membres du Congrès US — dataset [Quiver Quantitative US Congress Trading](https://www.quantconnect.com/datasets/quiver-quantitative-congress-trading) (payant ; disclosures SEC via STOCK Act, publication ≤ 45 jours après la transaction). Seules les transactions **BUY** déclenchent l'inclusion (pas de signal SELL symétrique dans les deux articles).
- **`rebalance=weekly`** (défaut, 17886) : rebalancement hebdomadaire — premier jour ouvré, 30 min après l'open SPY ; pondération **inverse-volatilité** (vol quotidienne trailing ~6 mois), levier cible **1,5×**, cap **10 % par actif** anti-concentration.
- **`rebalance=window`** (21469) : **Senate seulement** (`house=senate`), fenêtre de **30 jours sur la date de rapport** (`holding-days`), actions communes US uniquement — ni ADR ni REIT (univers fondamental), **equal-weight 1/n**, rebalancement quotidien 8 h ET mais **seulement à l'entrée/sortie de la fenêtre**, warm-up de la fenêtre. Exécution : `set_holdings(targets, True)` — liquidation implicite des sorties d'univers.

| Axe | 17886 (port initial) | 21469 (mode `window`) |
| --- | --- | --- |
| Chambre | Congrès entier | Senate seulement |
| Fenêtre | rebalancement calendaire hebdo | 30 j sur date de **rapport** |
| Pondération | inverse-vol + levier 1,5× + cap | equal-weight |
| Annonce | Sharpe 0,934 vs SPY 0,7 | Sharpe 1,054 vs SPY 0,363 (2021-09→2026-09), sweep 20-40 j : 21/21 > benchmark |

Ancrage académique du 21469 (vérifié sur abstract SSRN, sans variance avec l'article) : **Lazzaretto (2024), « Mind the Trade: Senators' Disclosure and Stock Returns », SSRN 4816497** (achats sénateurs ~1 pp/mois d'erreur anormale post-disclosure, >9 bps/jour sur les trades spéculatifs) ; **Fishman & Hagerty (1995), RFS 8(3) 637-676** (la divulgation déplace les prix même pour un insider non informé). Contre-point de littérature : « Capitol Losses » (JOP) — performance congressionnelle globale médiocre.

Ce que les articles divulguent : les Sharpe ci-dessus. Ce qu'ils ne divulguent pas — et que ce port mesure : drawdown, turnover, sensibilité, jambe OOS distincte, et pour le 21469 la **falaise 22→23 j** du sweep (0,988→1,260) que l'auteur attribue lui-même à quelques trades d'échantillon — mesure falsificatrice locale (reproduire ou contredire).

## Fricition corrigée

Les commentaires de l'article rapportent `self._universe.selected` retournant `None` (L. Raducu, en live). Le port cache la sélection dans le sélecteur lui-même (`self._selected`), jamais lu depuis `universe.selected`.

## Paramètres (backtests)

| Paramètre | Défaut | Rôle |
|---|---|---|
| `rebalance` | `weekly` | construction : `weekly` (17886) ou `window` (21469) |
| `house` | `all` | chambre : `all` / `senate` / `house` (filtre des deux constructions) |
| `holding-days` | `30` | fenêtre sur date de rapport, mode `window` (sweep 20-40 prévu) |
| `leverage` | `1.5` | multiplicateur de buying power (mode `weekly`) |
| `cap` | `0.10` | poids max par actif (mode `weekly`) |
| `vol-window` | `180` | fenêtre de vol quotidienne (jours, mode `weekly`) |
| `start` / `end` | `2019` / `2024` | années de début/fin (jambe OOS : `2025`/`2026`) |

## Résultats

**Aucun résultat publié : le jeu de données n'est pas licencié.** Le port lit le jeu de données QuantConnect « Quiver US Congress Trading », vendu sous licence. Sans elle, la stratégie ne passe aucun ordre : aucun Sharpe, CAGR ou drawdown ne peut être produit, et aucun résultat n'est reproductible. La baseline 2019-2024, la jambe OOS et le balayage de sensibilité restent donc sans mesure, comme les axes non divulgués listés plus haut. Décision mainteneur du 16/10/2026 : la licence n'est pas acquise.

Mesure de référence, faite le 15/10/2026 dans les deux espaces QC où le dépôt lance ses backtests ([détail sur l'issue #16372](https://github.com/jsboige/CoursIA/issues/16372#issuecomment-6196837722)) :

- la souscription par titre au flux `QuiverCongress` est refusée : « The current user does not have a subscription ... Please license the dataset » ;
- l'univers `QuiverQuantCongressUniverse` ne lève aucune erreur, mais son sélecteur n'est jamais appelé (sonde avec SPY souscrit, 62 séances) ;
- `main.py` tourne sur 2023 sans passer un seul ordre.

Le second point est le piège : un univers non licencié reste vide en silence. Si la licence est acquise plus tard, la vérifier d'abord par une souscription par titre ou par le compteur d'appels du sélecteur, avant toute série de backtests.
