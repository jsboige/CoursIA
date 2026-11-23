# FiftyTwoWeekHigh-QC

La stratégie « 52-week high » (momentum par proximité du plus-haut 52 semaines, le signal « glory » de la méthode CAN SLIM de William O'Neil) mesurée contre SPY détenu, à la brique 3 de la ligue de stratégies (#19821).

## Description

Le signal « 52-week high » retient les actions proches de leur plus-haut des 52 dernières semaines. C'est un signal de **momentum en coupe** : une action qui évolue vers son plus-haut est lue comme forte, et la méthode CAN SLIM de William O'Neil en fait son critère « G » — un titre est « glorious » lorsqu'il évolue vers un nouveau plus-haut sur volume. La version mesurée ici en est la forme la plus simple : au lieu d'exiger un nouveau plus-haut exact, on **classe** les actions par leur **proximité** à leur plus-haut 52 semaines (dernière clôture / plus-haut 52 semaines) et on détient les plus proches.

**Le code.**

- **Univers** : une liste fixe de 30 actions américaines large-cap, toutes liquides sur toute la fenêtre 2015-2026. Le service d'univers fondamental grossier/fin n'étant pas disponible dans l'image Lean de QC Cloud, un univers fixe de grandes valeurs liquides en est la forme robuste et équivalente.
- **Sélection mensuelle** (au changement de mois) : classement de l'univers par proximité au plus-haut 52 semaines ; on détient les **10** plus proches, à poids égal, et on liquide les titres sortis du top 10.

Le projet est un **candidat créé pour la mesure** : il n'a pas de code antérieur à reproduire, et le backtest qui suit est la sienne.

## How to Run

Projet QC Cloud : un `main.py` sans dépendance hors de Lean. Les constantes fixent la règle :

- `N` : nombre de lignes tenues (10) ;
- `UNIVERSE` : la liste fixe des 30 large-caps américaines liquides sur toute la fenêtre.

## Verdict contre SPY détenu (#19821, brique 3)

La brique 3 de la ligue mesure une **nouvelle** stratégie contre les références détenues de la ligue (SPY détenu, et le 60/40) avec un test de différence (Diebold-Mariano, correction de Holm). Cette passe est la **première** du candidat : un backtest de 2015-01-01 à 2026-11-18 comparé à **SPY détenu** (benchmark du backtest). Le 60/40 et le test de différence (DM/Holm) font l'objet d'un backtest de référence complémentaire.

Propriétés du code :

- le benchmark `SPY` est porté par `set_benchmark`, la référence de cette passe ;
- la décision se prend une fois par mois, au changement de mois ;
- **règle déterministe** : univers fixe (30 large-caps), classement par proximité au plus-haut 52 semaines, top 10 à poids égal, rééquilibrage au changement de mois — aucun aléa (pas de Monte-Carlo, pas de graine) ; un re-run reproduit la trajectoire à l'identique ;
- **coûts de transaction** : aucun modèle de courtage custom n'est posé, le modèle par défaut de Lean (commission par action + slippage) s'applique à chaque `liquidate()`/`set_holdings()` — les frais sont donc dans les chiffres (−$3 097 sur la fenêtre).

Le backtest `0f2141c98fd1982fe144ea792f016279` (QC Cloud, projet 39684781) rend, sur la fenêtre complète :

| | Sharpe QC | CAGR | Pire baisse |
|---|---|---|---|
| stratégie | 0.628 | 14.884 % | 25.8 % |
| SPY détenu (benchmark) | 0.515 | 13.014 % | 33.7 % |

**Fenêtre out-of-sample 2020-2026** — dérivée des courbes du même backtest (la règle étant sans mémoire de mois en mois, la sous-fenêtre est une mesure OOS fidèle) :

| | CAGR | Pire baisse |
|---|---|---|
| stratégie | 14.73 % | 25.8 % |
| SPY détenu | 14.42 % | 31.9 % |

L'avantage se **resserre** en OOS : l'écart CAGR passe de +1.87 pp (fenêtre complète) à **+0.31 pp**, le drawdown reste nettement plus bas (25.8 % vs 31.9 %), et le Sharpe dérivé est en parité. La prime momentum sur SPY est **réelle sur le cycle complet** mais **mince dans le régime 2020-2026** — où SPY est lui-même très chargé des mêmes mega-caps que la stratégie retient.

**Biais large-cap (limitation connue)** : l'univers est une liste fixe de 30 mega-caps **survivantes** (AAPL, MSFT, NVDA, …). Le « BEATS » est donc en partie un artefact de la sélection d'univers survivant — ce n'est pas la mesure d'un univers fondamental ex-ante. C'est la forme robuste du candidat tant que le service d'univers grossier/fin de l'image Lean n'est pas dispo.

**Verdict de la passe** : **BEATS** sur la fenêtre complète 2015-2026 (Sharpe 0.628 vs 0.515, CAGR 14.884 % vs 13.014 %, pire baisse 25.8 % vs 33.7 %, frais de transaction inclus), **l'avantage étant documenté comme plus mince en OOS 2020-2026** et le biais d'univers large-cap survivant déclaré. Le 60/40 et le test de différence (DM/Holm) restent au backtest de référence complémentaire.

## Files

- main.py — la règle de sélection mensuelle (univers fixe de 30 mega-caps, classement par proximité au plus-haut 52 semaines, top 10 à poids égal)

## References

- O'Neil, W. — méthode CAN SLIM, critère « G » (signal « glory »)
- EPIC #19821 (ligue de stratégies), brique 3 — mesure d'une nouvelle stratégie contre les références détenues
