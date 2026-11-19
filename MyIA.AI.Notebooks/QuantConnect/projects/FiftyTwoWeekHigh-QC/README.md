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

La brique 3 de la ligue mesure une **nouvelle** stratégie contre les références détenues de la ligue (SPY détenu, et le 60/40) avec un test de différence (Diebold-Mariano, correction de Holm). Cette mesure est la **première passe** du candidat : un **seul** backtest, de 2015-01-01 à 2026-11-18, qui compare la stratégie à **SPY détenu** (benchmark du backtest). Le 60/40 et le test de différence ne sont pas encore au programme : ils feront l'objet d'un backtest de référence complémentaire, et le verdict de cette passe se lit donc sur la comparaison à SPY seul.

Propriétés du code :

- le benchmark `SPY` est porté par `set_benchmark`, la référence de cette passe ;
- la décision se prend une fois par mois, au changement de mois ;
- la fenêtre couvre un cycle complet (bull 2015-2018, crash 2020, bear 2022) — elle n'est pas découpée en in/out-of-sample, ce que cette passe ne permet pas de trancher.

Le backtest `5646b9f074efd97387fc8d4a76de5cf8` (QC Cloud, projet 39684781) rend :

| | Sharpe QC | CAGR | Pire baisse |
|---|---|---|---|
| stratégie | 0.791 | 18.613 % | 25.0 % |
| SPY détenu (benchmark) | 0.515 | 13.014 % | 33.7 % |

**Verdict de la passe** : **BEATS** — la stratégie domine SPY détenu sur les trois métriques de la passe (Sharpe 0.791 vs 0.515, CAGR 18.613 % vs 13.014 %, pire baisse 25.0 % vs 33.7 %). Le 60/40 et le test de différence (Diebold-Mariano / Holm) restent au backtest de référence complémentaire.

## Files

- main.py — la règle de sélection mensuelle (univers grossier/fin, classement par proximité au plus-haut 52 semaines, top 10 à poids égal)

## References

- O'Neil, W. — méthode CAN SLIM, critère « G » (signal « glory »)
- EPIC #19821 (ligue de stratégies), brique 3 — mesure d'une nouvelle stratégie contre les références détenues
