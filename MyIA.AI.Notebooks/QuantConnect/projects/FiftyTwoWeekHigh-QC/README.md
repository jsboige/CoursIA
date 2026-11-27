# FiftyTwoWeekHigh-QC

La stratégie « 52-week high » (momentum par proximité du plus-haut 52 semaines, le signal « glory » de la méthode CAN SLIM de William O'Neil), mesurée à la brique 3 de la ligue de stratégies (#19821) contre deux références détenues (SPY, et 60/40) et contre son propre univers à poids égal.

## Description

Le signal « 52-week high » retient les actions proches de leur plus-haut des 52 dernières semaines. C'est un signal de **momentum en coupe** : une action qui évolue vers son plus-haut est lue comme forte, et la méthode CAN SLIM de William O'Neil en fait son critère « G » — un titre est « glorious » lorsqu'il évolue vers un nouveau plus-haut sur volume. La version mesurée ici en est la forme la plus simple : au lieu d'exiger un nouveau plus-haut exact, on **classe** les actions par leur **proximité** à leur plus-haut 52 semaines (dernière clôture / plus-haut 52 semaines) et on détient les plus proches.

**Le code.**

- **Univers** : une liste fixe de 30 actions américaines large-cap, toutes liquides sur toute la fenêtre 2015-2026. Le service d'univers fondamental grossier/fin n'étant pas disponible dans l'image Lean de QC Cloud, un univers fixe de grandes valeurs liquides en est la forme robuste et équivalente.
- **Sélection mensuelle** (au changement de mois) : classement de l'univers par proximité au plus-haut 52 semaines ; on détient les **10** plus proches, à poids égal, et on liquide les titres sortis du top 10.

Le projet est un **candidat créé pour la mesure** : il n'a pas de code antérieur à reproduire, et le backtest qui suit est la sienne.

## How to Run

Projet QC Cloud : un `main.py` sans dépendance hors de Lean. Les constantes fixent la règle :

- `N` : nombre de lignes tenues (10) ;
- `UNIVERSE` : la liste fixe des 30 large-caps américaines liquides sur toute la fenêtre ;
- `mode` (paramètre de backtest, défaut `strategy`) : `strategy` applique la règle du projet ; `spy`, `6040` et `ew30` détiennent une référence sur la même histoire, rééquilibrée au même rééquilibrage mensuel. `ew30` est le diagnostic (l'univers à poids égal, sans sélection).

Chaque mode trace une valeur de portefeuille par séance dans le chart `shadow` (`e0`..`e4`) avant 2025-01-01 et `shadow2` (`e0`..`e4`) ensuite, chaque compteur repartant de `e0` au début de sa fenêtre (contrat de rejeu en ombre, #18923). C'est la trace que consomment `Paradox46Benchmarks/significance.py` et la matrice de corrélation de la ligue.

## Verdict contre SPY détenu (#19821, brique 3)

La brique 3 de la ligue mesure une **nouvelle** stratégie contre les références détenues de la ligue (SPY détenu, et le 60/40) avec un test de différence (Diebold-Mariano, correction de Holm). Cette passe est la **première** du candidat : un backtest de 2015-01-01 à 2026-11-18 comparé à **SPY détenu** (benchmark du backtest). Le 60/40 et le test de différence font l'objet de la mesure de ligue plus bas.

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

**Lecture de la passe** : avantage ponctuel sur SPY (Sharpe 0.628 vs 0.515, CAGR 14.884 % vs 13.014 %, pire baisse 25.8 % vs 33.7 %, frais inclus), **plus mince en OOS 2020-2026**, et biais d'univers large-cap survivant déclaré. Cette passe ne portait qu'une référence (SPY, par le benchmark) et aucun test de différence : elle ne conclut pas au sens de la brique 3.

## Mesure de ligue (brique 3, #19821) — références détenues et tests de différence

Passe du 2026-11-25, projet 39684781, protocole pré-enregistré dans #28535. Une passe continue par mode sur 2015-01-01 → 2026-11-18 : le témoin (`main.py` d'avant instrumentation), `strategy`, `spy`, `6040` et `ew30`.

**Contrôle d'innocuité** : en mode `strategy`, le code instrumenté reproduit le témoin mesuré le même jour, champ par champ — Sharpe 0.620, CAGR 14.721 %, pire baisse 25.800 %, profit net 411.840 %, PSR 4.191 %, profit absolu $375 937.09, frais −$3 099.31, équité finale $511 840.13, `totalOrders` 1611, `tradeableDates` 2988. La limite écrite avant la mesure : le retour du MCP de ce siège n'expose pas le journal d'ordres, le contrôle porte donc sur ces champs.

Passe du 2026-11-20 (publiée ci-dessus) contre passe du 2026-11-25 : Sharpe 0.628 et 1609 ordres contre 0.620 et 1611. C'est la raison du témoin mesuré le même jour.

| Mode | Sharpe QC | CAGR | Pire baisse | Profit net | Ordres |
|---|---|---|---|---|---|
| `strategy` | 0.620 | 14.721 % | 25.800 % | 411.840 % | 1611 |
| `spy` | 0.521 | 13.124 % | 33.700 % | 333.263 % | 2 |
| `6040` | 0.425 | 8.611 % | 21.600 % | 167.013 % | 240 |
| `ew30` | 0.785 | 18.060 % | 28.500 % | 619.867 % | 1454 |

`spy` ne passe que deux ordres : un portefeuille mono-actif à poids 1 n'a rien à rééquilibrer, sa part reste 100 % quelle que soit la dérive. `6040` et `ew30` rééquilibrent réellement.

**Tests de différence** (`Paradox46Benchmarks/significance.py`, taux sans risque nul, 2 000 tirages, blocs de 10, graine 0 ; le Sharpe des traces n'est donc pas celui de QC, qui retire le taux — les deux membres d'une comparaison sont calculés de la même façon) :

| Fenêtre | Séances | Sharpe stratégie | Sharpe `spy` | Écart | p Ledoit-Wolf | p moyenne (Newey-West) |
|---|---|---|---|---|---|---|
| F1 2015-01-02 → 2024-12-30 | 2515 | 0.9250 | 0.8047 | +0.1203 | 0.514 | 0.653 |
| F2 2025-01-02 → 2026-11-18 | 472 | 1.0884 | 0.8582 | +0.2302 | 0.746 | 0.929 |

| Fenêtre | Sharpe `6040` | Écart | p Ledoit-Wolf | p moyenne |
|---|---|---|---|---|
| F1 | 0.8292 | +0.0957 | 0.642 | 0.028 |
| F2 | 0.9333 | +0.1551 | 0.825 | 0.530 |

La plus petite des six p-values brutes de F1 (0,028, écart de moyenne contre `6040`) devient 0,169 après correction de Holm ; toutes les autres valent 1,000. En F2, les six valent 1,000 après Holm.

**Verdict, par fenêtre** : **INCONCLUSIVE** dans les deux. L'écart de Sharpe est positif contre les deux références, mais aucune p de Holm n'atteint 0,05 — l'avantage ponctuel du tableau de la passe initiale n'est pas distinguable du bruit à cette taille d'échantillon.

**Diagnostic `ew30`** — le même test contre l'univers détenu à poids égal, sans sélection :

| Fenêtre | Sharpe `ew30` | Écart stratégie − `ew30` | p Ledoit-Wolf | p moyenne |
|---|---|---|---|---|
| F1 | 1.1181 | −0.1931 | 0.210 | 0.225 |
| F2 | 1.2686 | −0.1802 | 0.756 | 0.821 |

Le point estimé est **négatif dans les deux fenêtres** : la sélection des dix plus proches de leur plus-haut ne montre aucun ajout sur la détention de l'univers, et le CAGR de `ew30` (18.060 %) dépasse celui de la stratégie (14.721 %). Non significatif non plus, mais convergent avec le biais d'univers déclaré plus haut : ce que la stratégie capture sur SPY vient pour l'essentiel de son panier de mega-caps, pas de son classement.

Traces et tests : `G:\Mon Drive\MyIA\IA\QC-traces\28535-fiftytwo-week-high-held-references\` (`control`, `strategy`, `spy`, `6040`, `ew30` ; `significance-f1.json`, `significance-f2.json`, `diagnostic-ew30-f1.json`, `diagnostic-ew30-f2.json`, `innocuite.txt`).

## Files

- main.py — la règle de sélection mensuelle (univers fixe de 30 mega-caps, classement par proximité au plus-haut 52 semaines, top 10 à poids égal)

## References

- O'Neil, W. — méthode CAN SLIM, critère « G » (signal « glory »)
- EPIC #19821 (ligue de stratégies), brique 3 — mesure d'une nouvelle stratégie contre les références détenues
