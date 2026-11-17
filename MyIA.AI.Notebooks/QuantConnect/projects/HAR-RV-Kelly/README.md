# HAR-RV-Kelly

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** Voir `config.json` (local-id : 230839018)

## Description

Modèle HAR-RV (Heterogeneous Autoregressive Realized Variance, Corsi 2009) pour prévoir la variance réalisée à 5 jours sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Utilise le critère de Kelly à fraction 1/4 pour le dimensionnement des positions basé sur la prévision HAR. Inclut la direction du momentum à 5 jours. Ré-ajustement du modèle par OLS tous les 22 jours sur une fenêtre glissante de 500 jours. Rebalancement hebdomadaire.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm HAR-RV-Kelly/main.py
```

### QC Cloud
Ouvrir le projet cloud (local-id : 230839018), compiler et lancer un backtest.

## Métriques du backtest

| Méthode | Rebalancement | Paramètres clés |
|---------|---------------|-----------------|
| HAR-RV + Critère de Kelly | Hebdomadaire | Fraction Kelly 1/4, prévision 5 jours, ré-ajustement OLS tous les 22 jours, fenêtre 500 jours |

## Noyau de risque déterministe (#24698)

Le paramètre `kernel` ajoute à la stratégie le noyau de risque déterministe de Steward (arXiv 2610.30557). Le portage de référence de ce noyau dans le dépôt est le projet `DeterministicRiskKernel-QC`. Avec la valeur par défaut, `kernel=off`, le code de la stratégie est inchangé.

| `kernel` | Plafond d'exposition à 90 % | Stop à 2 ATR(14) | Coupe-circuit à −3 % |
|---|---|---|---|
| `off` (défaut) | non | non | non |
| `cap90` | oui | non | non |
| `kernel_nocb` | oui | oui | non |
| `kernel` | oui | oui | oui |

Sur six lignes rééquilibrées chaque lundi, le noyau fonctionne ainsi :

- **le plafond** ramène la somme des poids à 0,90 quand elle la dépasse. La normalisation d'origine, qui ramène cette somme à 1, est appliquée avant lui. Le plafond porte sur l'ordre : entre deux lundis, la hausse des prix peut faire monter l'exposition mesurée jusqu'à 0,917 ;
- **le stop** est un ordre `StopMarket` placé à 2 ATR(14) sous le prix du moment de l'ordre, sur chaque ligne achetée. Il est reposé à chaque rééquilibrage. Une ligne stoppée reste à plat jusqu'au lundi suivant ; les autres lignes restent en place ;
- **le coupe-circuit** lit la clôture. Si la valeur du portefeuille perd 3 % ou plus sur la séance, toutes les lignes sont vendues à l'ouverture suivante (`MarketOnOpen`). La séance suivante se passe à plat, puis les poids du lundi en cours sont repris ;
- **la règle de dimensionnement de Steward** (0,5 % du capital au stop) n'est pas implémentée. La taille d'une ligne reste celle du Kelly, bornée à 0,30.

Le défaut d'échelle relevé dans #26329 n'est pas corrigé ici : dans le code, la variance annuelle est sous-estimée d'un facteur 5. Le noyau est mesuré sur le code tel qu'il est.

### Mesures

Cinq backtests du 2026-11-13, dans l'espace de backtest du cours, tous sur la fenêtre codée : 2015-01-01 → 2025-01-01, soit 2516 dates négociables. Le run `bare` exécute la `main.py` de `0ddc1e46fd`, avant l'ajout du noyau (projet QC 39328653, compile `93edc4052254b0197f7483fb5a12f230-6725a12c2c2991872db58f69a7accbee`). Les quatre autres runs exécutent le code de cette PR (projet QC 39328660, compile `08a275404053555c3da676b2590e98d2-9889056cf07ad03339281937e1ce3e09`). Les deux compiles sont `BuildSuccess`. Les deux codes ont été envoyés puis relus, avec contrôle d'empreinte (sha256 `c80afa6189cd…` et `706eef6cefa3…`).

| `kernel` | Backtest | Ordres | Sharpe (QC) | CAGR | Drawdown max | Profit net | PSR | Stops | Coupures | Exposition max | Séances à plat |
|---|---|---|---|---|---|---|---|---|---|---|---|
| code nu | `995560424f5e0f6e18ff84a126d03bb3` | 1358 | 0,065 | 3,470 % | 15,7 % | 40,681 % | 0,018 % | — | — | — | — |
| `off` | `c700ad0175a8c8012d5865c2cb7f7379` | 1358 | 0,065 | 3,470 % | 15,7 % | 40,681 % | 0,018 % | 0 | 0 | 1,0191 | 523 / 2516 (21 %) |
| `cap90` | `be3cbb6e8e7d06918de3264259b2f049` | 1355 | 0,060 | 3,430 % | 15,5 % | 40,147 % | 0,016 % | 0 | 0 | 0,9173 | 523 / 2516 (21 %) |
| `kernel_nocb` | `021617f247331e060dcf06731c3892c2` | 2163 | −0,025 | 2,781 % | 12,6 % | 31,584 % | 0,004 % | 222 | 0 | 0,9174 | 629 / 2516 (25 %) |
| `kernel` | `5713297bb5e872b36e7b7b80d4a9090c` | 2164 | −0,022 | 2,809 % | 12,4 % | 31,945 % | 0,005 % | 222 | 2 | 0,9174 | 631 / 2516 (25 %) |

Les ordres comptent aussi les stops annulés : chaque rééquilibrage annule le stop d'une ligne avant de le reposer. Sur `kernel_nocb`, on compte 1158 ordres de rééquilibrage exécutés, 222 stops exécutés, 782 stops annulés et un stop encore actif en fin de fenêtre. Les deux coupures de `kernel` partent des clôtures du 2020-06-11 et du 2022-03-09. Les 222 stops se répartissent entre 16 et 36 par an. Le premier ordre date du 2016-01-11. Avant cette date, une ligne n'est pas négociée tant qu'elle n'a pas 500 variances réalisées ; cette année à plat entre dans les séances à plat de tous les modes.

**Témoins.** Le run `off` rend les mêmes 1358 ordres que le code nu (date, titre, quantité et type identiques, un par un) et les mêmes statistiques : le code du noyau ne change rien quand il est désactivé. Ces deux runs ne reproduisent pas la ligne publiée dans `docs/qc/qc-strategies-status.md`, qui donne un Sharpe de 0,146, un CAGR de 4,23 % et un drawdown de 12,8 % sur la même fenêtre. Le code n'a pas changé ; la cause de l'écart n'est pas établie.

**Test apparié.** `Paradox46Benchmarks/significance.py` s'applique aux rendements journaliers des traces `shadow` (2516 séances, taux sans risque nul). Il calcule l'écart de Sharpe Ledoit-Wolf, l'écart de moyenne Newey-West et un bootstrap stationnaire (2000 tirages, blocs de 10, graine 0), puis corrige les p-valeurs par Holm. Le Sharpe de QC déduit un taux sans risque ; celui des traces, calculé à taux nul, est d'un autre ordre.

| Mode contre `off` | Sharpe du mode | Sharpe `off` | Écart | Corrélation | p Ledoit-Wolf | IC 95 % bootstrap | p Newey-West | p de Holm |
|---|---|---|---|---|---|---|---|---|
| `cap90` | 0,506 | 0,491 | +0,014 | 0,999 | 0,353 | [−0,016 ; 0,043] | 0,650 | 1,0 |
| `kernel_nocb` | 0,471 | 0,491 | −0,020 | 0,906 | 0,880 | [−0,280 ; 0,239] | 0,432 | 1,0 |
| `kernel` | 0,476 | 0,491 | −0,016 | 0,906 | 0,906 | [−0,279 ; 0,244] | 0,450 | 1,0 |

### Lecture

- **Le plafond mord souvent, mais pèse peu.** Sous `off`, l'exposition brute dépasse 0,95 après 29 % des 395 rééquilibrages qui passent des ordres, et se situe entre 0,85 et 0,95 après 16 % d'entre eux. Cette exposition est relevée au prix d'exécution et rapportée à la valeur de clôture du jour. Ramener ces semaines à 0,90 ne coûte que 0,04 point de CAGR et ne gagne que 0,2 point de drawdown. L'écart de Sharpe n'est pas significatif.
- **Le stop échange du rendement contre du drawdown.** Le drawdown passe de 15,7 % à 12,6 % et le CAGR de 3,47 % à 2,78 %, soit un cinquième du rendement annuel. Le Sharpe ponctuel baisse. Les 222 stops font passer à plat 106 séances de plus que `off`, et en ôtent bien davantage à des lignes isolées.
- **Le coupe-circuit est presque inerte** : deux coupures en dix ans, pour +0,028 point de CAGR et −0,2 point de drawdown face à `kernel_nocb`.
- **Aucun écart n'est significatif.** Le stop décorrèle la trace (0,906), ce qui élargit l'intervalle du bootstrap à ±0,26 environ autour de l'écart.

**Verdict : NO BEATS** pour `kernel` et `kernel_nocb`, dont le Sharpe ponctuel est inférieur à celui de `off`. Verdict **INCONCLUSIVE** pour `cap90`, dont l'écart positif n'est pas significatif (p de Holm 1,0).

**Prédictions écrites avant les runs** (commentaire `[CLAIMED]` de #24698) :

1. Innocuité tenue : **tenue**.
2. Le plafond mord souvent et baisse CAGR et drawdown, sans écart de Sharpe significatif : **tenue**, avec un effet plus faible qu'attendu.
3. Le stop baisse le drawdown à CAGR proche : **en partie fausse**. Le drawdown baisse bien, mais le CAGR perd un cinquième de sa valeur.
4. Le coupe-circuit est presque inerte : **tenue**.
5. `kernel` contre `off` donne INCONCLUSIVE : **fausse**. Le Sharpe ponctuel de `kernel` est inférieur, donc NO BEATS, sans significativité dans un sens ni dans l'autre.

**Contraste.** Trois portefeuilles portent maintenant le noyau :

| Projet | Portefeuille | Coût du stop sur le CAGR | Gain sur le drawdown |
|---|---|---|---|
| `Cloud-VolTargeting` | une ligne, rééquilibrage mensuel | lourd : CAGR divisé par deux sur 2007-2026 | 6,1 à 6,4 points |
| `HAR-RV-Kelly` | six lignes, rééquilibrage du lundi | intermédiaire : 0,7 point, un cinquième du CAGR | 3,1 points |
| `DeterministicRiskKernel-QC` (#25221) | dix ETF, rééquilibrage hebdomadaire | presque nul | net |

Ici, un stop ne vide qu'une ligne, et au plus jusqu'au lundi suivant. Une hypothèse, non mesurée, expliquerait le coût intermédiaire : le rendement de la stratégie est faible (3,5 % par an), si bien que chaque semaine perdue par une ligne stoppée en emporte une part plus grande.

### Mesure de ligue (#26329)

La stratégie est mesurée au protocole de la ligue (#21594, gabarit #22828) : cinq modes dans un seul code (paramètre `mode`), une passe continue 2015-01-01 → 2026-07-01 par mode. Fenêtre F1 = 2015-01-01 → 2024-12-31 (la période codée), fenêtre F2 = 2025-01-01 → 2026-06-30, hors période codée. Le graphique `shadow` (e0..e4) trace les séances d'avant 2025, le graphique `shadow2` les suivantes, chaque compteur repartant de e0. La stratégie est causale : sa trace F1 dans la passe continue est celle d'une passe arrêtée fin 2024, et l'année de liquidités initiale (préchauffage de 500 variances réalisées) entre dans la mesure, telle que le code la vit.

Backtests du 2026-11-14, projet QC 31456164, compile `9ddf80f4c8379d0f5e78e21114f45ca0-2829b9bff149def10e9b688c3ce39622` (`BuildSuccess`, empreinte du `main.py` mesuré : sha256 `59654a6121d06c4d…`).

| `mode` | Backtest | Ordres | Sharpe (QC) | CAGR | Drawdown max | Profit net | PSR |
|---|---|---|---|---|---|---|---|
| `strategy` | `4ba35090f1e841fe6ccb820520b55c6a` | 1642 | 0,153 | 4,706 % | 15,700 % | 69,736 % | 0,025 % |
| `spy` | `35760d7e05958612ddb3022f1d4861be` | 2 | 0,557 | 13,891 % | 33,700 % | 346,619 % | 2,620 % |
| `6040` | `426393e633ce4a28eadd0f7e34e0bcb6` | 698 | 0,468 | 9,183 % | 21,700 % | 174,790 % | 1,233 % |
| `ew6` | `2ce5cab10334be61d06565a18ffb4aaf` | 1512 | 0,379 | 7,984 % | 21,500 % | 142,007 % | 0,481 % |
| `naivevol` | `4f0cfe9d245c282e5a0318bd02937f24` | 1642 | 0,153 | 4,706 % | 15,700 % | 69,736 % | 0,025 % |

**Témoin d'innocuité.** La `main.py` nue de `0ddc1e46fd` (compile `a8567b86…5a12c2c2991872db58f69a7accbee`, empreinte sha256 `c80afa6189cd5638…`, run `e5937392d62a1fb2c6a4277b81ac37df`) et le code instrumenté en mode `strategy`, lancés le même jour, rendent les mêmes 1358 ordres (date, titre, quantité) sur la fenêtre codée : le code de mesure ne change pas la stratégie. Le run nu reproduit aussi la mesure de #24698 (Sharpe QC 0,065, CAGR 3,470 %, drawdown 15,700 %).

Par fenêtre, depuis les traces `shadow` (taux sans risque nul, 252 jours par an) :

| Mode | F1 CAGR | F1 drawdown | F1 Sharpe | F2 CAGR | F2 drawdown | F2 Sharpe |
|---|---|---|---|---|---|---|
| `strategy` | 3,479 % | 15,731 % | 0,491 | 13,487 % | 6,823 % | 1,224 |
| `spy` | 13,216 % | 33,668 % | 0,794 | 19,385 % | 18,741 % | 1,080 |
| `6040` | 8,593 % | 21,694 % | 0,810 | 13,800 % | 11,247 % | 1,217 |
| `ew6` | 5,835 % | 21,480 % | 0,580 | 24,416 % | 9,176 % | 1,849 |
| `naivevol` | 3,479 % | 15,731 % | 0,491 | 13,487 % | 6,823 % | 1,224 |

**Test apparié.** `Paradox46Benchmarks/significance.py` (écart de Sharpe Ledoit-Wolf, Newey-West, bootstrap stationnaire, Holm) sur les rendements journaliers des traces, fenêtre par fenêtre, candidate contre `spy` et `6040` pour le verdict, contre `ew6` et `naivevol` pour le diagnostic :

| F1 (2516 séances) | Écart | Corrélation | p Ledoit-Wolf | IC 95 % bootstrap | p Holm |
|---|---|---|---|---|---|
| contre `spy` | −0,303 | 0,294 | 0,365 | [−0,952 ; +0,335] | 1,0 |
| contre `6040` | −0,318 | 0,330 | 0,345 | [−0,975 ; +0,313] | 1,0 |
| contre `ew6` | −0,089 | 0,501 | 0,764 | [−0,637 ; +0,469] | 1,0 |

| F2 (373 séances) | Écart | Corrélation | p Ledoit-Wolf | IC 95 % bootstrap | p Holm |
|---|---|---|---|---|---|
| contre `spy` | +0,144 | 0,374 | 0,868 | [−1,671 ; +1,725] | 1,0 |
| contre `6040` | +0,007 | 0,384 | 0,994 | [−1,745 ; +1,520] | 1,0 |
| contre `ew6` | −0,625 | 0,679 | 0,298 | [−1,777 ; +0,381] | 1,0 |

**Verdict : NO BEATS sur F1** (Sharpe 0,491 sous les 0,794 de SPY détenu) ; **INCONCLUSIVE sur F2** (+0,144 contre `spy`, non significatif, p Holm 1,0). Sur la passe continue, le Sharpe QC (0,153 contre 0,557) confirme le NO BEATS.

**Propriétés publiées (protocole #26329).** Poids bornés à 0,30 avant renormalisation : 1213 sur 1215 poids positifs (99,8 %). Rééquilibrages renormalisés (somme des poids > 1) : 145 sur 492 (29 %). Premier rééquilibrage effectif : 2016-01-04. Ordres envoyés le lundi 30 minutes après l'ouverture, remplissage moyen 21 534 s (environ 6 heures) plus tard, soit la clôture de la même séance (#20264). Séances à plat : 532 sur 2890 (18 %).

**Lecture.**

- **Le modèle HAR n'entre jamais dans le dimensionnement.** Le mode `naivevol` — même code, prévision HAR remplacée par la moyenne géométrique des 22 dernières variances réalisées — reproduit la stratégie **à l'identique** : 0 séance différente sur 2889, statistiques QC égales à l'octet près (mêmes ordres, mêmes frais, même volume). Gonflé par le défaut d'échelle (variance annuelle divisée par 5, cf #26329), le Kelly dépasse le plafond de 0,30 sur presque tous les poids ; après renormalisation, le portefeuille est l'équipondéré des lignes à momentum 5 jours positif. La corrélation avec `ew6`, la plus haute des bancs (0,50 en F1, 0,68 en F2), le confirme. Corriger l'échelle (une autre issue) est la seule voie pour que la prévision compte.
- **F2 ne sauve pas la stratégie.** La fenêtre 2025-2026 lui donne 13,5 % par an pour 6,8 % de drawdown, mais l'univers détenu à poids égal en fait 24,4 % : la fenêtre favorise l'univers, pas le modèle.
- **SPY détenu domine F1 en Sharpe ponctuel** (0,794 contre 0,491) avec un drawdown deux fois plus profond (33,7 % contre 15,7 %) : la stratégie paie son rendement faible, pas sa protection.

**Prédictions écrites avant les runs** (body de #26329) :

1. Innocuité tenue : **tenue**.
2. F1 : NO BEATS ou INCONCLUSIVE, pas de BEATS : **tenue** (NO BEATS).
3. Plus de la moitié des poids non nuls bornés à 0,30 : **tenue** (99,8 %).
4. `naivevol` : écart non significatif face à `strategy`, le plafond dominant : **tenue au-delà** — l'écart est nul, identité parfaite.
5. `ew6` : écart non significatif : **tenue**.
6. F2 : sans prédiction (INCONCLUSIVE).

**Traces et panier (brique 4).** Dépôt : `G:\Mon Drive\MyIA\IA\QC-traces\26329-har-rv-kelly-held-references\` — un dossier par run (`backtest.json` relecture verbatim, `backtest_id.txt`, `chart.json` trace F1, `chart-f2.json` trace F2, `plan.json` avec empreinte du `main.py` mesuré), le témoin nu dans `control/`, `significance-f1/f2.json` (sorties de l'organe), `innocuite.txt` et les journaux d'ordres (`orders-nu.json`, `orders-strategy.json`). La trace F1 de `strategy` est inscrite au panier (`ML-Training-Pipeline/shadow/league_members.json`, entrée `har-rv-kelly`).

Suites possibles, non mesurées : corriger le défaut d'échelle (autre issue, autre stratégie), refaire l'ablation du noyau une fois corrigé, tester un stop plus large ou une re-entrée dans la semaine.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Prévision de volatilité HAR-RV avec dimensionnement par critère de Kelly sur 6 ETFs multi-actifs |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec analyse du modèle HAR-RV et exploration de la fraction Kelly |

## Références

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Kelly, J.L. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
