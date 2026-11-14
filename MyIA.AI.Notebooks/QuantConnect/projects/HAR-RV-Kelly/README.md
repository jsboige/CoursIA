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

Suites possibles, non mesurées : refaire l'ablation une fois le défaut d'échelle corrigé (#26329), tester un stop plus large ou une re-entrée dans la semaine, et mesurer la fenêtre 2025-2026.

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
