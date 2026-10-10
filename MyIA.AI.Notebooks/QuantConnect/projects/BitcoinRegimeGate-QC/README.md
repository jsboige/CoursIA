# BitcoinRegimeGate-QC — porte de régime BTC pour QQQ/SHY

Distillation de l'article QC Research **« Bitcoin Regime Signal for Growth Equities »** (Derek Melchin, publié août 2026) — [source](https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/). Porté dans le dépôt pour l'issue #18576 (re-évaluation de la lecture #12748 : les raisons « non publié » et « pas de sources primaires » du verdict IGNORE d'août sont tombées sur la version publiée).

## Idée

Lire le régime de risque sur le **BTC, un marché 24/7** (« no halts, circuit breakers, or closing bell » — l'auteur), pour allouer entre **QQQ** (risque on) et **SHY** (risque off) — la face **crypto → equity** du spillover documenté par Iyer 2022 (IMF GFSN 2022/001) : le BTC explique 14-18 % de la variation de volatilité equity, ~17 % pour le S&P 500.

**Règle** (fidèle à l'article) :

> QQQ si (BTC > SMA50 BTC) **ET** (ROC20 BTC > 0), sinon SHY.
> Réévaluation hebdomadaire : premier jour de trading à 8 h ET, avant l'open US.

C'est le même geste que `DynamicVIXSpyRegime-QC` (gate de régime → equity/obligataire), avec une **source différente** (BTC Bitfinex 24/7 au lieu du VIX) et un sous-jacent growth (QQQ). La cohorte BTC tranche 11 du dépôt avait mesuré **0 edge crypto → crypto** ; ce distillat teste la face crypto → equity, non couverte.

## Sources primaires (article publié)

- Faber 2007 (SSRN 962461) — timing tactique par moyenne mobile.
- Liu & Tsyvinski 2021 (RFS 34(6)) — risques crypto systématiques.
- Iyer 2022 (IMF GFSN 2022/001) — spillovers BTC → vol equity.

## Mesures #19929 — test de différence contre références détenues (QC Cloud, 2026-10-08)

Une seule compilation, quatre backtests sur le même projet QC, sélectionnés par le paramètre `mode` : `gate` (le candidat), et trois **références détenues** — `hold-qqq` (QQQ buy-and-hold), `spy` (SPY détenu) et `sixty40` (60 % SPY / 40 % IEF, rééquilibrés le premier jour de bourse du mois). Période 2016-01-04 → 2026-06-30, **2 636 séances communes** aux quatre backtests (fin de période demandée, aucune troncature J-90).

Le Sharpe est calculé à taux sans risque nul sur les valeurs à chaque clôture ; il diffère de celui affiché par QC (0,894 pour le gate), qui déduit un taux sans risque. Le décompte ci-dessus est celui des rendements : les séries portent 2 637 valeurs de portefeuille.

| Version | Sharpe | CAGR | MaxDD |
|---|---|---|---|
| **gate** (candidat) | **1.3139** | 16.54 % | **-15.21 %** |
| hold-qqq (QQQ détenu) | 0.9608 | 20.56 % | -34.89 % |
| spy (SPY détenu) | 0.8838 | 15.16 % | -33.59 % |
| sixty40 (60 % SPY / 40 % IEF) | 0.9350 | 9.68 % | -21.14 % |

**Verdict : NO BEATS.** Le test de différence est un bootstrap par blocs circulaires (21 séances, 10 000 tirages, graine 18921, la même graine pour toutes les paires) sur la différence de Sharpe `gate − référence`, avec correction de Holm sur les trois références :

| Référence | Différence de Sharpe | p brut | p Holm | IC 95 % |
|---|---|---|---|---|
| hold-qqq | +0.353 | 0.1058 | 0.2952 | [-0.1968, 0.8754] |
| spy | +0.430 | 0.0984 | 0.2952 | [-0.2085, 1.0137] |
| sixty40 | +0.379 | 0.1237 | 0.2952 | [-0.2585, 0.9665] |

Aucune différence n'est significative (p Holm 0.2952 partout, les intervalles de confiance à 95 % contiennent zéro). Le gate devance les références en ratio de Sharpe estimé (Sharpe +0.35 / +0.43 / +0.38) avec une pire baisse nettement plus faible, mais l'écart reste dans le bruit d'échantillonnage : **l'avantage descriptif de la mesure du 2026-09-30 n'est pas reproduit comme significatif**. Les backtests de grille (`gate_sma30`, `gate_sma70`, `gate_roc10`, `gate_roc30`, `gate_monthly`) et de frais doublés (`gate_fees2`) ne sont **pas** lancés : le protocole préinscrit les rend conditionnels à une significativité qui n'est pas là.

### Réserves d'exécution (mesuré tel qu'implémenté)

Ces chiffres sont ceux du code **tel qu'implémenté**, pas d'un basculement QQQ/SHY parfait. Compteurs d'exécution du backtest `gate` : **134 tentatives de cible** (67 vers QQQ, 67 vers SHY), exposition brute moyenne **0.966**, rotation **22.154 / an**, frais rapportés à l'equity **0.101 % / an**.

Défaut d'ordre **confirmé** (`orders.json`, exécution `gate`) : 250 ordres = **233 remplis + 17 invalides**. Les 17 invalides portent tous le motif **« Insufficient buying power »**, sont tous des **achats** (SHY 8, QQQ 9) et sont tous soumis à **8 h ET, avant l'open** — l'heure du rééquilibrage hebdomadaire. La cause est la forme du rééquilibrage : à la bascule de cible, `liquidate()` puis `set_holdings()` partent avant l'open alors que la vente n'est **pas encore remplie** (en journalier, l'ordre du matin est rempli à la clôture) ; la jambe d'achat est contrôlée contre un pouvoir d'achat que la vente en attente n'a pas encore libéré. Conséquence : sur ces 17 tentatives (≈ 12,7 % des 134), l'achat cible a été refusé tandis que la vente précédente a ensuite été exécutée ; le portefeuille passe donc en liquidités plutôt que dans l'actif cible jusqu'à une nouvelle décision. Le comportement de base (la règle, et le couple `liquidate()` → `set_holdings()`) est **préservé tel quel** ; une correction n'est **pas** revendiquée ici — c'est une hypothèse à éprouver par une expérience dédiée, pas un résultat mesuré.

Corrélations hebdomadaires au gate : hold-qqq 0.567, spy 0.497, sixty40 0.516.

## Exécution séparée #20006 — mesure du 2026-10-09

Le paramètre `execution=base` reste le défaut et conserve la mesure précédente.
`execution=settled` garde le même signal et la même décision hebdomadaire : il mémorise
la cible avant de liquider l'autre ETF, puis demande l'achat depuis une barre ultérieure,
seulement quand cette autre position est nulle et qu'aucun ordre QQQ/SHY n'est ouvert.
L'intention est effacée avant soumission ; aucun achat ne part d'un callback d'ordre.
Une vente refusée ou annulée peut être retentée à la décision suivante, jamais dans les
barres intermédiaires. Ce bras est une variante d'exécution, pas une bascule simultanée.

Cinq backtests QC Cloud terminés, même compilation et empreinte `a73a6fe144a7`, sur
2016-01-04 → 2026-06-30 : 2 636 rendements communs, aucune troncature. Le rejeu `base`
reproduit les métriques de #19929 et ses 17 achats refusés.

| Exécution | Sharpe sans taux sans risque | CAGR | Pire baisse | Exposition moyenne | Rotation annuelle |
|---|---|---|---|---|---|
| `base` | 1,3139 | 16,54 % | −15,21 % | 0,966 | 22,154 |
| `settled` | 1,3283 | 16,22 % | −16,28 % | 0,908 | 22,554 |

**Défaut corrigé sur cette fenêtre, sans avantage démontré.** Le journal complet donne
237 ordres remplis sur 237 sous `settled`, zéro refus et zéro annulation. La reconstruction
chronologique des événements vérifie les 119 demandes d'achat : aucune avant extinction
de l'autre position ni pendant un ordre ouvert ; aucune position courte. Les scénarios
partiels/annulés/refusés sont testés localement, mais ne se sont pas produits dans ce
backtest : leur couverture n'est pas une observation de courtage.

**Coût du délai.** Le compteur donne 238 clôtures sans position et 1,3 jour moyen entre
décision et **soumission**, pas remplissage. Le journal des ordres ajoute 1,009 jour moyen
entre soumission et remplissage (minimum 1 jour, maximum 2,125). Par exemple, la première
décision du 4 janvier 2016 à 08:00 ET mène à une soumission le 5 à la clôture, puis un
remplissage le 6 à la clôture. Le rendement mesure ce délai journalier, pas un échange
instantané. Les 119 tentatives sous `settled` ne doivent pas être comparées aux 134 de
`base` comme si le signal avait changé : `base` retente aussi après ses passages en cash.

**NO BEATS**, selon le même bootstrap préinscrit (21 séances, 10 000 tirages, graine
18921, correction de Holm sur trois références) :

| Référence | Écart de Sharpe `settled − référence` | p Holm | IC 95 % |
|---|---|---|---|
| QQQ détenu | +0,3675 | 0,2907 | [−0,1997 ; +0,9175] |
| SPY détenu | +0,4445 | 0,2907 | [−0,2086 ; +1,0519] |
| 60/40 SPY/IEF | +0,3933 | 0,2907 | [−0,2527 ; +1,0136] |

L'écart `settled − base` est descriptif, hors Holm : +0,0145, IC95
[−0,1701 ; +0,2079], p unilatérale 0,45. Cela ne prouve **pas** une non-infériorité.
La grille et les frais doublés ne sont pas lancés : leur condition de significativité
n'est pas satisfaite. Le mode `base` demeure le défaut ; aucun choix de performance
n'est tiré de cette correction mécanique.

Validation : 25 tests de transitions et d'initialisation, compilation QC réussie et
cinq exécutions complètes. Le premier lancement a échoué à l'initialisation parce que
`self.execution` collisionnait avec la propriété native Lean `Execution` ; l'état privé
est désormais `_execution_mode`, avec une garde dans les tests. Le lancement échoué
est conservé, pas assimilé à une mesure. Les fenêtres 2016-2019 / 2020-2022 / 2023-2026
sont des découpages descriptifs ; ni le signal publié ni la réparation choisie après
constat du défaut ne constituent une validation prospective indépendante.

Traces : `G:\\Mon Drive\\MyIA\\IA\\QC-traces\\20006-bitcoin-settled\\run2`
(plans, identifiants, empreintes, séries, ordres, `results_settled.json`,
`execution_audit.json`).

## Claims de l'article confrontés — mesures du dépôt (QC Cloud, 2026-09-30)

| Claim auteur (2014-2026) | Valeur |
|---|---|
| Sharpe stratégie | 0.838 (vs QQQ 0.682, SPY 0.564) |
| Grille 30-70 j × 10-30 j | 25/25 > SPY, 23/25 > QQQ, médiane 0.812 |

**Mesuré (projet QC 37168922, même compile pour les 4 runs, benchmark QQQ buy-and-hold apparié) :**

| Run | Période | Sharpe | CAGR | MaxDD | PSR |
|---|---|---|---|---|---|
| **Gate IS** | 2016-01 → 2021-12 | **1.133** | 18.51 % | **14.40 %** | 56.4 % |
| QQQ-hold IS (benchmark) | 2016-01 → 2021-12 | 0.961 | 24.74 % | 28.20 % | 36.0 % |
| **Gate OOS** | 2022-01 → 2026-06 | **0.640** | 14.87 % | **15.20 %** | 14.3 % |
| QQQ-hold OOS (benchmark) | 2022-01 → 2026-06 | 0.426 | 15.25 % | 34.70 % | 5.9 % |

**Lecture descriptive historique, remplacée par le test ci-dessus** : sur ce découpage IS/OOS et sans test d'inférence, le gate domine le buy-and-hold QQQ en risque-ajusté sur les **deux** fenêtres (Sharpe OOS +50 %, MaxDD OOS divisé par 2.3 — 15.2 % contre 34.7 %, en couvrant le bear 2022) pour un CAGR égal. Cette lecture est **descriptive et historique** (des niveaux de Sharpe comparés entre fenêtres séparées, sans test de différence) ; elle est remplacée par le test de différence #19929 ci-dessus, qui mesure l'écart apparié sur la période commune et conclut **NO BEATS** (aucun écart significatif, p Holm 0.2952). Réserves conservées : PSR OOS 14.3 %, et la cohorte BTC tranche 11 du dépôt avait mesuré 0 edge **crypto → crypto** — l'edge revendiqué vivait sur la face **crypto → equity**. Le statut `Alive — risk-adjusted` (`docs/qc/qc-strategies-status.md`) reflète cette lecture descriptive, pas le test de différence.

## Structure

- `main.py` — algorithme LEAN sans ML : le gate de l'article est un pur filtre de régime.
- Pas de notebook de recherche : contrairement à `DynamicVIXSpyRegime-QC` (overlay RandomForest), il n'y a rien à entraîner — le distillat est le filtre lui-même.
