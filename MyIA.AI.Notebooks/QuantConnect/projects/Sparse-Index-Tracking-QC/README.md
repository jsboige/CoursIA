# Sparse-Index-Tracking-QC

**Classe d'actifs :** Actions US (40 large/mega caps) · **Benchmark :** SPY

**ID projet Cloud :** 35957711 · **Issue :** #14062

## Description

Sparse index tracking sous contrainte de cardinalité, sur **données réelles** : suivre SPY avec
un sous-ensemble réduit d'actions (K ∈ {6, 8, 10}) plutôt que de répliquer l'univers complet.
Versant « épreuve du réel » du compagnon de méthode
App-27 — Sparse index tracking walk-forward (`MyIA.AI.Notebooks/Search/Applications/Hybrid/`, PR #14046)
(série Search), qui pose le même problème en CP-SAT sur données synthétiques à vérité
connue. App-27 porte le modèle et le validateur ; ce projet porte le test sur prix réels avec un
backtest QC Cloud et des coûts explicites.

### Distinction de moteur (documentée honnêtement)

| | App-27 (méthode) | Ce projet (réel) |
|---|---|---|
| Solveur | OR-Tools CP-SAT, lots entiers | `scipy.optimize.nnls` + **énumération exacte sur short-list** |
| Optimalité | globale, statut/borne/gap | exacte **dans** la short-list de 12 (classement par corrélation = filtre heuristique) |
| Contraintes | cardinalité exacte, secteurs, turnover dur | cardinalité exacte à la sélection, no-trade band (pas de secteur/turnover dur) |
| Données | synthétiques à vérité connue | réelles (yfinance en recherche, QC Cloud en backtest) |

OR-Tools n'est pas disponible dans l'environnement Python QC Cloud — aucun contournement
déguisé : le sélecteur est un compromis documenté (cf règle SOTA, `main.py` en-tête et notebook
section 2).

### Protocole walk-forward (miroir d'App-27 section 5)

- Rebalancement trimestriel (63 jours ouvrés).
- À chaque date $t$ : **calibration** = 252 rendements se terminant 63 jours avant $t$ (sélection
  de la short-list et de tous les sous-ensembles K) ; **validation** = les 63 rendements
  précédant $t$ (choix de K) ; le trimestre tradé $(t, t+63]$ est le bloc **test**, jamais consulté.
- Période d'ajustement initiale (316 jours ouvrés, 2015-01 → 2016-03) jamais tradée : **tout le
  trading est hors échantillon** par construction — la période de calibration est distincte de la
  période OOS à chaque rebalancement.
- **Validateur indépendant** (App-27 section 4) : budget, cardinalité ≤ K, poids minimum
  re-vérifiés depuis le seul vecteur de poids après chaque construction.
- Coûts : **5 bps par transaction** sur le notionnel via `PercentFeeModel` (pattern canonique du
  dépôt, cf `Portfolio-IBKR-Coinbase-Hybrid/main.py`), identiques dans les deux modes, sans
  slippage (effet des frais isolé).

## Comment exécuter

### QC Cloud

Projet 35957711. Téléverser `main.py`, compiler, puis lancer les deux backtests (même compile,
seul le paramètre change) :

- `sparse-K6-8-10-2015-2026-5bps` — paramètres `{"mode": "sparse", "fee_bps": "5"}`
- `full-baseline-40assets-2015-2026-5bps` — paramètres `{"mode": "full", "fee_bps": "5"}`

Période codée en dur : **2015-01-01 → 2026-08-31** (fenêtre figée, reproductible).

### Recherche locale

`research.ipynb` (kernel `python3`, yfinance) : reproduction pédagogique du sélecteur et du
walk-forward, trois exercices, comparaison des métriques actives (RMSE, biais, TE annualisée).

## Métriques de backtest (QC Cloud, 2026-09-01)

Compile `f568fa02c28f86891b09ba483c3dc910-6ac3548de888050a391bd35be5ec2013` (`BuildSuccess`),
mêmes dates 2015-01-01 → 2026-08-31, mêmes frais 5 bps — seule change la contrainte de cardinalité :

| Indicateur | Sparse (K ∈ {6, 8, 10}) | Full (40 actifs) |
|---|---|---|
| Backtest | `sparse-K6-8-10-2015-2026-5bps` | `full-baseline-40assets-2015-2026-5bps` |
| backtestId | `fb7a8440495b581fed37d6f4cdc4db7d` | `dfdd6fb8a42afb557157e195f70a3941` |
| Ordres | **703** | 1414 |
| Ratio de Sharpe | 0.611 | **0.698** |
| CAGR | 17.003 % | **17.258 %** |
| Drawdown max | 34.700 % | **30.700 %** |
| Profit net total | 525.241 % | **541.372 %** |
| PSR | 3.749 % | 7.429 % |

Simulation walk-forward pédagogique (yfinance, même protocole, OOS 2016-04 → 2026-08) :
sparse RMSE active 0.455 %/j, TE annualisée 7.22 %, 139.5 bps de frais cumulés (42 rebalances,
cardinalité moyenne 9.2) ; full RMSE 0.202 %/j, TE 3.20 %, 58.0 bps (39 rebalances, 32.1 actifs
en moyenne). Le classement (full > sparse sur Sharpe et drawdown) est le même dans la simulation
et dans le cloud.

**Verdict honnête : la sélection sparse ne domine pas la réplication complète ici.** Le sparse
échange moitié moins d'ordres (703 vs 1414) mais concentre le portefeuille sur 5-10 lignes :
drawdown plus profond (34.7 % vs 30.7 %) et Sharpe plus faible (0.611 vs 0.698). L'économie de
coûts à 5 bps ne compense pas la concentration — et la simulation révèle le mécanisme : la
concentration fait migrer **plus de poids** par rebalance (139.5 vs 58.0 bps cumulés), donc la
contrainte de cardinalité économise des *ordres*, pas du *turnover*. Aucune des différences n'est
statistiquement significative (PSR < 10 % dans les deux modes) : non-départ statistique, pas une
hiérarchie. Leçon pédagogique : la sparse tracking ne paie que si les coûts par ligne sont élevés,
si l'univers de départ est large et bruité (500 lignes, pas 40 déjà corrélatées au marché), ou si
la contrainte est exogène (budget, mandat).

## Limites

- **Univers biaisé de survivant** : 40 valeurs choisies en 2026, toutes gagnantes de la période —
  le niveau absolu (CAGR ~17 %) surestime la capacité réelle à suivre un indice ; seule la
  comparaison sparse vs full est informative.
- Pas de contrainte sectorielle ni de turnover dur (App-27 les a ; QC Cloud n'a pas CP-SAT).
- Short-list de 12 par corrélation = filtre heuristique : l'énumération est exacte dans la
  short-list, pas sur l'univers.
- Pas de slippage (frais isolés à 5 bps exprès) ; fills daily à l'ouverture suivante.
- K ∈ {6, 8, 10} et taille de short-list fixés à l'avance, non balayés hors période.

## Fichiers

| Fichier | Rôle |
|---|---|
| `main.py` | Algorithme QC Cloud (sparse/full via paramètre `mode`), sélecteur NNLS + énumération, validateur, frais 5 bps |
| `research.ipynb` | Recherche pédagogique exécutée (yfinance) : sélecteur, walk-forward, 3 exercices, verdict |

## Renvois

- **Méthode** : App-27 — Sparse index tracking walk-forward (`MyIA.AI.Notebooks/Search/Applications/Hybrid/`, PR #14046) — modèle CP-SAT, validateur, fuite reproduite. Lien hypertexte à ajouter au merge de #14046 (cible absente de `main` tant que la PR est ouverte).
- **Issue** : #14062 (développement d'App-27 côté QuantConnect).
- **Tracking error sans cardinalité** : [QC-Py-14 — Portfolio Construction & Execution](../Python/QC-Py-14-Portfolio-Construction-Execution.ipynb) — l'arête manquante que ce projet ajoute.
