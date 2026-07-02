# L3 — Trend Long-Horizon (LSTM directionnel, Panier Anti-Biais 25 Symboles)

## Verdict : NO BEATS

Premier échelon ML du ladder (Epic #1409) : un LSTM entraîné sur GPU pour prédire la
**direction** des rendements à long horizon ($h \in \{60, 120, 252\}$ jours) sur le panier
anti-biais (25 symboles, 7 classes d'actifs, sans FAANG/Mag7). **Aucune cellule
(symbol × horizon) ne passe le gate d'edge** : la prédiction de direction long-horizon
n'est pas statistiquement exploitable.

## Méthode

- **Modèle** : LSTM entraîné à prédire le **signe** du rendement futur (classification
  directionnelle), pas son amplitude.
- **Horizons** : $h \in \{60, 120, 252\}$ jours (≈ 3 / 6 / 12 mois).
- **Sweep GPU** : 300 combinaisons (25 symboles × 3 horizons × 4 seeds), run réel
  (`device: cuda`, `smoke: false`), ~15 min sur GPU 2.
- **Gate d'edge** : un combo est déclaré « signal » si son edge cross-seed
  $\geq 2\sigma$ (`EDGE_SIGMA = 2.0`).
- **Baselines** : majority (« toujours prédire la classe majoritaire ») + buy-and-hold.
- **Validation** : walk-forward expansif, 5 folds, gap 21j, 4 seeds (0/1/7/42).

## Résultats

| Métrique (300 combos) | Valeur | Lecture |
|-----------------------|--------|---------|
| Cellules « signal » (edge ≥ 2σ) | **0 / 75** | aucune cellule exploitable |
| `sigma_edge` max observé | **1.49** | sous le seuil 2.0 requis |
| AUC médian | **0.509** | ≡ hasard (0.5 = pile-ou-face) |
| AUC moyen | 0.508 | 64.7 % des combos > 0.5 (à peine mieux que le hasard) |
| `dir_acc` LSTM (médian) | 0.505 | **< majority 0.521** |
| Combos où LSTM > majority | **24 %** | perd contre la baseline triviale |
| `delta_sharpe` médian (vs B&H) | **−0.51** | seulement 8.7 % des combos > 0 |

**Par horizon** (hypothèse « horizon long = plus prévisible ») :

| Horizon | n | mean AUC | mean delta_sharpe | frac delta > 0 |
|---------|----|----------|-------------------|----------------|
| 60 j    | 100 | 0.503 | −0.441 | 8 % |
| 120 j   | 100 | 0.511 | −0.574 | 5 % |
| 252 j   | 100 | 0.509 | −0.501 | 13 % |

L'AUC est **plate** (~0.50–0.51) quel que soit l'horizon : allonger l'horizon n'extrait pas
plus de signal trend prédictible. Le Sharpe n'est pas monotone non plus.

**Cellules extrêmes** (delta_sharpe moyen sur les seeds) :

- Pires : SHY/252j (−2.14), XLB/120j (−1.31), RSP/120j (−1.09) — obligations et ETFs à
  faible trend, là où la prédiction directionnelle échoue le plus.
- Meilleures : TLT/252j (+0.38), ETH-USD/252j (+0.23), DBA/252j (+0.06) — restent
  marginales et ne passent pas le gate.

## Conclusions clés

1. **Le LSTM n'apprend rien de prédictible à long horizon.** AUC médian 0.509 ≡ hasard ;
   64.7 % des combos dépassent à peine 0.5. Le signal « trend directionnel » n'existe pas
   à ces horizons sur ce panier.

2. **Pire que la baseline majority.** La précision directionnelle du LSTM perd contre
   « toujours prédire la classe majoritaire » dans 76 % des combos — un modèle utile
   doit au minimum battre cette baseline triviale.

3. **Impact trading net négatif.** delta_sharpe médian −0.51, seulement 8.7 % des combos
   battent le buy-and-hold. L'échec est net sur les obligations (SHY) et les ETFs à faible
   trend.

4. **L'horizon ne sauve pas le signal.** Allonger de 60j à 252j ne creuse pas l'AUC
   (0.503 → 0.509) : la prédictibilité directionnelle est plate, pas croissante.

## Données

- 25 symboles du panier anti-biais (VIX exclu : pas de price-return), 7 classes d'actifs.
- Plage : 2015-01-02 à 2026-05-23.
- Résultats du sweep GPU **committés** dans
  `scripts/results/l3_trend_long_horizon/` (`results.json` : verdict agrégé + 75 cellules ;
  `checkpoint.jsonl` : 300 lignes combo avec AUC, dir_acc, majority, sharpe).

## Script et notebook

- Sweep GPU canonique : `scripts/L3_trend_long_horizon_gpu.py` (#1576 / #1417).
- Notebook d'interprétation (CPU-only, reproduit le verdict sans ré-entraîner) :
  `research_l3_trend.ipynb` (#4926).

## Implication pour le ladder

L1 (TSMOM) et L2 (CS+DM) sont NO BEATS à cause des **coûts de rotation** et du **B&H
dominant** (Sharpe 1.15). L3 (ML directionnel) est NO BEATS à cause de
l'**imprédictibilité directionnelle** elle-même : trois échecs distincts convergent vers
le même constat — prédire un *retour* (L3) ou un *signe de momentum* (L1/L2) ne suffit pas.

C'est ce qui motive **L4 Decision Transformer** : au lieu de prévoir un retour, apprendre
directement une **action** (buy/hold/sell) par offline RL. L4 est le **seul échelon qui
BEATS** le buy-and-hold (#1461), confirmant que le changement de paradigme
(action-based) contourne l'échec de la prévision de retour.

Référence : sweep GPU canonique `scripts/L3_trend_long_horizon_gpu.py` (#1576). Epic #1409.
