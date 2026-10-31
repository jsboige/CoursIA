# L4 — Decision Transformer (Offline RL action-based, Panier Anti-Biais 25 Symboles)

## Verdict : NO BEATS (panel re-mesuré sous protocole causal, #21187)

> **État mesuré au 2026-10-20 (#21187).** Le panel de 25 symboles a été re-mesuré sous le protocole `causal-v1` (#21584) : **NO BEATS, 0/25**. Aucun écart positif contre buy & hold ne reste significatif après correction de Holm, et le DT ne bat pas non plus son teacher momentum. L'ablation de la tranche 3 rendait déjà **`NO SKILL`** (6 symboles, témoin apparié en exposition, plus petit p de Fisher 0,381 : [c.6248538028](https://github.com/jsboige/CoursIA/issues/21187#issuecomment-6248538028)).
>
> L'ancien verdict « BEATS (panel @10bps) » venait d'un protocole qui lisait l'avenir. L'entrée « retour à venir » du modèle était la somme des récompenses futures du fold de test (RTG réalisé), et la simulation du sweep associait les positions aux mauvais rendements. Ses chiffres sont conservés plus bas, dans une section historique, avec ceux des holdouts du 06/08 et du run OOT du 04/09, eux aussi antérieurs aux correctifs.

Un Decision Transformer (Chen et al. 2021) entraîné en **offline RL** apprend directement une **action** (rester investi ou à plat) à partir de trajectoires, au lieu de prévoir un *retour* (L3) ou un *signe de momentum* (L1/L2). L'échelon a longtemps été présenté comme le seul du ladder (Epic #1409) qui batte le buy-and-hold. Sous le protocole causal, ce n'est plus le cas : sur le panier anti-biais (25 symboles, 7 classes, sans FAANG/Mag7), le DT reste sous buy & hold sur 20 symboles sur 25, et ses cinq écarts positifs ne sont pas significatifs.

## Méthode

- **Modèle** : Decision Transformer (Chen et al. 2021, « RL via Sequence Modeling »),
  entraîné sur des trajectoires (état, action, retour) pour prédire la **bonne action**
  (position discrète), pas l'amplitude du retour. 642 563 paramètres (d_model 128,
  4 têtes, 3 couches, contexte 20, état de 360 caractéristiques).
- **Features** : rendements, volatilité réalisée, RSI, MACD, etc. (ingénierie classique).
- **Protocole `causal-v1` (#21187)** : la décision qui s'applique au rendement de k à k+1
  ne lit que des lignes antérieures ou égales à k−2 ; le RTG est fixé sur le fold
  d'entraînement ; une décision par pas ; positions longues ou à plat. Tous les scripts
  d'évaluation passent par ce protocole : `validate_xrp_dt.py`, `validate_xrp_dt_holdout.py`
  et `ablation_rtg_leak.py` (#21196, #21240), puis `sweep_l4_decision_transformer.py`,
  `train_dt_multiseed.py` et `eval_rl_dt.py`.
- **Validation** : walk-forward **5 folds × 4 graines** (0/1/7/42), 15 époques par fold,
  **pas de FAANG/Mag7** (`panier_loader.FORBIDDEN_SYMBOLS` enforced).
- **Références** : buy & hold du symbole, et le **teacher** dont le DT apprend les
  trajectoires (momentum 20 jours, seuils ±1 %). Coût de 5 bps par changement de position,
  sur le DT comme sur le teacher, scorés sur les mêmes rendements.
- **Verdict qualifié** : un symbole est « BEATS » si l'écart de Sharpe contre buy & hold est
  positif, si la règle sigma passe (`sigma_edge = mean_delta / std_delta` ≥ 2 entre
  graines) **et** si le test de Ledoit-Wolf (HAC) sur le portefeuille équipondéré des
  politiques des graines reste sous 0,05 après correction de Holm. La règle sigma mesure la
  dispersion entre graines, pas la significativité : elle ne suffit pas seule.

## Résultats (protocole causal, #21584)

| Mesure (25 symboles × 4 graines) | Valeur | Lecture |
|---|---|---|
| DT au-dessus de buy & hold (moyenne des graines) | **5 / 25** | XLV +0,155, XRP +0,145, LTC +0,129, DBA +0,117, BTC +0,004 |
| Règle sigma passée (σ ≥ 2 et écart > 0) | **0 / 25** | σ maximal : DBA 1,44 |
| Écart positif significatif après Holm, contre buy & hold | **0 / 24** | p brutes des cinq écarts positifs : 0,54 à 0,95 |
| Écart significatif après Holm, contre le teacher | **0 / 24** | plus petite p brute : XLY 0,074 |
| `mean_delta` (Sharpe DT − buy & hold) | min −1,09 · **médian −0,40** · max +0,16 | écart négatif sur 20 symboles |
| `delta_sharpe` (100 graines) | **16 % > 0** · médian −0,42 | la plupart des graines perdent |
| Symboles avec 4/4 graines positives | 1 / 25 | |
| DT au-dessus de son teacher | 11 / 25 | aucun écart significatif |
| Corrélation DT / teacher entre symboles | 0,877 (Sharpe), 0,936 (exposition) | le DT suit son teacher |
| AUC médiane (25 symboles hors VIX) | **0,497** | hasard (L3 : 0,509) |

**Symboles exclus des tests** (motif écrit dans le carnet) : VIX, dont le `Volume` vaut 0 sur
toutes les lignes, si bien qu'aucune ligne de caractéristiques ne survit et qu'aucune graine
n'est entraînée ; SHY, où le DT n'est jamais investi : sa série est constante et l'erreur
standard du test dégénère. SHY reste dans le tableau (écart à buy & hold −0,73), d'où 24 tests.

Quatre écarts **négatifs** sont significatifs avant correction (GLD, XLY, EFA, EEM) ; Holm les
porte à 0,08 et au-delà.

## Conclusions clés

1. **Le DT ne bat pas le buy-and-hold.** Écart médian −0,40 de Sharpe, 16 % des graines
   positives, aucun écart positif significatif après Holm. L'ancien delta médian de +1,20
   ne survit pas au retrait de la fuite.

2. **Le DT reproduit son teacher.** La corrélation entre symboles de son Sharpe avec celui du
   teacher momentum est de 0,877, celle de son exposition de 0,936, et il ne bat le teacher
   que sur 11 symboles sur 25, sans écart significatif. Sous le protocole causal, l'offline
   RL apprend surtout à imiter la politique qui a produit ses trajectoires.

3. **L'action ne contourne pas l'imprévisibilité.** L'ancienne conclusion (« un modèle qui
   prévoit une action n'a besoin que du signe de la position optimale ») reposait sur un RTG
   qui contenait le résultat à venir. Sans lui, l'AUC médiane retombe à 0,497, au niveau de
   L3 : prévoir une action ne donne pas plus d'information que prévoir un retour.

4. **D'où venait l'edge.** Le RTG réalisé du test indiquait au modèle combien la suite allait
   rapporter, et le décalage entre positions et rendements dans la simulation du sweep
   faisait le reste. Ce sont deux fuites de l'avenir, pas une propriété du paradigme : le
   détail des correctifs est dans #21187.

## Données

- 25 symboles du panier anti-biais (VIX exclu faute de volume), 7 classes d'actifs.
- Plage : 2015-01-01 à 2026-05-22 (`data.first_day` et `data.last_day` du résultat ci-dessous).
- Sortie du balayage causal **committée** dans `scripts/results/l4_decision_transformer/results.json`
  (`eval_protocol: causal-v1 (#21187)`, verdict agrégé, une cellule par symbole, détail par graine et par
  fold, tests de Ledoit-Wolf contre buy & hold et contre le teacher). 104 combinaisons, 2,7 h
  sur cuda.

## Script et notebook

- Sweep canonique : `scripts/sweep_l4_decision_transformer.py` (réutilise
  `DecisionTransformerModel` de `train_rl_dt.py`). Depuis #21187, il évalue chaque fold
  avec les organes causaux de `ablation_rtg_leak.py` (`causal_condition_actions`,
  `causal_eval_returns`, `simulate_dt_portfolio`, `score_actions`). Ses sorties portent
  `eval_protocol`, et ajoutent `mean_hit_rate`, `mean_exposure`, la série du teacher et les
  tests de significativité.
- Notebook : `research_l4_decision_transformer.ipynb` + figure `research_l4_dt_results.png`
  (lecture de la sortie causale, tableau par symbole, tests avec Holm, verdict qualifié).

## Historique — mesures antérieures au protocole causal

Les sections qui suivent sont conservées pour l'historique. Toutes ont été produites avant
les correctifs de #21187 et de #21196 : leurs chiffres ne font pas foi.

### Panel du sweep initial (RTG réalisé)

Le verdict d'origine était « BEATS (panel @10bps) » :

| Métrique (25 symboles × 4 seeds = 100 delta_sharpe) | Valeur publiée |
|-----------------------------------------------------|--------|
| Cellules « signal » (edge ≥ 2σ et delta > 0) | 24 / 26 |
| `sigma_edge` (cross-seed) | min 0.0 · médian 9.98 · max 31.82 (BTC-USD) |
| `mean_delta` (Sharpe vs B&H) | min −1.94 · médian +1.20 · max +1.95 |
| Cellules avec 4/4 seeds positifs | 25 / 26 |
| `delta_sharpe` (100 seeds) | 96 % > 0 · médian +1.23 |
| AUC médian | 0.558 |

Le benchmark était un buy-and-hold équipondéré (Sharpe 1.15), et le gate d'edge (G.2) ne
demandait que `sigma_edge` ≥ 2 et `mean_delta` > 0, sans test de significativité. Les deux
cellules hors signal étaient VIX (pas de rendement de prix) et SHY (delta −1.94) ; les plus
forts edges publiés, BTC-USD (σ 31.8), XLC (σ 20.0) et XLF (σ 16.5).

### Holdout temporel 06/08

Le verdict panel ci-dessus (24/26, edge 9.98σ cross-seed, 5/5 seeds @10bps edge 3.84σ
DM p 0.024) avait été testé en **holdout temporel** le 06/08 (`scripts/validate_xrp_dt_holdout.py`,
XRP, période jamais touchée par le walk-forward). `validate_xrp_dt.py` n'avait pas encore
reçu son correctif (#21196) :

| Run holdout (06/08) | Split | seeds > BH | `edge_sigma` | DM p médian | Verdict |
|---|---|---:|---:|---:|---|
| `holdout_internal_20260806_093143` | interne (train .. train-end ; holdout = train-end+gap .. fin) | 0/5 | **−6.63** | 0.0847 | **NO-BEATS** |
| `holdout_fresh_20260806_094210` | split frais (jamais vu) | 5/5 | **+19.97** | 0.236 | INCONCLUSIVE |

Le `+19.97σ` du split frais ne validait pas l'edge : la dispersion du dénominateur
`edge_sigma` est *inter-seeds* (reproductibilité de la procédure), pas la significativité
de l'edge, c'est pourquoi le test de Diebold-Mariano (p 0.236) ne rejetait pas.

La page concluait alors à un edge « borné » : BEATS en panel @10bps, NO-BEATS en holdout
temporel interne, INCONCLUSIVE en holdout frais. Le panel causal tranche la question dans
l'autre sens : l'edge ne vivait pas plus dans la coupe transversale que dans le temps.

Résultats détaillés : `results/xrp_dt_validation/holdout_internal_20260806_093143.json` et
`holdout_fresh_20260806_094210.json` (gitignored, machine d'entraînement).

### Protocole OOT (#14579), run du 04/09

L'issue #14579 demande le premier verdict **out-of-time véritable** : l'entraînement est gelé à
une borne, le holdout est postérieur et **absent de tous les folds et de toute sélection
d'hyperparamètres**. L'instrument mis en place le 04/09 reste valable ; le run du 04/09 est
antérieur au correctif de `validate_xrp_dt.py` (#21196) et devra être rejoué sous le
protocole causal.

| Brique | Où | Rôle |
|---|---|---|
| **Gel de borne** `--train-end` | `scripts/train_dt_multiseed.py` | Tronque le CSV à la borne inclusive AVANT le walk-forward ; le hash est recalculé sur la tranche gelée (l'absence de contamination devient vérifiable). |
| **Jambe de précision §C** | `scripts/validate_xrp_dt_holdout.py` | Erreur directionnelle `e_t = position_t − sign(r_{t+1})` — une politique alignée au marché fait `e = 0`, une politique opposée `e = ±2` : le DM mse/mae sur `e` est sign-aware pour des positions ±1 (le mse direct sur les retours positionnés reste sign-blind, `(−r)² = r²`, cf #10228). |
| **Contrôle de biais** | idem | DM `linear` sur les retours positionnés (différentiel de performance moyenne), **jamais la jambe de conjonction** (§C amendé #11010) ; biais signés par modèle (`mean(return)` DT / momentum / BH) rapportés dans le JSON. |
| **Conjonction** | idem | `seeds_beat ≥ min(4, len(seeds))` **et** `edge ≥ 2σ` cross-seed **et** `dm_p_mse_median < 0.05` (mae rapportée en variante) — dans cet ordre, celui du code (`validate_xrp_dt_holdout.py`, verdict `BEATS`). La médiane des p DM exige la significativité sur une majorité de seeds : un seed chanceux sur cinq ne fait pas passer le 3e conjonct. Sinon `NO-BEATS` / `INCONCLUSIVE` explicites. |

Dataset de référence (04/09, yfinance, gitignored) : `XRP-USD.csv` — bornes
`2018-01-01 → 2026-09-04` (3169 rows), sha256 `71d8aee9d0bda18b`.

**Verdict du run OOT (`--label oot --train-end 2025-06-30`, seeds 0/1/7/42/99, 30 epochs) :**

| Run | Split | seeds > BH | `edge_sigma` | DM mse p médian | DM mae p | DM linear p (biais) | Biais moyens (retour/jour) | Verdict |
|---|---|---:|---:|---:|---:|---:|---|---|
| `holdout_oot_20260904_164308` | OOT véritable : train gelé ≤ 2025-06-30 (hash recalculé), holdout 2025-07-10 → 2026-09-04 — **absent de tous les folds** | 0/5 | **−5.38** | 0.1419 | 0.2642 | 0.2969 | DT −0.004059 · momentum −7.5e-05 · BH −0.001406 | **NO-BEATS** |

Lecture d'alors : le troisième test temporel (après interne et frais du 06/08) confirmait le
NO-BEATS sur la vraie fenêtre future. Le DT net Sharpe −1.744 (± 0.214) était battu par le
buy-and-hold (−0.592) sur une fenêtre baissière XRP, avec un signe directionnel négatif sur
0/5 seeds. Ce NO-BEATS va dans le sens du panel causal, mais ses chiffres viennent d'un
évaluateur non corrigé. Résultats par seed complets (séries de retours incluses pour
re-calcul DM) : `results/xrp_dt_validation/holdout_oot_20260904_164308.json` (gitignored).

**Reproductibilité du verdict.** Les JSON de verdict et les CSV de marché sont
**gitignored** : `results/` est un artefact machine-local d'entraînement, et la politique du
pipeline garde le dépôt sur les protocoles et verdicts, pas sur les sorties d'entraînement ni
les données de marché. Ce qui est cité pour permettre la réfutation : bornes exactes, sha256
du dataset (`71d8aee9d0bda18b`), verdicts par seed et séries de retours par seed **dans** le
JSON. Pour rejouer : re-télécharger `XRP-USD.csv` via yfinance (bornes 2018-01-01 →
2026-09-04), vérifier le sha256, puis relancer l'instrument gelé —
`scripts/train_dt_multiseed.py` avec `--train-end 2025-06-30` (seeds 0/1/7/42/99, 30 epochs),
puis `scripts/validate_xrp_dt_holdout.py` (jambe §C + conjonction ci-dessus) ; le hash est
recalculé sur la tranche gelée, ce qui rend l'absence de contamination vérifiable.

## Implication pour le ladder

| Échelon | Paradigme | Verdict |
|---------|-----------|---------|
| L1 TSMOM | momentum temporelle (signe) | NO BEATS (coûts de rotation) |
| L2 CS+DM | momentum cross-sectionnelle | NO BEATS (B&H dominant) |
| L3 LSTM | prévision de **direction/retour** | NO BEATS (AUC ≡ hasard) |
| **L4 Decision Transformer** | **prévision d'action** (offline RL) | **NO BEATS** (panel causal 0/25, #21187) |

Les quatre échelons échouent. L1/L2/L3 échouent pour des raisons distinctes (coûts, B&H,
imprédictibilité directionnelle). L4 ne fait pas exception : une fois le RTG fixé sur le fold
d'entraînement et les décisions alignées sur les rendements qui les suivent, le DT imite son
teacher momentum et reste sous buy & hold. Le BEATS qui distinguait L4 venait d'une fuite de
l'avenir, et non du passage de la prévision de retour à l'apprentissage d'une action.

Référence : Chen et al., *Decision Transformer: Reinforcement Learning via Sequence
Modeling*, NeurIPS (2021). Sweep canonique `scripts/sweep_l4_decision_transformer.py`.
Epic #1409.
