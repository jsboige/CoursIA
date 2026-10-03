# M18 : TimesFM 2.5 zero-shot contre HAR / Log-HAR / persistence / EWMA

**Modèle :** TimesFM 2.5-200M (Google Research, code et poids Apache-2.0),
zero-shot, sans fine-tuning ni calibration sur le panel.
**Date :** 2026-09-05
**Script :** `scripts/m18_tsfm_benchmark.py` · **Tests :** `scripts/tests/test_m18_tsfm_benchmark.py`
**Issue :** #14768 · **Registre :** entrée M18 dans `REGISTRY.md`

## Positionnement

Le curriculum couvre déjà PatchTST et iTransformer (`QC-Py-23b`, entrées §C
du registre : PatchTST `NO BEATS` revalidé #14081). TimesFM 2.5 entre comme
**challenger falsifiable**, pas comme keeper présumé : la littérature primaire
(Goel et al. 2025, https://arxiv.org/abs/2505.11163 sur TimesFM 2.0 ;
comparaison zero-shot 50 actifs 1/5/22 j, https://arxiv.org/abs/2607.05291)
donne un signal borné — Log-HAR reste très compétitif, le gain TSFM n'est pas
uniforme. D'où un protocole §C strict, sans avantage de structure donné au
challenger.

## Protocole (§C, aligné M17 round-3/4)

| Élément | Choix |
|---|---|
| Cible | moyenne glissante h-jour du log-RV (`rolling(h).mean().shift(-h)`) |
| Horizons | 1, 5, 22 jours (protocole #14768, pas le 1/5/10 des M4/M17) |
| Folds | walk-forward expanding 5 folds, `fold_size = n // 6` (arithmétique `har_model._make_split_indices`) |
| Seeds | {0, 7, 42, 99} — timesfm servi avec `torch.manual_seed(seed)` |
| Débiais | biais constant par fold estimé sur la queue d'entraînement (60 j) SEULE, appliqué symétriquement : `yhat_deb = yhat + bias` (leçon M17 round-3 : signe `+`, jamais `-`) |
| DM | deux jambes (#11010) : conjonction sur `loss_fn="mse"` (perte de précision), jambe `linear` (erreurs signées) = diagnostic de biais, ne jambe jamais le verdict |
| Verdict | `BEATS` ⇔ dm_p_median(mse) < 0,05 ET DM cohérent gagnant sur tous les seeds ET (edge ≥ 2σ cross-seed OU seeds bit-identiques — précédent M17 OLS : déterminisme ⇒ jambe σ dégénérée, pas artificiellement infinie) |
| Métriques | MSE/MAE (log), QLIKE (Patton 2011, échelle RV), biais signé ; TimesFM seul : pinball natif, couverture/largeur 80 % |
| Provenance | repo id + SHA du checkpoint (HfApi), compteur de séries réellement servies, `panel_hash` (fenêtre canonique 360 bars), `bounds_train_test` par fold, hash SHA256 des prévisions par fold (audit bit-identité cross-seed) |
| Garde non-dégénérescence | (#14791) chaque paire de baselines déclarées distinctes doit différer d'au moins `1e-6` en relatif sur AU MOINS un point OOS (`assert_baselines_distinct`, exécuté par `run_config`) — un contrôle qui **peut rougir**, contrairement au hash de prévisions qui ne sépare que bit-identique de non-bit-identique ; séparation la plus faible consignée dans le manifeste (`baseline_weakest_rel_sep`) |

## Modèles

Tous prédisent **la même cible** sur **les mêmes indices de test** :

- **persistence** — dernier log-RV observé (naïf / marche aléatoire).
- **ewma** — moyenne exponentiellement pondérée du log-RV, span choisi sur
  la queue d'entraînement uniquement parmi {5, 10, 20, 60}.
- **log_har** — OLS HAR(1d, 5d, 22d) sur lags log-RV (`har_model.HARModel`,
  spécification log de Corsi 2009), chemin h-étapes itéré, prédiction =
  moyenne du chemin log. Refit tous les 22 jours (fenêtre expanding).
- **har_rv** — même structure OLS sur les **niveaux** de RV (HAR-RV brut),
  **régresseurs décalés d'un pas** (miroir de
  `realized_variance.har_lag_features` ; correctif #14791 : l'alignement
  contemporain d'origine régressait RV_t sur RV_t — fit identité parfait,
  prévision dégénérée en persistence exacte), chemin h-étapes itéré en RV,
  projection sur la cible commune = `log(mean(chemin RV))`. Les deux
  spécifications HAR répondent à l'exigence « HAR et Log-HAR » de l'issue.
- **tsfm** — TimesFM 2.5-200M, contexte = `context_len` (512) derniers
  log-RV, chemin direct multi-horizon (pas de récursion), prédiction =
  moyenne des h premières étapes du chemin médian ; quantiles natifs à
  l'étape h pour l'évaluation pinball/couverture.

### Disposition du tenseur TimesFM (vérifiée empiriquement)

Le dernier axe de la sortie quantiles est **`[mean, q0.1, q0.2, …, q0.9]`**
(10 canaux) — le canal 0 est la tête mean, le quantile i vit en colonne
`1 + i`, et la sortie point == canal 5 == médiane. Le wrapper asserte cette
largeur d'axe à chaque appel (garde anti-dérivation d'API).

### Évaluation quantile vs ponctuelle — deux fonctionnels distincts

Les prévisions ponctuelles ciblent la **moyenne h-jour** du log-RV ; les
quantiles natifs sont évalués sur le log-RV **réalisé à l'étape h** (cible
directe). Les deux sont enregistrés séparément dans le manifeste, jamais
mélangés — comparer le quantile d'une cible moyenne à la cible directe
serait une erreur de fonctionnel.

## Contrat fail-explicit (#14768)

Aucun fallback : si le checkpoint ne charge pas, si la provenance HF échoue,
ou si l'axe quantiles dévie, le script **abort** (exit non nul). Rien ne
peut être rapporté sous l'étiquette TimesFM sans le vrai modèle. Le compteur
`n_tsfm_series_served` atteste le volume réellement servi.

## Données et périmètre

- Panel M-série existant (`har_asymmetric._load_panel`) : BTC (Bitstamp 1h,
  ~2 272 j de RV) et ETH (Binance 1h) en cache local (`--skip-remote`) ;
  les 5 autres coins du panel (yfinance 1h, ~725 j) ne supportent pas
  h=22 avec 5 folds + calibration — exclus du barème §C, même verdict de
  profondeur que M4/M17.
- « Panier diversifié, aucune FAANG/Mag7 » : satisfait structurellement —
  le panel est crypto (BTC + ETH = les deux majeures), aucun titre
  équity n'entre dans l'échantillon.

## Choix de périmètre assumés

- **Chronos-Bolt** : non inclus — l'issue le conditionne à « chargement
  réel attesté » ; il a son propre script d'éval (`eval_chronos_bolt.py`)
  et son cadre (direction-accuracy) diffère du protocole RV/§C. Un grain
  séparé peut l'ajouter en baseline §C si souhaité.
- **PatchTST / iTransformer** : modèles **entraînés** avec leurs propres
  entrées §C (PatchTST `NO BEATS` #14081 sur BTC log-RV débiaisé) ;
  les ré-entraîner dans ce benchmark dupliquerait ces entrées. Le doc les
  cite comme contexte ; la comparaison fraîche ici est TSFM vs baselines
  classiques zero-cost.
- **TimesFM 3.0** : hors périmètre de ce benchmark public — poids sous
  TimesFM Non-Commercial License v1.0 ; pilote privé suivi par #14769
  (qui dépend du présent benchmark).

## Résultats

Run live 2026-09-05 : `google/timesfm-2.5-200m-pytorch` SHA `1d952420fba8`,
43 720 séries servies, 867,5 s GPU (RTX 3090). Manifeste :
`scripts/results/m18_tsfm_benchmark.json`. Les 4 seeds sont
**bit-identiques** (`ident=True` partout — inférence GPU déterministe,
précédent M17 OLS : la jambe σ cross-seed dégénère, elle ne gonfle rien).

### Verdicts §C (conjonction : jambe MSE du DM)

| Coin | h | vs persistence | vs ewma | vs log_har | vs har_rv |
|---|---:|---|---|---|---|
| BTC | 1 | **BEATS** +40,7 % (p<1e-4) | **BEATS** +20,1 % (p<1e-4) | **BEATS** +19,7 % (p<1e-4) | **BEATS** +33,4 % (p<1e-4) |
| BTC | 5 | **BEATS** +56,2 % | INCONCLUSIVE +5,4 % (p=0,116) | **BEATS** +8,5 % (p=0,0015) | **BEATS** +40,1 % (p<1e-4) |
| BTC | 22 | **BEATS** +46,5 % | **BEATS** +10,7 % (p=0,016) | INCONCLUSIVE −4,8 % (p=0,232) | **BEATS** +30,1 % (p=0,0008) |
| ETH | 1 | **BEATS** +30,6 % | **BEATS** +10,5 % | **BEATS** +7,6 % | **BEATS** +29,8 % (p<1e-4) |
| ETH | 5 | **BEATS** +49,7 % | INCONCLUSIVE +4,1 % (p=0,381) | **BEATS** +10,7 % (p=2e-4) | **BEATS** +51,1 % (p<1e-4) |
| ETH | 22 | **BEATS** +47,2 % | **BEATS** +11,9 % (p=0,029) | **BEATS** +12,5 % (p=0,0445) | **BEATS** +45,2 % (p<1e-4) |

La colonne `vs har_rv` est celle du **re-run #14791** (régresseurs décalés,
voir la section dédiée ci-dessous) : les colonnes persistence / ewma /
log_har sont bit-identiques au run initial #14778 (checkpoint SHA inchangé,
inférence GPU déterministe) — seul har_rv a changé.

**Lecture honnête.** Contre la baseline qui compte (Log-HAR) :
**5/6 BEATS, 1/6 INCONCLUSIVE, 0/6 NO BEATS**. Deux réserves explicites :
(i) BTC h=22 : le log-HAR est numériquement meilleur (edge −4,8 %) mais pas
significativement (p=0,23) — INCONCLUSIVE, pas NO BEATS ; (ii) ETH h=22 :
BEATS au bord du seuil (p=0,0445, à peine < 0,05) — fragile, à ne pas
sur-vendre. Le verdict global « TimesFM 2.5 zero-shot bat Log-HAR sur RV
crypto quotidienne aux horizons 1-22 j » tient sur 4 cellules solides
(p ≤ 0,0015), pas sur les deux bordelines.

La littérature citée en tête (TSFM non uniformément supérieur, Log-HAR très
compétitif) est **partiellement confirmée** : Log-HAR résiste au plus long
horizon BTC, l'avantage TSFM est net aux horizons courts/moyens.

### har_rv ≈ persistence : c'était un bug d'alignement, corrigé (#14791)

Le run initial (#14778) rapportait har_rv **numériquement identique à
persistence** (écart relatif 5e-14 à 7e-12 sur les 24 cellules) et la
section précédente de ce document l'attribuait à « l'artefact connu du HAR
en niveaux sur séries persistantes ». Cette explication était fausse :
l'issue #14791 (mesurée par ai-01 en revue de #14778) a établi qu'un accord
à ~13 chiffres significatifs n'est pas une convergence statistique mais
**la même quantité calculée dans un ordre de sommation différent**.

Cause réelle, dans `HarRvModel.fit` : les régresseurs HAR en niveaux étaient
**contemporains** de la cible (`rv_d = RV_t`, `y = RV_t`) — la régression
apprenait l'identité parfaite (coefficient `[0, 1, 0, 0]`, résidu in-sample
~1e-19) et la prévision itérée dégénère en dernière valeur = persistence
exacte. Le contrôle « hashs de prévisions distincts » ne pouvait pas le
voir : deux tableaux différant au 14e chiffre ont des hashs distincts — le
détecteur n'avait aucun pouvoir discriminant sur l'hypothèse « même modèle
effectif » qu'il était censée écarter.

Correctif #14791 : régresseurs **décalés d'un pas** (miroir de
`realized_variance.har_lag_features`, déjà correct pour log_har) + garde
`assert_baselines_distinct` — chaque paire de baselines déclarées
distinctes doit différer d'au moins `1e-6` en relatif sur au moins un point
OOS, sinon le run échoue (un contrôle qui **peut** rougir). Re-run complet
(24 cellules, checkpoint SHA `1d952420fba8` inchangé, 43 720 séries servies,
persistence/ewma/log_har bit-identiques) : `baseline_weakest_rel_sep` entre
**0,11 et 0,18** sur toutes les cellules — cinq ordres de grandeur au-dessus
du seuil. har_rv est désormais une vraie 4e baseline, et le HAR en niveaux
corrigé est **meilleur que persistence** (BTC h=1 : MSE 1,044 vs 1,172) :
l'edge TSFM passe de +40,7 % (doublon persistence) à +33,4 %.

### Calibration quantile native (évaluée à l'étape h)

| Config | couverture 80 % (nominal 0,80) | largeur | pinball q=0,5 |
|---|---|---|---|
| BTC h=1 | 0,814 | 2,053 | 0,313 |
| BTC h=5 | 0,801 | 2,313 | 0,356 |
| BTC h=22 | 0,794 | 2,672 | 0,418 |
| ETH h=1 | 0,806 | 1,971 | 0,307 |
| ETH h=5 | 0,795 | 2,225 | 0,350 |
| ETH h=22 | 0,774 | 2,541 | 0,406 |

Couverture 80 % mesurée entre 0,774 et 0,814 pour un nominal de 0,80 :
**calibration quantile remarquablement honnête zero-shot**, sans aucun
ajustement. La largeur croît avec l'horizon comme attendu (2,0 → 2,7 en
log-RV). Pinball complet par niveau dans le manifeste.

### Biais par fold (extraits, BTC h=1)

`per_fold_bias` (queue d'entraînement, 60 j, signe +) : log_har
[+0,59, +0,21, …], tsfm [+0,34, −0,01, …], persistence [+0,005, −0,020, …].
Le débiais symétrique est appliqué à TOUS les modèles — aucun ne reçoit de
calibration que les autres n'ont pas (leçon M17 round-3).

## Coûts

Non applicables au verdict de forecast pur (aucun claim Sharpe/P&L, aucune
étape économique — hors scope #14768 jusqu'à une étape séparée).

## Reproduction

```bash
python scripts/m18_tsfm_benchmark.py --coins BTC-USD ETH-USD \
    --horizons 1 5 22 --seeds 0 7 42 99 --skip-remote \
    --out-json scripts/results/m18_tsfm_benchmark.json
```

Environnement : `mcp-jupyter-py310` (torch 2.6.0+cu124, timesfm 3.0.1,
checkpoint `google/timesfm-2.5-200m-pytorch` SHA consigné dans le manifeste).
Inférence GPU déterministe (vérifiée : appels répétés bit-identiques) — les
4 seeds servent d'audit de bit-identité, précédent M17 OLS.

## Revalidation cluster 7 actifs — 2026-10-03 (Epic #1454)

### Fix préalable : le harnais produisait un manifeste vide en exit 0

En préparant le run cluster, le harnais s'est révélé cassé depuis la refonte M16 de
`har_asymmetric.py` : `_load_panel` retourne `(panel, failures)` et `main()` assignait le
tuple entier — `coin not in panel` testait l'appartenance au **tuple**, toujours faux,
chaque actif skippé en silence, manifeste écrit avec `n_tsfm_series_served: 0` et exit 0.
Correctif : unpack + `validate_requested_panel` (organe existant) + garde fail-closed
(0 série servie → `SystemExit`). Toute reproduction documentée ci-dessus était donc
silencieusement vide depuis la refonte ; elle fonctionne à nouveau (smoke BTC 2 folds :
6552 séries servies).

### Protocole

Run complet sur RTX 3070 (rôle pionnier du ping-pong GPU #1454) : 7 actifs (BTC, ETH,
SOL, LTC, XRP, ADA, DOT) × horizons {1, 5, 10, 22} × graines {0, 7, 42, 99} —
1462,9 s, 126 368 séries servies, SHA checkpoint inchangé (`1d952420fba8`). Inférence
déterministe bit-identique (graines = contrôles d'audit, jamais des observations —
précédent M17/M18 OLS) ; `n_seeds_effective = 1`.

La couche d'agrégation `scripts/m18_tsfm_cluster.py` (additive — le benchmark lui-même
n'est pas modifié au-delà du fix) applique le protocole de la famille #1454 :

1. **Repli par actif** (règle M16) : BEATS sur majorité stricte d'horizons BEATS, NO
   BEATS dès qu'un horizon est NO BEATS (sans majorité BEATS), sinon INCONCLUSIVE.
2. **Sign-test binomial exact unilatéral** (`alternative="greater"`, n=7 actifs) —
   identique à M16/M12/M17.
3. **Deux vues d'horizons** : `cluster` {1, 5, 10} (comparabilité M4/M15/M16/M17) et
   `protocol` {1, 5, 22} (continuité du claim d'origine #14768).
4. **4 baselines** : persistence, ewma, **log_har** (référence déclarée du protocole
   #14768), har_rv.
5. **Alignement** : contrairement à M4/M15, les deux jambes DM vivent dans **un seul
   walk-forward intra-harnais** — baseline et TimesFM sont scorés sur les mêmes indices
   de fold par construction ; il n'existe pas de jointure cross-harness à mesurer. Le
   manifeste consigne ce fait au lieu de le laisser tacite (leçon M15 : l'alignement se
   déclare, il ne se suppose pas).
6. **Fail-closed** : toutes les lignes summary attendues (un ensemble par
   actif × horizon × graine) doivent exister, chacune `seeds_bit_identical`.

### Résultats mesurés

**Verdict cluster par baseline** (sign-test binomial exact unilatéral, n=7 actifs) :

| Vue | vs persistence | vs ewma | vs **log_har** (référence) | vs har_rv |
|---|---|---|---|---|
| `cluster` {1,5,10} | **BEATS** 7/7, p=0,0078 | NO BEATS 2/7, p=0,9375 | **NO BEATS** 3/7, p=0,7734 | INCONCLUSIVE 5/7, p=0,2266 |
| `protocol` {1,5,22} | **BEATS** 7/7, p=0,0078 | INCONCLUSIVE 4/7, p=0,5000 | **NO BEATS** 3/7, p=0,7734 | INCONCLUSIVE 5/7, p=0,2266 |

**Détail par actif vs log_har** (vue cluster) :

| Actif | Verdict | h=1 | h=5 | h=10 |
|---|---|---|---|---|
| BTC | **BEATS** | BEATS +19,7 % (p≈0) | BEATS +8,5 % (p=0,0015) | INCONCL. +3,3 % |
| ETH | **BEATS** | BEATS +7,6 % (p≈0) | BEATS +10,7 % (p=0,0002) | BEATS +13,0 % (p=0,0029) |
| SOL | **BEATS** | BEATS +9,7 % (p=0,0010) | BEATS +9,3 % (p=0,0281) | INCONCL. +8,5 % |
| LTC | INCONCLUSIVE | BEATS +5,6 % (p=0,0185) | INCONCL. +3,9 % | INCONCL. +1,7 % |
| XRP | INCONCLUSIVE | BEATS +6,1 % (p=0,0227) | INCONCL. +2,3 % | INCONCL. −0,9 % |
| ADA | INCONCLUSIVE | BEATS +7,3 % (p=0,0016) | INCONCL. +7,7 % (p=0,0537) | INCONCL. +6,9 % |
| DOT | INCONCLUSIVE | INCONCL. +3,6 % (p=0,0744) | INCONCL. +2,2 % | INCONCL. +0,7 % |

**Lecture** : (1) le claim #14778 se **reproduit exactement** sur son périmètre — BTC h=1
vs log_har mesure +19,7 % (p≈0), chiffre identique au run original, et ETH reste BEATS
3/3 horizons ; (2) la **généralisation** ne passe pas : à h=1, 6 des 7 actifs battent
log_har (tous sauf DOT) ; à h≥5, l'edge ne se maintient en BEATS que sur BTC, ETH et
**SOL** (+9,27 %, p=0,028 à h=5) — LTC, XRP, ADA et DOT, les quatre actifs yfinance à
historique court (~721 jours horaires contre 2 277 pour BTC), passent en INCONCLUSIVE à
h≥5 sans qu'**aucun horizon ne soit NO BEATS** vs log_har. Le verdict cluster NO BEATS
(3/7, p=0,7734) dit « pas de preuve d'un edge cluster-wide », pas « réfuté partout » ;
il est porté par une perte de puissance sur séries courtes, exactement le profil mesuré
pour M4 (edge confiné aux longues séries).
(3) Contre har_rv, la majorité 5/7 ne suffit pas (p=0,2266) — la baseline HAR recalibrée
reste la référence non battue de la famille, cohérent avec M12/M15/M16/M17.

### Rapport de biais signé (critère §C-7, reprise de la prévalidation c.2026-10-03)

Convention : `signed_bias_debiased` = moyenne des erreurs signées OOS par fold, échelle
log-vol débiaisée ; négatif = sous-estimation. Vue cluster, 7 actifs × h{1,5,10} (n=21
configurations, graine 0 — les graines bit-identiques sont des contrôles).

| Modèle | biais signé moyen | Verdict cluster (tsfm vs lui) |
|---|---:|---|
| har_rv | −0,0278 | INCONCLUSIVE 5/7 (p=0,2266) |
| persistence | −0,0301 | BEATS 7/7 (p=0,0078) |
| ewma | −0,0491 | NO BEATS 2/7 (p=0,9375) |
| **tsfm** | **−0,0522** | — |
| log_har | −0,0686 | NO BEATS 3/7 (p=0,7734) |

Lecture : tsfm est **moins sous-estimateur que log_har** (−0,052 vs −0,069 ;
SOL h=1 : −0,0282 vs −0,0416 ; h=5 : −0,0567 vs −0,0743) mais **plus biaisé que
persistence et har_rv**. En conséquence : (a) le seul BEATS cluster (vs persistence)
n'est **pas** porté par le biais — tsfm y est plus biaisé que la baseline, l'edge vient
de la précision ; (b) vs log_har, l'avantage de biais ne suffit pas à faire passer le
sign-test ; (c) la jambe `linear` (contrôle de biais, #10961 CE1) est INCONCLUSIVE sur
SOL (p=0,40 / 0,38) alors que la jambe MSE y donne BEATS — conformément au protocole,
la conjonction porte sur la perte de précision (MSE), `linear` ne remplace jamais la
jambe principale.

**Conséquence ping-pong GPU (#1454)** : aucun job `[GPU-QUEUE]` ne se justifie pour M18 —
le goulot n'est pas le compute mais la **profondeur de données** (séries hourly >2 ans
pour les cinq actifs distants). Élargir le panel est un problème de sources, pas de GPU.

### Artefacts et reproduction

- Manifeste compact : `scripts/results/m18_tsfm_cluster_aligned.json` (36 301 octets —
  verdicts par vue/baseline/actif, ancres SHA-256 par actif, discipline de graines,
  provenance du checkpoint ; politique #15890).
- Séries complètes hors dépôt :
  `G:\Mon Drive\MyIA\Dev\Trading\ML-Training-Pipeline\m18_tsfm_cluster_full.json`
  (905 349 octets).
- Reproduction :

```bash
python scripts/m18_tsfm_benchmark.py --coins BTC-USD ETH-USD SOL-USD LTC-USD \
    XRP-USD ADA-USD DOT-USD --horizons 1 5 10 22 \
    --out-json <scratchpad>/m18_tsfm_cluster_full.json
python scripts/m18_tsfm_cluster.py --full-json <scratchpad>/m18_tsfm_cluster_full.json \
    --out-json scripts/results/m18_tsfm_cluster_aligned.json
```
