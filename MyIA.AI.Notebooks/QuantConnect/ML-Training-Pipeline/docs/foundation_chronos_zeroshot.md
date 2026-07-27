# Foundation-model zero-shot — Chronos-Bolt sur le panier anti-biais (spin-out #8607 du ladder #1409)

> Script associé : [`scripts/eval_chronos_bolt.py`](../scripts/eval_chronos_bolt.py) (+ [`scripts/eval_kronos_zeroshot.py`](../scripts/eval_kronos_zeroshot.py), non exécuté ce cycle).
> Résultats bruts : [`scripts/results/chronos_bolt/`](../scripts/results/chronos_bolt/) (JSON par symbole × horizon + `verdict.md`).
> Spin-out de l'Epic #1409 (parqué après L6 ROBUST NO BEATS) : le track **foundation-models** du corps originel de l'Epic, jamais exécuté, ressuscité comme rung distinct.

## Verdict : NO BEATS (panier, robuste sur 3 horizons)

Un **foundation-model zero-shot** (Amazon Chronos-Bolt-base, ~200M params, pré-entraîné sur
~100B séries, *aucun* entraînement sur l'univers) **ne bat pas majority-class** sur le panier
anti-biais en prévision de **direction**, à aucun des 3 horizons demandés par #8607
(h=22/66/132). La grille théorique est 3 symboles × 3 horizons = 9, mais **seules 7
configurations ont été effectivement exécutées** (GLD n'a été évalué qu'à h≈22 ; SPY et TLT
aux 3 horizons). Sur ces 7, **aucune** ne produit un edge à la fois positif, **consistant à
travers les horizons**, et économiquement significatif (5 à edge strictement négatif, 2
positives dégénérées ; toutes < 1 pt de DirAcc, consommés par le coût de transaction de 10 bps).

## Hypothèse (#8607)

L1-L6 du Curriculum V3 sont tous NO BEATS (overlays *trend* / *regime-sizing* sur allocation
*risk-based*), à l'exception de **L4 (Decision Transformer)** — le seul échelon BEATS, qui
apprend une **politique d'action** plutôt qu'une prévision de retour. Un **foundation-model
zero-shot** est un **troisième paradigme** : pas d'entraînement sur l'univers, pas d'overlay,
prévision directe transférée depuis un pré-entraînement massif. La question de #8607 : un tel
modèle bat-il majority-class sur le panier anti-biais en direction, aux **horizons longs**
(h=22/66/132) ? Biais de fouille après 6 réfutations (L1-L6) → **barre complète sans
allègement** : edge ≥ 2σ cross-seed, ≥3/4 seeds positifs, bat majority-class, coûts tx.

## Méthode

- **Modèle** : Amazon **Chronos-Bolt-base** (`amazon/chronos-bolt-base`, ~200M params,
  architecture T5 encoder-decoder, tokenisation des valeurs continues) en mode **zero-shot**
  (modèle figé, *aucun* fine-tuning sur le panier). 250× plus rapide que le Chronos original.
  Cache HF 784 MB. Via `chronos-forecasting` 2.3.1 (`BaseChronosPipeline`).
- **Inférence** : `prediction_length` ∈ {24, 66, 132} (≈ h=22, 66, 132 jours de bourse),
  contexte `seq_len=96`. Device GPU (RTX 3070 8GB, `CUDA_VISIBLE_DEVICES=0`, env
  `coursia-ml-training`, torch 2.5.1+cu121).
- **Univers** : panier anti-biais (FORBIDDEN FAANG/Mag7) — SPY, TLT, GLD via
  [`data_utils.load_data`](../scripts/data_utils.py) (yfinance daily, data-source-to-convert
  AUTORISÉ). SPY 2015-2024 (2515 lignes), TLT/GLD 2015-2025 (2765 lignes).
- **Validation** : walk-forward **5-fold**, **5 seeds** (0/1/7/42/99), coût de transaction
  **10 bps** par rebalancement, baseline majority-class (`max(up_frac, down_frac)`,
  [`compute_majority_baseline`](../scripts/eval_kronos_zeroshot.py)).
- **Métrique** : `edge_vs_majority = DirAcc − majority_baseline`. Gate `beats_valid` du harnais
  ([`eval_chronos_bolt.py:371`](../scripts/eval_chronos_bolt.py)) : `len(seeds)≥4 AND
  mean_edge>0 AND (std_edge<1e-10 OR mean_edge≥2·std_edge)`.

## Résultats — sweep horizon × symbole (walk-forward 5-fold, 5 seeds, 10 bps)

| Horizon | SPY DirAcc | SPY majority | SPY edge | TLT DirAcc | TLT majority | TLT edge | GLD edge (h≈22) |
|---------|-----------|--------------|----------|-----------|--------------|----------|-----------------|
| h≈22 (`pred_len=24`) | 0.4957 | 0.5461 | **-0.0505** | 0.5217 | 0.5130 | +0.0087 ⚠️ | **-0.0706** |
| h=66 (`pred_len=66`) | 0.5508 | 0.5461 | +0.0046 ⚠️ | 0.4769 | 0.5130 | **-0.0361** | — |
| h=132 (`pred_len=132`) | 0.4931 | 0.5461 | **-0.0530** | 0.4992 | 0.5130 | **-0.0138** | — |

⚠️ = `beats_valid=True` au harnais, mais **dégénéré** (voir Finding 1).

`std_edge = 0.0000` pour **tous** les symboles, **tous** les horizons, **toutes** les seeds.

## Findings clés

1. **Le gate multi-seed dégénère en zero-shot (C893-L).** `std_edge = 0.0000` partout parce que
   l'inférence zero-shot de Chronos-Bolt n'a **aucune stochasticité d'entraînement** : le modèle
   est figé, et le split walk-forward détermine seul la sortie (mêmes split points ⇒ inférence
   déterministe ⇒ seeds identiques). Le gate `beats_valid` ([`eval_chronos_bolt.py:371`](../scripts/eval_chronos_bolt.py))
   collapse alors en « n'importe quel edge > 0 = BEATS »,
   via la branche `std_edge < 1e-10`. **Leçon durable** : un gate de robustesse fondé sur la
   variance cross-seed est **structurellement inopérant pour les modèles zero-shot**. La
   robustesse doit reposer sur la variance **cross-fenêtre** ou **cross-bootstrap**, pas
   cross-seed. Amélioration proposée : exiger `std_edge > eps` ET un t-stat cross-fenêtre.

2. **Les 2 seuls edges positifs s'inversent à l'autre horizon = signature du bruit.** TLT passe
   de +0.0087 (h≈22) à -0.0361 (h=66) à -0.0138 (h=132). SPY passe de -0.0505 (h≈22) à +0.0046
   (h=66) à -0.0530 (h=132). Un edge réel serait **consistant à travers les horizons** ; cette
   inversion de signe est la signature d'un bruit d'échantillonnage cross-fenêtre, pas d'un
   signal prédictif. Aucun edge positif n'est ni consistant, ni économiquement significatif.

3. **Aucune configuration ne bat majority-class de façon robuste.** Sur les **7 configurations
   exécutées** (la grille 3×3 en compte 9 ; GLD n'a été évalué qu'à h≈22), 5 ont un edge
   strictement négatif, et les 2 positives (TLT h≈22, SPY h=66) sont dégénérées (Finding 1) +
   inversées (Finding 2). La barre pleine de #8607 (edge ≥2σ cross-seed **ET** ≥3/4 seeds
   positifs **ET** bat majority) n'est satisfaite par **aucune** configuration.

4. **Le coût de transaction achève l'edge résiduel.** Même en supposant les edges positifs
   réels (< 1 pt de DirAcc), le coût de 10 bps par rebalancement les consomme intégralement.
   La prévision de direction zero-shot n'a pas la précision nécessaire pour couvrir le
   turnover sur cet univers liquide (ETF).

## Comparaison au M15 LSTM fine-tuned (KEEPER Gate V2) — cadrage honnête

La comparaison *foundation-zero-shot* vs *M15-fine-tuned* n'est **pas apples-to-apples** :

| Axe | M15 LSTM (BEATS) | Chronos-Bolt (ce cycle) |
|-----|------------------|-------------------------|
| Univers | Crypto (7 coins BTC/ETH/SOL/LTC/XRP/ADA/DOT) | ETF anti-biais (SPY/TLT/GLD) |
| Cible | Volatilité réalisée (log-RV) | Direction (DirAcc) |
| Horizon | h=1/5/10 (court) | h=22/66/132 (long) |
| Entraînement | Fine-tuned (~4.8K params, walk-forward refit) | Zero-shot (aucune donnée du panier) |

Le verdict de #8607 (« Chronos bat-il le LSTM spécialisé sur le signal long-horizon ? ») ne
peut donc être tranché que sur un **terrain commun** (même univers + même cible + même
horizon). Ce cycle établit le baseline zero-shot sur **ETF-direction-long-horizon** (référence
future) ; une comparaison directe nécessiterait M15 fine-tuné sur le même univers+cible
(**out-of-scope ce cycle**).

## Implication pour #8607 / #1409

Le paradigme **foundation-model zero-shot** **ne bat pas majority-class** sur le panier
anti-biais en direction — rejoignant L1-L6 (tous NO BEATS sauf L4-DT). Cela **renforce** la
conclusion centrale de l'Epic #1409 : **l'alpha sur cet univers provient de politiques d'action
apprises** (L4 Decision Transformer), **pas** d'overlays *trend*, de *sizing* régime-conditionnel,
**ni de prévision foundation-model zero-shot**.

Trois paradigmes testés, un seul BEATS (action-based) : la prévision de retour/direction — qu'elle
vienne d'un overlay artisanal (L1-L3, L5) ou d'un foundation-model de 200M params pré-entraîné
sur 100B séries (ce rung) — ne produit pas d'edge robuste après coûts sur cet univers.

`See #8607`. `See #1409` (Epic parqué ; ce rung foundation-models en confirme la conclusion).

## Résiduel

- **Kronos** (AAAI 2026, pré-entraîné sur 12B K-lines OHLCV) non exécuté ce cycle :
  `chronos-forecasting` installé, mais Kronos exige un DL modèle séparé + adaptateur de harnais
  ([`eval_kronos_zeroshot.py`](../scripts/eval_kronos_zeroshot.py) existe, pas tourné). Comparaison
  cross-foundation-model laissée pour un cycle futur.
- **M15 sur terrain commun** : fine-tuner M15 sur ETF-direction-long-horizon pour une comparaison
  directe — out-of-scope, multi-cycle.
- **t-stat cross-fenêtre propre** : le harnais actuel ne le calcule pas (seeds dégénérés en
  zero-shot, Finding 1) ; amélioration méthodologique (C893-L) non codée ce cycle.

## Références

- Chronos: Learning the Language of Time Series (Ansari et al., Rasul et al., 2024) — T5-based.
- Chronos-Bolt: Amazon Science, 2025 — 250× plus rapide, tokenisation continue.
- Kronos (AAAI 2026) — shiyu-coder/Kronos, K-lines OHLCV.
- M15 LSTM (KEEPER Gate V2) : [`docs/M15_LSTM_RV.md`](M15_LSTM_RV.md) (crypto, vol-forecasting).
- L4 Decision Transformer (seul BEATS du ladder) : [`docs/L4_decision_transformer.md`](L4_decision_transformer.md).
- L6 HMM regime-sizing (dernier rung NO BEATS avant spin-out) : [`docs/L6_hmm_regime_sizing.md`](L6_hmm_regime_sizing.md).
- Spin-out : issue #8607. Epic parent parqué : #1409.
