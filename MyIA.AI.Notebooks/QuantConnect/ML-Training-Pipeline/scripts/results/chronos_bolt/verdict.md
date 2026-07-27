# Verdict — Chronos-Bolt zero-shot, panier anti-biais (foundation-model spin-out #8607)

> Script : [`scripts/eval_chronos_bolt.py`](../../eval_chronos_bolt.py) (modèle `amazon/chronos-bolt-base`, ~200M params, T5 encoder-decoder, zero-shot).
> Spin-out de l'Epic #1409 (parqué après L6 NO BEATS) : le track foundation-models du corps originel, jamais exécuté, ressuscité comme rung distinct (#8607).

## Verdict : NO BEATS (panier) — `beats_valid` TLT = artefact de harnais, pas un BEATS

Sur 3 symboles anti-biais à horizon h≈22 (`pred_len=24`, walk-forward 5-fold, 5 seeds, coût tx 10 bps) :

| Symbole | DirAcc | Majority baseline | Edge | `beats_valid` (harnais) | Verdict honnête |
|---------|--------|-------------------|------|-------------------------|-----------------|
| SPY | 0.4957 | 0.5461 | **-0.0505** | False | **NO BEATS** |
| TLT | 0.5217 | 0.5130 | +0.0087 | True | **NO BEATS** (edge dégénéré, voir § ci-dessous) |
| GLD | 0.4609 | 0.5315 | **-0.0706** | False | **NO BEATS** |

2/3 symboles échouent clairement ; le seul « pass » (TLT) est un artefact méthodologique, pas un edge réel.

## Finding critique (C893-L) — le gate multi-seed dégénère en zero-shot

`std_edge = 0.0000` pour **tous** les symboles et **toutes** les seeds, parce que l'inférence
zero-shot de Chronos-Bolt n'a **aucune stochasticité d'entraînement** : le modèle est figé, et
le split walk-forward détermine seul la sortie (mêmes split points ⇒ inférence déterministe ⇒
seeds identiques). Le gate du harnais ([`eval_chronos_bolt.py`](../../eval_chronos_bolt.py):371) :

```python
beats_valid = len(seeds) >= 4 and mean_edge > 0 and (
    std_edge < 1e-10 or mean_edge >= 2 * std_edge
)
```

…collapse en `len(seeds) >= 4 AND mean_edge > 0` quand `std_edge ≈ 0` : **n'importe quel edge
strictement positif valide comme BEATS**. L'edge TLT de +0.0087 (0.87 pt de DirAcc) est donc
**non validé** : il est du bruit d'échantillonnage cross-fenêtre (~23 fenêtres OOS), invisible
aux seeds (qui n'échantillonnent rien en zero-shot). Un test de variance cross-fenêtre propre
(ce que les seeds simulent habituellement) ferait apparaître ce +0.0087 comme non significatif.

De plus, l'edge TLT est **économiquement nul** : +0.87 pt de DirAcc, même si réel, est consommé
par le coût de transaction de 10 bps à chaque rebalancement.

**Leçon durable C893-L** : un gate de robustesse fondé sur la variance cross-seed est
**structurellement inopérant pour les modèles zero-shot** (pas de stochasticité d'entraînement
→ seeds identiques → std=0). La robustesse doit reposer sur la variance **cross-fenêtre** ou
**cross-bootstrap**, pas cross-seed. À coder en dur pour les futurs runs foundation-models :
exiger `std_edge > eps` ET un t-stat cross-fenêtre, sinon `beats_valid=False`.

## Barre pleine (#8607) non atteinte

#8607 exige, après 6 réfutations (L1-L6), une **barre complète sans allègement** :
edge ≥ 2σ cross-seed **ET** ≥3/4 seeds positifs **ET** bat majority-class. Le premier critère
(2σ cross-seed) est structurellement non-prouvable en zero-shot (std=0 dégénéré) ; les 2 autres
sont: panier 1/3 positif (TLT seul, dégénéré), 2/3 sous majority. **Aucun critère robuste
n'est satisfait.** NO BEATS sur le panier.

## Horizons longs h=22/66/132 (#8607 scope)

`#8607` demande h=22/66/132. Sweep complet walk-forward (5-fold, 5 seeds, 10 bps), std=0.0000
partout (zero-shot déterministe, §C893-L) :

| Horizon | SPY DirAcc | SPY majority | SPY edge | TLT DirAcc | TLT majority | TLT edge |
|---------|-----------|--------------|----------|-----------|--------------|----------|
| h≈22 (`pred_len=24`) | 0.4957 | 0.5461 | **-0.0505** | 0.5217 | 0.5130 | +0.0087 ⚠️ |
| h=66 (`pred_len=66`) | 0.5508 | 0.5461 | +0.0046 ⚠️ | 0.4769 | 0.5130 | **-0.0361** |
| h=132 (`pred_len=132`) | 0.4931 | 0.5461 | **-0.0530** | 0.4992 | 0.5130 | **-0.0138** |

(GLD h≈22 : DirAcc 0.4609 vs majority 0.5315, edge **-0.0706** — NO BEATS.)

⚠️ = `beats_valid=True` au harnais, **dégénéré** (std=0 → gate collapse, §C893-L ci-dessus).

**Les 2 seuls edges positifs (+0.0087 TLT h22, +0.0046 SPY h66) s'inversent à l'autre
horizon pour le même symbole** : TLT passe de +0.0087 (h22) à -0.0361 (h66) et -0.0138 (h132) ;
SPY passe de -0.0505 (h22) à +0.0046 (h66) à -0.0530 (h132). **Un edge réel serait consistant
à travers les horizons ; cette inversion de signe est la signature du bruit d'échantillonnage.**
Aucun edge positif n'est ni consistant, ni économiquement significatif (tous < 1 pt de DirAcc,
consommés par les 10 bps de coût tx). **NO BEATS robuste sur les 3 horizons.**

## Implication pour #8607 / #1409

Le paradigme **foundation-model zero-shot** (prévision directe transférée depuis ~100B séries,
sans entraînement sur l'univers) **ne bat pas majority-class** sur le panier anti-biais en
direction — rejoignant L1-L6 (tous NO BEATS sauf L4-DT). Cela **renforce** la conclusion
#1409 : l'alpha sur cet univers provient de **politiques d'action apprises** (L4 Decision
Transformer), pas d'overlays trend, de sizing régime-conditionnel, **ni de prévision
foundation-model zero-shot**.

La comparaison au **M15 LSTM fine-tuned** (BEATS en crypto/vol-forecasting) n'est PAS
apples-to-apples : univers disjoints (ETF vs crypto), cibles disjointes (direction vs
log-realized-vol), horizons disjoints (h=22-132 vs h=1-10), entraînement disjoint (zero-shot
vs fine-tuned). Le verdict #8607 (Chronos bat-il le LSTM spécialisé sur le signal long-horizon ?)
ne peut être tranché que sur un terrain commun — out-of-scope ce cycle.

## Données

- SPY 2515 lignes (2015-2024), TLT/GLD 2765 lignes (2015-2025), yfinance daily close
  (data-source-to-convert AUTORISÉ). `data_utils.load_data` depuis `datasets/yfinance/`.
- Zero-shot : aucun entraînement sur le panier (modèle HF `amazon/chronos-bolt-base` figé,
  cache 784 MB). Device GPU (RTX 3070 8GB, `CUDA_VISIBLE_DEVICES=0`).
- OOS : walk-forward 5-fold, 5 seeds (0/1/7/42/99), coût tx 10 bps.

## Résiduel

- **Kronos** (AAAI 2026, K-lines OHLCV) non exécuté ce cycle : `chronos-forecasting` installé,
  mais Kronos exige un DL modèle séparé + un adaptateur de harnais (`eval_kronos_zeroshot.py`
  existe, pas tourné). Out-of-scope ce cycle ; laisser pour un cycle futur.
- **M15 sur terrain commun** (même univers ETF + cible direction) : out-of-scope ; nécessiterait
  fine-tuner M15 sur ETF-direction.
- **t-stat cross-fenêtre propre** : le harnais actuel ne le calcule pas (seeds dégénérés) ;
 amélioration méthodologique proposée (C893-L) non codée ce cycle.
