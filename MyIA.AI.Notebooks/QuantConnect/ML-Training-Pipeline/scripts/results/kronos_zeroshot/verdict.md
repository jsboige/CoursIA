# Verdict — Kronos zero-shot, panier anti-biais (foundation-model spin-out #8607, 2e rung)

> Script : [`scripts/eval_kronos_zeroshot.py`](../../eval_kronos_zeroshot.py) (modèle `NeoQuasar/Kronos-base`, ~102M params, AAAI 2026, pré-entraîné sur 12B K-lines OHLCV, zero-shot).
> 2e rung foundation-model du spin-out #8607 de l'Epic #1409 (parqué après L6 NO BEATS). Le 1er rung était Chronos-Bolt (c.893, See #8610).

## Verdict : NO BEATS (panier, robuste sur 3 horizons)

Sur 3 symboles anti-biais × 3 horizons = **9 configurations**, walk-forward 5 fenêtres, 5 seeds (0/1/7/42/99), coût tx 10 bps : **aucune** configuration ne bat majority-class. **9/9 mean_edge strictement négatifs**, `beats_valid=False` partout. DirAcc (0.4885-0.5113) **sous** la baseline majority (0.5130-0.5461) sur les 9 configs.

| Symbole | Horizon | DirAcc | Majority | Edge | std_edge | `beats_valid` |
|---------|---------|--------|----------|------|----------|---------------|
| SPY | h≈22 (`pred_len=24`) | 0.5113 | 0.5461 | **-0.0348** | 0.0502 | False |
| SPY | h=66 | 0.5058 | 0.5461 | **-0.0403** | 0.0228 | False |
| SPY | h=132 | 0.5014 | 0.5461 | **-0.0448** | 0.0230 | False |
| TLT | h≈22 | 0.4957 | 0.5130 | **-0.0174** | 0.0286 | False |
| TLT | h=66 | 0.4929 | 0.5130 | **-0.0201** | 0.0086 | False |
| TLT | h=132 | 0.4885 | 0.5130 | **-0.0245** | 0.0104 | False |
| GLD | h≈22 | 0.4887 | 0.5315 | **-0.0428** | 0.0266 | False |
| GLD | h=66 | 0.5095 | 0.5315 | **-0.0219** | 0.0297 | False |
| GLD | h=132 | 0.5066 | 0.5315 | **-0.0249** | 0.0161 | False |

`std_edge` est **strictement positif** sur les 9 configs (0.0086 à 0.0502) — voir § ci-dessous (C893-L distinction).

## Le harness était BROKEN/spéculatif — réécrit sur l'API réelle

`eval_kronos_zeroshot.py` n'avait **jamais été exécuté** : il appelait `from kronos import KronosPipeline` + `KronosPipeline.from_pretrained(model_id, device_map=)` — une API **qui n'existe pas**. Kronos n'a pas de wheel PyPI (`kronos-forecasting` absent de PyPI) ; c'est un repo source (`github.com/shiyu-coder/Kronos`). API réelle (groundée firsthand via `model/__init__.py` + `examples/prediction_example.py`) :

- Import : `from model import Kronos, KronosTokenizer, KronosPredictor` (package `model/` du repo, sur `sys.path` — le harness clone le repo si absent).
- Chargement : `KronosTokenizer.from_pretrained("NeoQuasar/Kronos-Tokenizer-base")` + `Kronos.from_pretrained("NeoQuasar/Kronos-base")` + `KronosPredictor(model, tokenizer, max_context=512)`.
- Inférence : `predictor.predict(df=OHLCV, x_timestamp, y_timestamp, pred_len, T, top_p, sample_count)` → DataFrame de forecast (colonne `close` extraite).
- IDs réels `NeoQuasar/Kronos-{mini,small,base}` (Kronos-large ~499M **non open-source** → absent). Défaut `base` (102M, comparable à Chronos-Bolt-base ~200M).

Réécriture complète du wrapper + window-builder (OHLCV + timestamps) + evaluate + ajout `run_multi_seed`/`run_sweep`. **SOTA-OK** : `is_mock=False`, vrai forward pass GPU.

## Distinction critique vs Chronos — C893-L ne s'applique PAS (vérifié firsthand)

**C893-L (Chronos-Bolt, c.893)** : le décodeur Chronos-Bolt est **déterministe** → `std_edge=0.0000` toutes seeds identiques → le gate `beats_valid = seeds≥4 AND edge>0 AND (std<1e-10 OR edge≥2·std)` **collapse** en « n'importe quel edge>0=BEATS » via la branche `std<1e-10`.

**Kronos est l'inverse** : les forecasts sont produits par **échantillonnage autorégressif** (`T=1.0, top_p=0.9, sample_count=1`) → la forward pass est **stochastique** → les 5 seeds produisent des forecasts **différents** → `std_edge > 0` (mesuré : 0.0086 à 0.0502 sur les 9 configs). Le seed (`torch.manual_seed` + `np.random.seed` avant chaque `predict`) contrôle explicitement cet échantillonnage.

**Conséquence** : pour Kronos, le gate multi-seed est un **vrai test** de robustesse, pas un artefact dégénéré. Les 2 `beats_valid=True` « dégénérés » de Chronos (TLT h22, SPY h66) n'ont pas d'équivalent ici — Kronos produit un négatif **uniforme** (9/9), plus propre, précisément parce que la variance cross-seed ne s'effondre pas.

## Barre pleine #8607 non atteinte

#8607 exige, après 6 réfutations (L1-L6), une barre complète : edge ≥2σ cross-seed **ET** ≥3/4 seeds positifs **ET** bat majority-class. Kronos : 9/9 mean_edge négatifs, 0/9 avec ≥3/5 seeds positifs (max 2/5 sur SPY h22), DirAcc sous majority partout. **Aucun critère satisfait.** NO BEATS robuste.

## Comparaison Chronos-Bolt (1er rung) vs Kronos (ce rung)

| Axe | Chronos-Bolt-base (~200M) | Kronos-base (~102M) |
|-----|---------------------------|---------------------|
| Pré-entraînement | ~100B séries temporelles (langage des TS) | 12B K-lines OHLCV multi-actifs |
| Décodage | **Déterministe** (Bolt) | **Stochastique** (échantillonnage AR) |
| `std_edge` cross-seed | **0.0000** partout (dégénéré, C893-L) | **0.0086-0.0502** (variance réelle) |
| Configs exécutées | 7 (GLD h22 only) | **9 (grille 3×3 complète)** |
| Edges positifs | 2 (dégénérés, artefact harnais) | **0** (négatif uniforme) |
| Verdict panier | NO BEATS | **NO BEATS** (plus propre) |

Les **deux** foundation-models zero-shot (langage des TS **et** K-lines OHLCV) échouent à battre majority-class sur le panier anti-biais en direction, aux horizons longs, après coûts. Renforce #1409 : l'alpha sur cet univers provient de **politiques d'action apprises** (L4 Decision Transformer), pas de prévision foundation-model.

## Données

- SPY 2515 bars (2015-2024), TLT/GLD 2765 bars (2015-2025), yfinance daily OHLCV (data-source-to-convert AUTORISÉ). `data_utils.load_data` depuis `datasets/yfinance/` (gitignored).
- Zero-shot : aucun entraînement sur le panier (modèle HF `NeoQuasar/Kronos-base` figé, cache 391 MB + tokenizer). Device GPU (RTX 3070 8GB, `CUDA_VISIBLE_DEVICES=0`, env `coursia-ml-training` torch 2.5.1+cu121).
- OOS : walk-forward 5 fenêtres, 5 seeds (0/1/7/42/99), coût tx 10 bps.

## Résiduel (out-of-scope, multi-cycle)

- **M15 sur terrain commun** (ETF-direction-long-horizon) : fine-tuner M15 pour comparaison directe Chronos vs Kronos vs M15 — multi-cycle.
- **t-stat cross-fenêtre propre** : le gate actuel utilise std cross-seed (significatif pour Kronos, contrairement à Chronos), mais un t-stat cross-fenêtre formaliserait la significativité OOS — amélioration méthodologique non codée ce cycle.
- **Kronos-large** (499M) : non open-source, inaccessible.
