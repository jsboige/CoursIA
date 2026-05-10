# M8 SOTA Sweep Verdict (vs Majority Class Baseline)

**Setup:** 4 models x 2 coins x 3 horizons x 4 seeds = 96 runs, seq_len=60, epochs=250, GPU2 (RTX 4090, PCIe x4)

**Verdict criterion:** edge_over_majority cross-seed >= 2*std (BEATS) or <= -2*std (NO BEATS), otherwise INCONCLUSIVE.

**HAR baseline comparison TODO** — driver intended HAR_mse but per-seed metadata only has majority_class baseline.

| Model | Coin | h | n_seeds | MSE mean+/-std | DirAcc mean+/-std | Edge mean+/-std | Verdict |
|-------|------|---|---------|----------------|-------------------|-----------------|---------|
| tft | BTC_USD | 1 | 1 | 0.000540+/-0.000000 | 0.4833+/-0.0000 | -0.0243+/-0.0000 | **SINGLE_SEED** |
| tft | BTC_USD | 5 | 1 | 0.000545+/-0.000000 | 0.5228+/-0.0000 | +0.0152+/-0.0000 | **SINGLE_SEED** |
| tft | BTC_USD | 10 | 1 | 0.000584+/-0.000000 | 0.5061+/-0.0000 | -0.0061+/-0.0000 | **SINGLE_SEED** |
| tft | ETH_USD | 1 | 1 | 0.001356+/-0.000000 | 0.4985+/-0.0000 | -0.0061+/-0.0000 | **SINGLE_SEED** |
| tft | ETH_USD | 5 | 2 | 0.001405+/-0.000000 | 0.4833+/-0.0000 | -0.0243+/-0.0000 | **SINGLE_SEED** |
| tft | ETH_USD | 10 | 2 | 0.001451+/-0.000000 | 0.4787+/-0.0000 | -0.0243+/-0.0000 | **SINGLE_SEED** |
| mamba | BTC_USD | 1 | 4 | 0.000563+/-0.000024 | 0.4886+/-0.0052 | -0.0190+/-0.0052 | **NO BEATS** |
| mamba | BTC_USD | 5 | 4 | 0.000584+/-0.000020 | 0.5000+/-0.0201 | -0.0076+/-0.0201 | **INCONCLUSIVE** |
| mamba | BTC_USD | 10 | 4 | 0.000615+/-0.000045 | 0.5008+/-0.0063 | -0.0114+/-0.0063 | **INCONCLUSIVE** |
| mamba | ETH_USD | 1 | 4 | 0.001343+/-0.000005 | 0.4909+/-0.0101 | -0.0137+/-0.0101 | **INCONCLUSIVE** |
| mamba | ETH_USD | 5 | 4 | 0.001446+/-0.000051 | 0.5030+/-0.0146 | -0.0046+/-0.0146 | **INCONCLUSIVE** |
| mamba | ETH_USD | 10 | 4 | 0.001495+/-0.000066 | 0.4855+/-0.0169 | -0.0175+/-0.0169 | **INCONCLUSIVE** |
| itransformer | BTC_USD | 1 | 4 | 0.000534+/-0.000011 | 0.5008+/-0.0146 | -0.0069+/-0.0146 | **INCONCLUSIVE** |
| itransformer | BTC_USD | 5 | 4 | 0.000595+/-0.000034 | 0.5053+/-0.0201 | -0.0041+/-0.0201 | **INCONCLUSIVE** |
| itransformer | BTC_USD | 10 | 4 | 0.000572+/-0.000022 | 0.5015+/-0.0113 | -0.0076+/-0.0113 | **INCONCLUSIVE** |
| itransformer | ETH_USD | 1 | 4 | 0.001320+/-0.000015 | 0.5023+/-0.0175 | -0.0023+/-0.0175 | **INCONCLUSIVE** |
| itransformer | ETH_USD | 5 | 4 | 0.001496+/-0.000092 | 0.5076+/-0.0293 | +0.0030+/-0.0293 | **INCONCLUSIVE** |
| itransformer | ETH_USD | 10 | 4 | 0.001437+/-0.000029 | 0.4924+/-0.0091 | -0.0125+/-0.0091 | **INCONCLUSIVE** |
| patchtst | BTC_USD | 1 | 4 | 0.000523+/-0.000005 | 0.4886+/-0.0225 | -0.0190+/-0.0225 | **INCONCLUSIVE** |
| patchtst | BTC_USD | 5 | 4 | 0.000576+/-0.000019 | 0.5160+/-0.0280 | +0.0084+/-0.0280 | **INCONCLUSIVE** |
| patchtst | BTC_USD | 10 | 4 | 0.000556+/-0.000008 | 0.5221+/-0.0171 | +0.0099+/-0.0171 | **INCONCLUSIVE** |
| patchtst | ETH_USD | 1 | 4 | 0.001336+/-0.000014 | 0.5099+/-0.0115 | +0.0053+/-0.0115 | **INCONCLUSIVE** |
| patchtst | ETH_USD | 5 | 4 | 0.001452+/-0.000027 | 0.4924+/-0.0163 | -0.0152+/-0.0163 | **INCONCLUSIVE** |
| patchtst | ETH_USD | 10 | 4 | 0.001420+/-0.000009 | 0.4840+/-0.0084 | -0.0190+/-0.0084 | **NO BEATS** |

## Summary
- BEATS: 0
- NO BEATS: 2
- INCONCLUSIVE: 16
- SINGLE_SEED: 6
- NO_DATA: 0

## Cross-model BEATS pattern
(How many BEATS verdicts each model has across 6 combos)

- **tft**: 0 BEATS / 0 INCONCLUSIVE / 0 NO BEATS
- **mamba**: 0 BEATS / 5 INCONCLUSIVE / 1 NO BEATS
- **itransformer**: 0 BEATS / 6 INCONCLUSIVE / 0 NO BEATS
- **patchtst**: 0 BEATS / 5 INCONCLUSIVE / 1 NO BEATS
