# DM Test Retroactif -- Cycle 28 Track A

**Status:** COMPLETE

## Methodology

- Diebold-Mariano test on MSE loss differential (M3/M3b/M4/M5 vs HAR classic baseline)
- M9 TFT: binomial test on direction accuracy vs majority-class baseline
- Re-classification thresholds: BEATS p<0.05 (strict), BEATS p<0.10 (marginal), INCONCLUSIVE
- Cross-seed sign-test: binomial H0:p=0.5 on per-seed BEATS counts

## Per-combo results

| Model | Coin | h | Runs | Beats | Mean p | Sign-test p | MSE red% | Verdict |
|-------|------|---|------|-------|--------|-------------|----------|---------|
| M3_HAR_classic | ADA-USD | 1 | 1 | 1/1 | 0.011313 | 0.5000 | 48.4% | **BEATS_p005** |
| M3_HAR_classic | ADA-USD | 5 | 1 | 1/1 | 0.042922 | 0.5000 | 56.1% | **BEATS_p005** |
| M3_HAR_classic | ADA-USD | 10 | 1 | 0/1 | 0.067727 | 1.0000 | 56.6% | **BEATS_p010** |
| M3_HAR_classic | BTC-USD | 1 | 1 | 1/1 | 0.000000 | 0.5000 | 48.7% | **BEATS_p005** |
| M3_HAR_classic | BTC-USD | 5 | 1 | 1/1 | 0.001790 | 0.5000 | 62.4% | **BEATS_p005** |
| M3_HAR_classic | BTC-USD | 10 | 1 | 0/1 | 0.194182 | 1.0000 | 60.3% | **INCONCLUSIVE** |
| M3_HAR_classic | DOT-USD | 1 | 1 | 0/1 | 0.112160 | 1.0000 | 37.7% | **INCONCLUSIVE** |
| M3_HAR_classic | DOT-USD | 5 | 1 | 0/1 | 0.796634 | 1.0000 | 41.8% | **INCONCLUSIVE** |
| M3_HAR_classic | DOT-USD | 10 | 1 | 0/1 | 0.876081 | 1.0000 | 36.4% | **INCONCLUSIVE** |
| M3_HAR_classic | ETH-USD | 1 | 1 | 1/1 | 0.000000 | 0.5000 | 52.7% | **BEATS_p005** |
| M3_HAR_classic | ETH-USD | 5 | 1 | 1/1 | 0.000000 | 0.5000 | 66.5% | **BEATS_p005** |
| M3_HAR_classic | ETH-USD | 10 | 1 | 1/1 | 0.000244 | 0.5000 | 66.1% | **BEATS_p005** |
| M3_HAR_classic | LTC-USD | 1 | 1 | 1/1 | 0.013168 | 0.5000 | 43.3% | **BEATS_p005** |
| M3_HAR_classic | LTC-USD | 5 | 1 | 0/1 | 0.286260 | 1.0000 | 50.5% | **INCONCLUSIVE** |
| M3_HAR_classic | LTC-USD | 10 | 1 | 0/1 | 0.421759 | 1.0000 | 49.5% | **INCONCLUSIVE** |
| M3_HAR_classic | SOL-USD | 1 | 1 | 1/1 | 0.000267 | 0.5000 | 34.3% | **BEATS_p005** |
| M3_HAR_classic | SOL-USD | 5 | 1 | 1/1 | 0.002347 | 0.5000 | 46.0% | **BEATS_p005** |
| M3_HAR_classic | SOL-USD | 10 | 1 | 1/1 | 0.005476 | 0.5000 | 46.0% | **BEATS_p005** |
| M3_HAR_classic | XRP-USD | 1 | 1 | 1/1 | 0.001180 | 0.5000 | 42.3% | **BEATS_p005** |
| M3_HAR_classic | XRP-USD | 5 | 1 | 0/1 | 0.181190 | 1.0000 | 48.2% | **INCONCLUSIVE** |
| M3_HAR_classic | XRP-USD | 10 | 1 | 0/1 | 0.724475 | 1.0000 | 43.8% | **INCONCLUSIVE** |
| M3b_HAR_asymmetric | BTC-USD | 1 | 4 | 4/4 | 0.000066 | 0.0625 | 5.1% | **BEATS_p005** |
| M3b_HAR_asymmetric | BTC-USD | 5 | 4 | 4/4 | 0.000006 | 0.0625 | 23.6% | **BEATS_p005** |
| M3b_HAR_asymmetric | BTC-USD | 10 | 4 | 4/4 | 0.000001 | 0.0625 | 36.7% | **BEATS_p005** |
| M3b_HAR_asymmetric | ETH-USD | 1 | 4 | 0/4 | 0.607131 | 1.0000 | -0.6% | **INCONCLUSIVE** |
| M3b_HAR_asymmetric | ETH-USD | 5 | 4 | 0/4 | 0.951735 | 1.0000 | 0.3% | **INCONCLUSIVE** |
| M3b_HAR_asymmetric | ETH-USD | 10 | 4 | 0/4 | 0.915098 | 1.0000 | -0.9% | **INCONCLUSIVE** |
| M4_DLinear | ADA-USD | 1 | 4 | 3/4 | 0.049756 | 0.3125 | 5.3% | **BEATS_p005** |
| M4_DLinear | ADA-USD | 5 | 4 | 0/4 | 0.206132 | 1.0000 | 7.7% | **INCONCLUSIVE** |
| M4_DLinear | ADA-USD | 10 | 4 | 0/4 | 0.893847 | 1.0000 | 0.9% | **INCONCLUSIVE** |
| M4_DLinear | BTC-USD | 1 | 4 | 4/4 | 0.000000 | 0.0625 | 15.3% | **BEATS_p005** |
| M4_DLinear | BTC-USD | 5 | 4 | 4/4 | 0.000000 | 0.0625 | 28.3% | **BEATS_p005** |
| M4_DLinear | BTC-USD | 10 | 4 | 4/4 | 0.000000 | 0.0625 | 38.3% | **BEATS_p005** |
| M4_DLinear | DOT-USD | 1 | 4 | 0/4 | 0.140735 | 1.0000 | 3.2% | **INCONCLUSIVE** |
| M4_DLinear | DOT-USD | 5 | 4 | 0/4 | 0.930802 | 1.0000 | 0.3% | **INCONCLUSIVE** |
| M4_DLinear | DOT-USD | 10 | 4 | 0/4 | 0.921947 | 1.0000 | -0.7% | **INCONCLUSIVE** |
| M4_DLinear | ETH-USD | 1 | 4 | 4/4 | 0.035979 | 0.0625 | 3.3% | **BEATS_p005** |
| M4_DLinear | ETH-USD | 5 | 4 | 0/4 | 0.284667 | 1.0000 | 3.9% | **INCONCLUSIVE** |
| M4_DLinear | ETH-USD | 10 | 4 | 0/4 | 0.315930 | 1.0000 | 6.0% | **INCONCLUSIVE** |
| M4_DLinear | LTC-USD | 1 | 4 | 2/4 | 0.086157 | 0.6875 | 4.7% | **BEATS_p010** |
| M4_DLinear | LTC-USD | 5 | 4 | 0/4 | 0.100083 | 1.0000 | 9.1% | **INCONCLUSIVE** |
| M4_DLinear | LTC-USD | 10 | 4 | 0/4 | 0.235653 | 1.0000 | 8.9% | **INCONCLUSIVE** |
| M4_DLinear | SOL-USD | 1 | 4 | 4/4 | 0.001003 | 0.0625 | 9.8% | **BEATS_p005** |
| M4_DLinear | SOL-USD | 5 | 4 | 0/4 | 0.220825 | 1.0000 | 4.4% | **INCONCLUSIVE** |
| M4_DLinear | SOL-USD | 10 | 4 | 0/4 | 0.678655 | 1.0000 | 2.2% | **INCONCLUSIVE** |
| M4_DLinear | XRP-USD | 1 | 4 | 0/4 | 0.669727 | 1.0000 | -0.2% | **INCONCLUSIVE** |
| M4_DLinear | XRP-USD | 5 | 4 | 0/4 | 0.352673 | 1.0000 | 4.8% | **INCONCLUSIVE** |
| M4_DLinear | XRP-USD | 10 | 4 | 0/4 | 0.614544 | 1.0000 | 3.6% | **INCONCLUSIVE** |
| M5_HMM_regime | BTC-USD | 1 | 4 | 3/4 | 0.164619 | 0.3125 | 7.0% | **INCONCLUSIVE** |
| M5_HMM_regime | BTC-USD | 5 | 4 | 0/4 | 0.112928 | 1.0000 | -11.1% | **INCONCLUSIVE** |
| M5_HMM_regime | BTC-USD | 10 | 4 | 0/4 | 0.016261 | 1.0000 | -28.3% | **BEATEN_p005** |
| M5_HMM_regime | ETH-USD | 1 | 4 | 4/4 | 0.001075 | 0.0625 | 9.6% | **BEATS_p005** |
| M5_HMM_regime | ETH-USD | 5 | 4 | 0/4 | 0.018525 | 1.0000 | -17.9% | **BEATEN_p005** |
| M5_HMM_regime | ETH-USD | 10 | 4 | 0/4 | 0.000510 | 1.0000 | -53.0% | **BEATEN_p005** |
| M9_TFT | BTC-USD | 1 | 16 | 5/16 | 0.668774 | 0.9616 | N/A | **INCONCLUSIVE** |
| M9_TFT | BTC-USD | 5 | 16 | 6/16 | 0.610663 | 0.8949 | N/A | **INCONCLUSIVE** |
| M9_TFT | BTC-USD | 10 | 16 | 3/16 | 0.701275 | 0.9979 | N/A | **INCONCLUSIVE** |
| M9_TFT | ETH-USD | 1 | 16 | 4/16 | 0.746434 | 0.9894 | N/A | **INCONCLUSIVE** |
| M9_TFT | ETH-USD | 5 | 16 | 5/16 | 0.701742 | 0.9616 | N/A | **INCONCLUSIVE** |
| M9_TFT | ETH-USD | 10 | 16 | 3/16 | 0.755272 | 0.9979 | N/A | **INCONCLUSIVE** |

## Model summary

| Model | Combos | BEATS p<0.05 | BEATS p<0.10 | BEATEN p<0.05 | BEATEN p<0.10 | INCONCLUSIVE |
|-------|--------|-------------|-------------|---------------|--------------|-------------|
| M3_HAR_classic | 21 | 12 | 1 | 0 | 0 | 8 |
| M3b_HAR_asymmetric | 6 | 3 | 0 | 0 | 0 | 3 |
| M4_DLinear | 21 | 6 | 1 | 0 | 0 | 14 |
| M5_HMM_regime | 6 | 1 | 0 | 3 | 0 | 2 |
| M9_TFT | 6 | 0 | 0 | 0 | 0 | 6 |
| **TOTAL** | **60** | **22** | **2** | **3** | **0** | **33** |

**Population sign-test:** 24/60 combos beat, 3/60 beaten, p=0.9538

## Key findings

1. **Models with strict BEATS (p<0.05):** M3_HAR_classic, M3b_HAR_asymmetric, M4_DLinear, M5_HMM_regime
2. **Models significantly BEATEN by baseline (p<0.05):** M5_HMM_regime
3. **Models with NO significant signal (INCONCLUSIVE across all combos):** M9_TFT