# Profil par itération — banc 4, régime de mesure (semantic-fleet, 13/11/2026)

Genere par `scripts/benchmarks/bdn_iteration_profile.py` depuis `docs/dotnet/banc4-regime-25644.json` (SHA-256 `603aa2822c532d18bd6880dc2e412fbc210c90076c488c8aa9f12e2c7f21ca67`), lignes `WorkloadActual`.

Controle : 500 permutations par jambe, graine 20261115, au moins 3 iterations de chaque cote du point de coupe. Le rapport publie est celui des medianes ; la p-valeur est unilaterale et sa resolution vaut 1/501.

## Synthese

- Jambes lues : **96** ; series trop courtes pour un point de coupe : **0**.
- Marche significative contre l'ordre melange : **11** a p < 0,05, dont **4** a p < 0,01 (500 permutations par jambe).
- Rapport mediane avant / mediane apres, sur les 96 jambes mesurables : de 0.46 a 14.45.
- Un p eleve ne prouve pas l'absence de marche : la puissance est faible a quinze iterations et forte dispersion. Une marche detectee n'identifie pas sa cause.

## Ce que chaque colonne dit

- **position** : nombre d'iterations dans la partie « avant ». Une position a 9 signifie que les iterations 1 a 9 precedent la marche.
- **ratio** : mediane(avant) / mediane(apres), sans arrondi favorable.
- **part** : `(moyenne - mediane apres) / moyenne`, c'est-a-dire la part de la moyenne totale portee par le regime d'avant la marche. Negative quand la mediane d'apres depasse la moyenne.
- **p** : p-valeur du rapport contre l'ordre melange. Seules les lignes a p < 0,05 portent une marche distinguable du hasard.

## Table

| Methode | Runtime | Regime | Tiering | Passe | n | moyenne (us/op) | position | ratio | p | part |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| `Signature_Matches` | 9.0.22 | one | default | 2 | 15 | 17.244 | 5 | 1.47 | 0.002 | 0.606 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | default | 2 | 15 | 25.697 | 8 | 3.82 | 0.004 | 0.590 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | default | 1 | 15 | 6.766 | 3 | 3.98 | 0.010 | 0.411 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | default | 1 | 15 | 403.821 | 12 | 1.71 | 0.010 | 0.375 |
| `Transform_InterpolateKeys` | 9.0.22 | one | off | 2 | 15 | 62.087 | 3 | 4.46 | 0.012 | 0.591 |
| `Signature_Matches` | 10.0.14 | one | off | 1 | 15 | 74.401 | 3 | 1.50 | 0.012 | 0.950 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | default | 1 | 15 | 130.897 | 12 | 4.07 | 0.014 | 0.703 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | off | 3 | 15 | 8.199 | 12 | 2.36 | 0.020 | 0.524 |
| `Signature_Matches` | 10.0.14 | one | off | 2 | 15 | 17.322 | 3 | 1.34 | 0.030 | 0.696 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | default | 2 | 15 | 39.420 | 4 | 2.77 | 0.040 | 0.347 |
| `Signature_Matches` | 9.0.22 | auto | off | 1 | 15 | 0.231 | 4 | 1.87 | 0.040 | 0.256 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | off | 2 | 15 | 41.154 | 6 | 2.77 | 0.058 | 0.586 |
| `Signature_Matches` | 10.0.14 | one | off | 3 | 15 | 4.394 | 3 | 1.72 | 0.058 | 0.201 |
| `Transform_InterpolateKeys` | 10.0.14 | one | off | 2 | 15 | 129.781 | 5 | 12.69 | 0.068 | 0.801 |
| `Signature_Matches` | 10.0.14 | one | default | 2 | 15 | 6.983 | 3 | 1.26 | 0.084 | 0.258 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | default | 2 | 15 | 283.779 | 3 | 3.17 | 0.090 | 0.619 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | off | 1 | 15 | 22.510 | 12 | 1.12 | 0.102 | 0.124 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | default | 1 | 15 | 14.380 | 11 | 1.77 | 0.124 | 0.509 |
| `Transform_InterpolateKeys` | 10.0.14 | one | off | 1 | 15 | 28.340 | 3 | 1.37 | 0.124 | 0.136 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | off | 2 | 15 | 118.442 | 7 | 2.08 | 0.128 | 0.303 |
| `Signature_Matches` | 10.0.14 | auto | default | 3 | 15 | 0.088 | 3 | 1.62 | 0.132 | 0.217 |
| `Transform_InterpolateKeys` | 10.0.14 | one | default | 3 | 15 | 22.024 | 7 | 1.10 | 0.144 | 0.080 |
| `Transform_InterpolateKeys` | 9.0.22 | one | off | 3 | 15 | 190.331 | 7 | 3.45 | 0.146 | 0.860 |
| `Signature_Matches` | 10.0.14 | one | default | 3 | 15 | 183.320 | 4 | 10.15 | 0.152 | 0.952 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | off | 1 | 15 | 11.811 | 6 | 1.26 | 0.152 | 0.281 |
| `Transform_InterpolateKeys` | 10.0.14 | one | off | 3 | 15 | 154.955 | 7 | 5.03 | 0.154 | 0.821 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | default | 3 | 15 | 11.376 | 11 | 1.44 | 0.156 | 0.313 |
| `Signature_Matches` | 9.0.22 | auto | off | 2 | 15 | 0.245 | 3 | 1.63 | 0.160 | 0.256 |
| `Signature_Matches` | 10.0.14 | auto | off | 1 | 15 | 0.215 | 11 | 1.15 | 0.192 | 0.187 |
| `Signature_Matches` | 10.0.14 | auto | off | 3 | 15 | 0.096 | 3 | 1.18 | 0.202 | 0.075 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | off | 2 | 15 | 20.104 | 4 | 1.17 | 0.208 | 0.077 |
| `Transform_InterpolateKeys` | 9.0.22 | one | default | 1 | 15 | 100.483 | 3 | 2.17 | 0.214 | 0.471 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | off | 2 | 15 | 37.145 | 3 | 1.08 | 0.222 | 0.245 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | off | 2 | 15 | 16.567 | 10 | 1.22 | 0.226 | 0.300 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | default | 2 | 15 | 21.326 | 12 | 1.96 | 0.230 | 0.645 |
| `Signature_Matches` | 10.0.14 | one | default | 1 | 15 | 202.258 | 8 | 14.45 | 0.234 | 0.955 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | default | 2 | 15 | 430.606 | 6 | 2.80 | 0.234 | 0.499 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | off | 2 | 15 | 4.143 | 11 | 1.12 | 0.234 | 0.102 |
| `Signature_Matches` | 9.0.22 | one | default | 1 | 15 | 79.781 | 3 | 7.14 | 0.248 | 0.904 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | default | 3 | 15 | 140.983 | 4 | 1.18 | 0.263 | 0.279 |
| `Signature_Matches` | 9.0.22 | auto | default | 2 | 15 | 0.046 | 3 | 1.04 | 0.263 | 0.028 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | default | 3 | 15 | 10.897 | 8 | 1.64 | 0.269 | 0.367 |
| `Signature_Matches` | 9.0.22 | auto | default | 3 | 15 | 0.114 | 3 | 1.33 | 0.275 | 0.156 |
| `Transform_InterpolateKeys` | 10.0.14 | one | default | 1 | 15 | 502.053 | 9 | 2.78 | 0.305 | 0.951 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | default | 1 | 15 | 632.036 | 10 | 2.64 | 0.313 | 0.585 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | off | 1 | 15 | 31.991 | 12 | 1.11 | 0.331 | 0.106 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | default | 3 | 15 | 194.415 | 11 | 1.37 | 0.345 | 0.222 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | default | 1 | 15 | 677.611 | 8 | 4.15 | 0.355 | 0.809 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | off | 3 | 15 | 553.944 | 11 | 5.16 | 0.389 | 0.839 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | off | 3 | 15 | 13.143 | 6 | 1.06 | 0.401 | 0.097 |
| `Transform_InterpolateKeys` | 10.0.14 | one | default | 2 | 15 | 209.642 | 3 | 2.54 | 0.405 | 0.804 |
| `Signature_Matches` | 9.0.22 | auto | off | 3 | 15 | 0.187 | 8 | 1.17 | 0.415 | 0.092 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | off | 1 | 15 | 509.700 | 11 | 2.43 | 0.423 | 0.576 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | off | 1 | 15 | 41.231 | 12 | 1.10 | 0.423 | 0.060 |
| `Transform_InterpolateKeys` | 9.0.22 | one | off | 1 | 15 | 172.212 | 12 | 3.57 | 0.425 | 0.823 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | off | 1 | 15 | 16.148 | 3 | 1.31 | 0.435 | 0.435 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | default | 3 | 15 | 32.583 | 6 | 1.20 | 0.457 | 0.162 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | default | 2 | 15 | 3.681 | 12 | 1.08 | 0.467 | 0.092 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | default | 2 | 15 | 8.372 | 3 | 1.06 | 0.471 | 0.115 |
| `Signature_Matches` | 10.0.14 | auto | off | 2 | 15 | 0.262 | 12 | 1.16 | 0.481 | 0.412 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | default | 2 | 15 | 865.168 | 3 | 1.81 | 0.489 | 0.747 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | default | 2 | 15 | 124.927 | 7 | 1.29 | 0.489 | 0.328 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | default | 1 | 15 | 189.684 | 6 | 1.07 | 0.499 | -0.009 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | default | 1 | 15 | 555.745 | 12 | 3.58 | 0.511 | 0.690 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | off | 3 | 15 | 56.744 | 9 | 1.27 | 0.513 | 0.248 |
| `Signature_Matches` | 10.0.14 | auto | default | 2 | 15 | 0.039 | 4 | 1.14 | 0.513 | 0.111 |
| `Signature_Matches` | 9.0.22 | one | default | 3 | 15 | 133.189 | 12 | 3.07 | 0.529 | 0.889 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | off | 3 | 15 | 215.295 | 3 | 3.12 | 0.531 | 0.809 |
| `Transform_InterpolateKeys` | 9.0.22 | one | default | 2 | 15 | 249.099 | 12 | 2.31 | 0.549 | 0.865 |
| `Signature_Matches` | 9.0.22 | one | off | 1 | 15 | 188.822 | 5 | 1.11 | 0.563 | 0.961 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | off | 2 | 15 | 222.631 | 3 | 1.41 | 0.583 | 0.743 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | default | 2 | 15 | 3.613 | 12 | 1.08 | 0.593 | 0.058 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | default | 3 | 15 | 9.863 | 11 | 1.14 | 0.609 | 0.164 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | off | 2 | 15 | 18.349 | 12 | 1.06 | 0.647 | 0.164 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | default | 3 | 15 | 130.974 | 3 | 1.08 | 0.669 | 0.365 |
| `Signature_Matches` | 9.0.22 | one | off | 2 | 15 | 7.561 | 11 | 1.06 | 0.669 | 0.314 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | off | 1 | 15 | 953.517 | 3 | 1.37 | 0.671 | 0.107 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | off | 1 | 15 | 38.622 | 11 | 1.09 | 0.671 | 0.264 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | default | 3 | 15 | 7.703 | 5 | 1.08 | 0.679 | 0.126 |
| `Signature_Matches` | 9.0.22 | auto | default | 1 | 15 | 0.124 | 3 | 1.15 | 0.709 | 0.086 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | off | 1 | 15 | 90.870 | 5 | 1.10 | 0.709 | 0.524 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | off | 3 | 15 | 23.061 | 3 | 1.06 | 0.721 | 0.351 |
| `Signature_Matches` | 9.0.22 | one | off | 3 | 15 | 8.685 | 8 | 1.08 | 0.729 | 0.295 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | off | 3 | 15 | 16.496 | 8 | 1.03 | 0.768 | 0.059 |
| `JsonSerialize_PromptSettings` | 9.0.22 | one | default | 3 | 15 | 139.612 | 4 | 1.04 | 0.780 | 0.347 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | off | 3 | 15 | 610.655 | 11 | 1.46 | 0.782 | 0.588 |
| `JsonSerialize_PromptSettings` | 10.0.14 | auto | default | 1 | 15 | 46.684 | 11 | 1.01 | 0.842 | -0.046 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | default | 1 | 15 | 279.769 | 8 | 0.99 | 0.878 | 0.656 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | off | 2 | 15 | 4.691 | 3 | 0.93 | 0.930 | 0.103 |
| `Transform_InterpolateKeys` | 9.0.22 | one | default | 3 | 15 | 28.396 | 6 | 0.98 | 0.962 | 0.020 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | default | 3 | 15 | 49.943 | 12 | 0.95 | 0.970 | -0.173 |
| `Signature_Matches` | 10.0.14 | auto | default | 1 | 15 | 0.087 | 6 | 0.87 | 0.970 | -0.077 |
| `RequestSettings_RoundTrip` | 9.0.22 | one | off | 2 | 15 | 86.492 | 3 | 0.96 | 0.978 | 0.365 |
| `JsonSerialize_PromptSettings` | 10.0.14 | one | off | 1 | 15 | 455.381 | 5 | 0.46 | 0.978 | 0.119 |
| `RequestSettings_RoundTrip` | 10.0.14 | one | off | 3 | 15 | 1254.411 | 9 | 0.60 | 0.994 | 0.135 |
| `Transform_InterpolateKeys` | 10.0.14 | auto | off | 3 | 15 | 6.592 | 12 | 0.63 | 1.000 | -0.219 |
