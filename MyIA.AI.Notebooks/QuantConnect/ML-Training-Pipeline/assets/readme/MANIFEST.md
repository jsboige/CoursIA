# Galerie README — Pipeline d'entraînement ML

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS, markdown + code).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks de recherche (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim, natives (0 downscale).

| Figure | Notebook source | Cellule | Output | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|------------|-------|-------------|
| `mltp-hmm-regime.png` | `m5_hmm_regime_research.ipynb` | 6 | 1 | 779×409 | 29,8 KB | Détection de régimes HMM — probabilités postérieures par état |
| `mltp-har-rv.png` | `m12_har_rv_j_research.ipynb` | 6 | 0 | 715×432 | 33,1 KB | Décomposition de sauts HAR-RV-J — variance réalisée continue vs discontinue |
| `mltp-dlinear-vol.png` | `m4_dlinear_vol_research.ipynb` | 6 | 1 | 706×404 | 29,9 KB | Prévision DLinear — DL linéaire vs baseline HAR |
| `mltp-lstm-vol.png` | `m15_lstm_rv_research.ipynb` | 6 | 0 | 719×432 | 39,2 KB | Prévision Log-LSTM — mémoire séquentielle pour la variance réalisée |
| `mltp-tft-vol.png` | `m9_tft_vol_research.ipynb` | 6 | 1 | 790×409 | 60,3 KB | Attention Temporelle TFT — pondération des variables d'entrée |
| `mltp-ensemble.png` | `m11e_ensemble_research.ipynb` | 6 | 1 | 832×430 | 29,7 KB | Diagnostic d'ensemble HAR-Kelly — dilution des performances |

**Diversité méthodologique couverte** : classique (HAR-RV-J), DL linéaire (DLinear), récurrent (LSTM), Transformer à attention (TFT), Switching de régimes (HMM), combinaison de modèles (Ensemble). Total : 6 figures, 222,0 KB, max 60,3 KB/fichier.
