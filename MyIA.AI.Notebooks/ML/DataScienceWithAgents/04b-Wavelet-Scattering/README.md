# 04b - Wavelet Scattering : ondelettes et scattering

[← DataScienceWithAgents (série parente)](../README.md)

Série sur l'analyse multi-résolution : la transformée en ondelettes 1D réimplémentée from scratch, le débruitage par seuillage confronté au passe-bas Fourier, puis (feuille de route) l'extension 2D et les scattering networks invariants par translation.

## Notebooks

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [WS-00a-Ondelettes-1D-from-scratch](WS-00a-Ondelettes-1D-from-scratch.ipynb) | DWT orthonormale à la main (Haar, D4 par formes closes, db4 par constantes publiées), synthèse écrite comme adjoint exact, validation croisée coefficient par coefficient contre PyWavelets, profil d'énergie par échelle, débruitage par seuillage dur/doux (seuil universel MAD, sans oracle) contre passe-bas Fourier (trois cutoffs, avec oracle) sur le banc canonique Donoho-Johnstone | **Aucune base n'est universellement parcimonieuse** : l'ondelette gagne le chirp (+4,5 dB sans oracle), Fourier gagne le stationnaire (+4,8 dB avec oracle), le mixte est serré |

## Feuille de route (issue #16055)

- **A.1 (livré)** - WS-00a : moteur 1D from scratch + duel débruitage ondelette/Fourier.
- **A.2** - Ondelettes 2D : extension séparable, damiers de détails, compression d'image.
- **A.3** - Scattering : cascade ondelette -> module -> moyenne, invariance par translation par construction.
- **Bloc B** - SOTA : PyWavelets (BayesShrink, SureShrink), kymatio (scattering GPU), tableau comparatif from scratch vs SOTA.

## Prérequis

Python 3.10+, `numpy`. `pywt` (PyWavelets) n'est utilisé que pour la validation croisée, jamais pour calculer. Les bases d'algèbre linéaire (orthonormalité, adjoint) et de traitement du signal (FFT) suffisent ; `02-ML-Cours` (2.6, clustering/PCA) et `03-DeepLearning` (3.0, théorie de l'information) fournissent les ponts utiles.

## Position dans la série

Cette sous-série prolonge `03-DeepLearning` et `04-Vision` : les ondelettes sont à la fois un outil classique d'analyse de signal (débruitage, compression) et un ingrédient de réseaux modernes (scattering networks). La discipline est la même que dans les séries voisines : from scratch d'abord, framework ensuite, parité mesurée contre la référence.
