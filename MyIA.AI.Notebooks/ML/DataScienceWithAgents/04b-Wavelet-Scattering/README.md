# 04b - Wavelet Scattering : ondelettes et scattering

[← DataScienceWithAgents (série parente)](../README.md)

Série sur l'analyse multi-résolution : la transformée en ondelettes réimplémentée from scratch, d'abord en 1D (débruitage par seuillage confronté au passe-bas Fourier), puis en 2D (bandes orientées et compression d'image), puis la transformée de scattering — cascade ondelette → module → moyenne — dont l'invariance par translation est mesurée, validée contre kymatio et exploitée en classification. Le bloc B confronte ces moteurs aux implémentations SOTA (débruitage PyWavelets/skimage, scattering kymatio batché) sur les mêmes protocoles, avec le tableau comparatif final A-vs-B.

## Notebooks

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [WS-00a-Ondelettes-1D-from-scratch](WS-00a-Ondelettes-1D-from-scratch.ipynb) | DWT orthonormale à la main (Haar, D4 par formes closes, db4 par constantes publiées), synthèse écrite comme adjoint exact, validation croisée coefficient par coefficient contre PyWavelets, profil d'énergie par échelle, débruitage par seuillage dur/doux (seuil universel MAD, sans oracle) contre passe-bas Fourier (trois cutoffs, avec oracle) sur le banc canonique Donoho-Johnstone | **Aucune base n'est universellement parcimonieuse** : l'ondelette gagne le chirp (+4,5 dB sans oracle), Fourier gagne le stationnaire (+4,8 dB avec oracle), le mixte est serré |
| [WS-00b-Ondelettes-2D-from-scratch](WS-00b-Ondelettes-2D-from-scratch.ipynb) | Transformée 2D séparable construite comme produit tensoriel du moteur 1D de WS-00a, pyramide de Mallat multi-niveaux, contrôle d'orientation sur motifs à orientation connue (marches verticale/horizontale/diagonale + constante en contrôle négatif), reconstruction parfaite et validation croisée `allclose` bande par bande contre PyWavelets, duel de compression à budget de coefficients apparié contre une DCT 8×8 | **Le pouvoir de parcimonie est conditionnel au budget** : db4 écrase la DCT 8×8 de +16,4 dB à 0,2 % de coefficients retenus, mais l'écart tombe à ~0,2 dB (indiscernable) dès 5 % — l'avantage de la base multi-échelle s'évapore quand on peut se permettre plus de coefficients |
| [WS-00c-Scattering-from-scratch](WS-00c-Scattering-from-scratch.ipynb) | Transformée de scattering 2D from scratch : banc de morlets analytiques en forme close spectrale (pic unique, correction d'admissibilité, norme L²), cascade S0/S1/S2 en une passe pleine résolution, invariance L² par translation mesurée contre pixels et descripteur sans module, sélectivité d'orientation sur les marches de WS-00b, triple validation croisée contre kymatio (traduction du pipeline à filtres injectés = `allclose` rtol=1e-4 ; écart de l'écriture pleine résolution concentré sur S2 ; régime d'invariance commun à deux calibrages indépendants), classification Fashion-MNIST bornée avec test translaté ±2 px | **Le module rend la moyenne invariante** : l'écart par translation plafonne (0,73 à 8 px) là où pixels (1,14) et coefficients sans module (1,07) croissent sans borne — et à 600 images d'entraînement, le scattering complet tient 0,765 de précision sur test translaté quand les pixels s'effondrent de 0,790 à 0,425 |
| [WS-02-Scattering-SOTA](WS-02-Scattering-SOTA.ipynb) | kymatio (backend PyTorch, corpus batché en un tenseur) contre le moteur from-scratch de WS-00c repris à l'identique — même corpus (Fashion-MNIST 80/classe, 600/200), même classifieur (régression logistique L2), même test translaté ±2 px ; diagnostic de conventions par table de correspondance (permutation d'orientations mesurée par corrélation, canaux S1 appariés à 0,64-0,81) ; mesure jumelle accuracy/latence/mémoire ; loi de l'échantillon testée à 400/classe ; tableau récapitulatif final A-vs-B de la série (LOC et dépendances calculés à l'exécution) | **SOTA rime avec ingénierie, pas avec justesse** : kymatio transforme ~50× plus vite (0,38 contre 19,5 ms/image) mais, ses filtres isotropes par défaut étant moins sélectifs que les morlets anisotropes from-scratch, l'accuracy bornée leur donne raison — comprendre en Bloc A, produire en Bloc B |

## Feuille de route (issue #16055)

- **A.1 (livré)** - WS-00a : moteur 1D from scratch + duel débruitage ondelette/Fourier.
- **A.2 (livré)** - WS-00b : ondelettes 2D séparables, bandes orientées, reconstruction parfaite, duel de compression contre la DCT 8×8.
- **A.3 (livré)** - WS-00c : scattering 2D from scratch (cascade ondelette -> module -> moyenne), invariance par translation mesurée, validation croisée triple contre kymatio, classification Fashion-MNIST sur test translaté.
- **B.4 + item 6 (livrés)** - WS-02 : kymatio batché contre le from-scratch sur protocole identique (accuracy/latence/mémoire + permutation d'orientations mesurée), loi de l'échantillon à 400/classe, tableau récapitulatif final A-vs-B.
- **B.5** - débruitage SOTA (PyWavelets/skimage : BayesShrink, SureShrink) — PR #16317 en cours de merge.

## Prérequis

Python 3.10+, `numpy`, `matplotlib` (figures des notebooks), `scipy` (DCT 8×8 servant de baseline en compression, WS-00b), `scikit-learn` (régression logistique des WS-00c/WS-02). `pywt` (PyWavelets) et `kymatio` sont utilisés pour la validation croisée (WS-00c) ET comme moteurs SOTA (WS-01, WS-02 — kymatio sur backend `torch`). Les bases d'algèbre linéaire (orthonormalité, adjoint) et de traitement du signal (FFT) suffisent ; `02-ML-Cours` (2.6, clustering/PCA) et `03-DeepLearning` (3.0, théorie de l'information) fournissent les ponts utiles.

## Position dans la série

Cette sous-série prolonge `03-DeepLearning` et `04-Vision` : les ondelettes sont à la fois un outil classique d'analyse de signal (débruitage, compression) et un ingrédient de réseaux modernes (scattering networks). La discipline est la même que dans les séries voisines : from scratch d'abord, framework ensuite, parité mesurée contre la référence.
