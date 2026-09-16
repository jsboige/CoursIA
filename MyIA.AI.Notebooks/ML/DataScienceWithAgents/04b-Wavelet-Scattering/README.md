# 04b - Wavelet Scattering : ondelettes et scattering

[← DataScienceWithAgents (série parente)](../README.md)

Série sur l'analyse multi-résolution : la transformée en ondelettes réimplémentée from scratch, d'abord en 1D (débruitage par seuillage confronté au passe-bas Fourier), puis en 2D (bandes orientées et compression d'image), puis la transformée de scattering — cascade ondelette → module → moyenne — dont l'invariance par translation est mesurée, validée contre kymatio et exploitée en classification. Le notebook de synthèse referme l'arc en confrontant la représentation construite aux features d'un ResNet pré-entraîné.

## Notebooks

| Notebook | Sujet | Concept-phare |
|----------|-------|---------------|
| [WS-00a-Ondelettes-1D-from-scratch](WS-00a-Ondelettes-1D-from-scratch.ipynb) | DWT orthonormale à la main (Haar, D4 par formes closes, db4 par constantes publiées), synthèse écrite comme adjoint exact, validation croisée coefficient par coefficient contre PyWavelets, profil d'énergie par échelle, débruitage par seuillage dur/doux (seuil universel MAD, sans oracle) contre passe-bas Fourier (trois cutoffs, avec oracle) sur le banc canonique Donoho-Johnstone | **Aucune base n'est universellement parcimonieuse** : l'ondelette gagne le chirp (+4,5 dB sans oracle), Fourier gagne le stationnaire (+4,8 dB avec oracle), le mixte est serré |
| [WS-00b-Ondelettes-2D-from-scratch](WS-00b-Ondelettes-2D-from-scratch.ipynb) | Transformée 2D séparable construite comme produit tensoriel du moteur 1D de WS-00a, pyramide de Mallat multi-niveaux, contrôle d'orientation sur motifs à orientation connue (marches verticale/horizontale/diagonale + constante en contrôle négatif), reconstruction parfaite et validation croisée `allclose` bande par bande contre PyWavelets, duel de compression à budget de coefficients apparié contre une DCT 8×8 | **Le pouvoir de parcimonie est conditionnel au budget** : db4 écrase la DCT 8×8 de +16,4 dB à 0,2 % de coefficients retenus, mais l'écart tombe à ~0,2 dB (indiscernable) dès 5 % — l'avantage de la base multi-échelle s'évapore quand on peut se permettre plus de coefficients |
| [WS-00c-Scattering-from-scratch](WS-00c-Scattering-from-scratch.ipynb) | Transformée de scattering 2D from scratch : banc de morlets analytiques en forme close spectrale (pic unique, correction d'admissibilité, norme L²), cascade S0/S1/S2 en une passe pleine résolution, invariance L² par translation mesurée contre pixels et descripteur sans module, sélectivité d'orientation sur les marches de WS-00b, triple validation croisée contre kymatio (traduction du pipeline à filtres injectés = `allclose` rtol=1e-4 ; écart de l'écriture pleine résolution concentré sur S2 ; régime d'invariance commun à deux calibrages indépendants), classification Fashion-MNIST bornée avec test translaté ±2 px | **Le module rend la moyenne invariante** : l'écart par translation plafonne (0,73 à 8 px) là où pixels (1,14) et coefficients sans module (1,07) croissent sans borne — et à 600 images d'entraînement, le scattering complet tient 0,765 de précision sur test translaté quand les pixels s'effondrent de 0,790 à 0,425 |
| [WS-03-Synthese-Scattering-vs-ResNet](WS-03-Synthese-Scattering-vs-ResNet.ipynb) | Synthèse finale : représentation construite (scattering kymatio J=2, L=4, 1225-d) contre représentation apprise (ResNet18 pré-entraîné ImageNet, avgpool 512-d) sur le même Fashion-MNIST (1 500 train / 750 test, vrai split test torchvision), même sonde (régression logistique standardisée), même test translaté ±2 px, écart relatif de représentation mesuré sous décalage, tableau récap à quatre axes (discrimination, stabilité, coût, dimension) | **Construit et appris ne dominent pas les mêmes axes** : le scattering gagne le test propre (0,837 contre 0,811) et coûte ~28× moins cher à l'extraction (0,39 contre 11,04 ms/image) sans avoir vu une seule image ; le ResNet gagne la robustesse au décalage (chute 0,060 contre 0,255, écart relatif 0,331 contre 0,425) — la frontière du *pourquoi du from scratch / quand du SOTA* se lit axe par axe, pas en un vainqueur |

## Feuille de route (issue #16055)

- **A.1 (livré)** - WS-00a : moteur 1D from scratch + duel débruitage ondelette/Fourier.
- **A.2 (livré)** - WS-00b : ondelettes 2D séparables, bandes orientées, reconstruction parfaite, duel de compression contre la DCT 8×8.
- **A.3 (livré)** - WS-00c : scattering 2D from scratch (cascade ondelette -> module -> moyenne), invariance par translation mesurée, validation croisée triple contre kymatio, classification Fashion-MNIST sur test translaté.
- **Bloc B** - SOTA : PyWavelets (BayesShrink, SureShrink), kymatio (scattering GPU), tableau comparatif from scratch vs SOTA.
- **Synthèse (livré)** - WS-03 : représentation construite (scattering) vs apprise (features ResNet18 pré-entraîné) sur le même dataset, même sonde, même test translaté — le tableau récap à quatre axes.

## Prérequis

Python 3.10+, `numpy`, `matplotlib` (figures des notebooks), `scipy` (DCT 8×8 servant de baseline en compression, WS-00b), `scikit-learn` (régression logistique du WS-00c et du WS-03), `torch`/`torchvision` (features ResNet18 pré-entraîné et chargement Fashion-MNIST du WS-03). `pywt` (PyWavelets) et `kymatio` ne sont utilisés que pour la validation croisée, jamais pour calculer. Les bases d'algèbre linéaire (orthonormalité, adjoint) et de traitement du signal (FFT) suffisent ; `02-ML-Cours` (2.6, clustering/PCA) et `03-DeepLearning` (3.0, théorie de l'information) fournissent les ponts utiles.

## Position dans la série

Cette sous-série prolonge `03-DeepLearning` et `04-Vision` : les ondelettes sont à la fois un outil classique d'analyse de signal (débruitage, compression) et un ingrédient de réseaux modernes (scattering networks). La discipline est la même que dans les séries voisines : from scratch d'abord, framework ensuite, parité mesurée contre la référence.
