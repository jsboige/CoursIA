# 3D - Neural Rendering : NeRF et représentations neuronales de scènes

[← Documentation GenAI](../README.md) | [→ NeRF from scratch (3D-01)](3D-01-NeRF-From-Scratch.ipynb)

Le rendu 3D neuronal a ouvert une voie différente de la géométrie discrète classique (maillages, voxels, nuages de points) : **paramétrer la scène entière par un réseau de neurones continu**, entraîné uniquement depuis des images 2D calibrées. Cette série introduit le geste fondateur — NeRF (Mildenhall et al., ECCV 2020) — entièrement from scratch, puis mesure ses limitations structurelles, celles-là mêmes qui ont motivé le champ suivant (Mip-NeRF, Instant-NGP, 3D Gaussian Splatting).

Elle comble la lacune « 3D (nuages de points, NeRF, splatting) : confirmé absent » identifiée par l'audit [EPIC #18220](https://github.com/jsboige/CoursIA/issues/18220) pli 3, et constitue le Pli 2 de l'[Epic origami #18605](https://github.com/jsboige/CoursIA/issues/18605) (coord-based neural representations).

## Fil rouge : construire, puis mettre à l'épreuve

L'objectif fil rouge de la série est de **comprendre NeRF de l'intérieur** — chaque équation du papier (§3-§5) devient du code auditable ligne à ligne — puis de **mesurer pourquoi le champ l'a remplacé** : chaque limitation est démontrée par une expérience courte et déterministe, pas par une affirmation.

## Acquis d'apprentissage

À l'issue de la série, l'apprenant sait :

- **Écrire un pipeline NeRF complet** : encodage positionnel $\gamma$ (pont avec les Fourier features de [`3.4d`](../../ML/DataScienceWithAgents/03-DeepLearning/3.4d-Fourier-Features-Biais-Spectral-Python.html)), MLP à sauts de connexion, échantillonnage stratifié le long des rayons, compositing alpha différentiable, quadrature de l'équation de rendu.
- **Relier représentation continue et biais spectral** : pourquoi un MLP brut ne peut pas apprendre les hautes fréquences d'une scène, et ce que l'encodage positionnel change.
- **Mesurer les limites d'une architecture** : temps d'entraînement par scène, effondrement sans Fourier features, sensibilité aux poses, échelle unique du rayon, coût de l'échantillonnage volumique.
- **Situer les successeurs** : Mip-NeRF (frustum conique), Instant-NGP (tables de hachage), 3DGS (gaussiennes explicites) — et pourquoi chaque correctif change de représentation plutôt que de régler le MLP.

## Notebooks

| Notebook | Contenu | Outils |
|----------|---------|--------|
| [3D-01-NeRF-From-Scratch](3D-01-NeRF-From-Scratch.ipynb) | Pipeline NeRF complet from scratch (~200 lignes PyTorch) : scène jouet volumétrique analytique, entraînement, tranches de densité, évaluation MSE/PSNR sur la scène Blender Lego 100×100 du papier | PyTorch, matplotlib |
| [3D-02-NeRF-Critic](3D-02-NeRF-Critic.ipynb) | Les cinq limitations historiques de NeRF, chacune mesurée sur la scène jouet : paliers de qualité, ablation de l'encodage, bruit de pose, zoom multi-échelle, coût de l'échantillonnage | PyTorch, matplotlib |

## Prérequis et exécution

- **Prérequis conceptuel** : biais spectral et Fourier features ([`3.4d-Fourier-Features`](../../ML/DataScienceWithAgents/03-DeepLearning/3.4d-Fourier-Features-Biais-Spectral-Python.html), Pli 1 de l'Epic #18605).
- **Exécution** : PyTorch (CPU jouable pour la scène jouet ; GPU recommandé — ~2-3 min pour 3D-01, ~10-12 min pour 3D-02 sur RTX 3090). Les seeds sont fixés : les résultats sont reproductibles.
- **Dataset** : `tiny_nerf_data.npz` (scène Blender « Lego » 100×100, © les auteurs de NeRF) téléchargé au premier lancement depuis la page projet UCSD des auteurs, mis en cache dans `data/` (hors dépôt).

## Suite de la série (plis suivants de l'Epic #18605)

- **Pli 3 — R-gsplat** : la transition NeRF → 3D Gaussian Splatting (Kerbl et al., SIGGRAPH 2023) avec `nerfstudio-project/gsplat` comme moteur CUDA — du volume continu au nuage de gaussiennes explicites.

## Références

- Mildenhall, Srinivasan, Tancik, Barron, Ramamoorthi, Ng — *NeRF: Representing Scenes as Neural Radiance Fields for View Synthesis*, ECCV 2020 ([arXiv:2003.08934](https://arxiv.org/abs/2003.08934)) — PDF archivé dans le gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA`.
- Tancik et al. — *Fourier Features Let Networks Learn High Frequency Functions in Low Dimensional Domains*, NeurIPS 2020 ([arXiv:2006.10739](https://arxiv.org/abs/2006.10739)).
- Barron et al. — *Mip-NeRF*, ICCV 2021 ([arXiv:2103.13415](https://arxiv.org/abs/2103.13415)).
- Müller et al. — *Instant-NGP*, SIGGRAPH 2022 ; Kerbl et al. — *3D Gaussian Splatting*, SIGGRAPH 2023.
