# 3D - Neural Rendering : de NeRF aux gaussiennes splatting

[← Documentation GenAI](../README.md) | [→ NeRF from scratch (3D-01)](3D-01-NeRF-From-Scratch.ipynb)

Le rendu 3D neuronal a ouvert une voie différente de la géométrie discrète classique (maillages, voxels, nuages de points) : **paramétrer la scène entière par un réseau de neurones continu**, entraîné uniquement depuis des images 2D calibrées. Cette série introduit le geste fondateur — NeRF (Mildenhall et al., ECCV 2020) — entièrement from scratch, puis mesure ses limitations structurelles, celles-là mêmes qui ont motivé le champ suivant (Mip-NeRF, Instant-NGP, 3D Gaussian Splatting).

Elle comble la lacune « 3D (nuages de points, NeRF, splatting) : confirmé absent » identifiée par l'audit [EPIC #18220](https://github.com/jsboige/CoursIA/issues/18220) pli 3, et porte le Pli 2 (NeRF, 3D-01 et 3D-02) puis le Pli 3 — R-gsplat (3D-03 à 3D-06) — de l'[Epic origami #18605](https://github.com/jsboige/CoursIA/issues/18605) (coord-based neural representations).

## Fil rouge : construire, puis mettre à l'épreuve

L'objectif fil rouge de la série est de **comprendre NeRF de l'intérieur** — chaque équation du papier (§3-§5) devient du code auditable ligne à ligne — puis de **mesurer pourquoi le champ l'a remplacé** : chaque limitation est démontrée par une expérience courte et déterministe, pas par une affirmation. Le Pli 3 referme la boucle en **construisant le remplaçant** — les gaussiennes splatting, entraînées sur le moteur CUDA réel — et en mesurant ses propres leviers d'entraînement.

## Acquis d'apprentissage

À l'issue de la série, l'apprenant sait :

- **Écrire un pipeline NeRF complet** : encodage positionnel $\gamma$ (pont avec les Fourier features de [`3.4d`](../../ML/DataScienceWithAgents/03-DeepLearning/3.4d-Fourier-Features-Biais-Spectral-Python.ipynb)), MLP à sauts de connexion, échantillonnage stratifié le long des rayons, compositing alpha différentiable, quadrature de l'équation de rendu.
- **Relier représentation continue et biais spectral** : pourquoi un MLP brut ne peut pas apprendre les hautes fréquences d'une scène, et ce que l'encodage positionnel change.
- **Mesurer les limites d'une architecture** : temps d'entraînement par scène, effondrement sans Fourier features, sensibilité aux poses, échelle unique du rayon, coût de l'échantillonnage volumique.
- **Situer les successeurs** : Mip-NeRF (frustum conique), Instant-NGP (tables de hachage), 3DGS (gaussiennes explicites) — et pourquoi chaque correctif change de représentation plutôt que de régler le MLP.
- **Construire le splat** : covariance 3D projetée en ellipse 2D, tri par profondeur et alpha-blending correctement ordonné (3D-03), puis entraînement 3DGS complet sur le moteur CUDA réel `gsplat` — paramétrisation, conventions caméra, convergence mesurée (3D-04).
- **Piloter l'entraînement par la mesure** : densification (clones/scissions), reset d'opacité, learning rates différenciés, plancher d'échelle — chaque levier comparé sur banc court, avec son échelle temporelle d'action (3D-05).
- **Lire du code de production** : reconnaître tri côté GPU, conventions d'axes et pas de temps fixe dans une application navigateur réelle à base de splats (3D-06).

## Notebooks

| Notebook | Contenu | Outils |
|----------|---------|--------|
| [3D-01-NeRF-From-Scratch](3D-01-NeRF-From-Scratch.ipynb) | Pipeline NeRF complet from scratch en PyTorch : scène jouet volumétrique analytique, entraînement, tranches de densité, évaluation MSE/PSNR sur la scène Blender Lego 100×100 du papier | PyTorch, matplotlib |
| [3D-02-NeRF-Critic](3D-02-NeRF-Critic.ipynb) | Les cinq limitations historiques de NeRF, chacune mesurée sur la scène jouet : paliers de qualité, ablation de l'encodage, bruit de pose, zoom multi-échelle, coût de l'échantillonnage | PyTorch, matplotlib |
| [3D-03-Gaussian-Splats-Concepts](3D-03-Gaussian-Splats-Concepts.ipynb) | Gaussiennes splatting from scratch en Python pur : projeter une covariance 3D en ellipse 2D, trier par profondeur, composer par alpha-blending — et pourquoi l'ordre de rendu n'est pas négociable | PyTorch (CPU), matplotlib |
| [3D-04-3DGS-From-Scratch-with-gsplat](3D-04-3DGS-From-Scratch-with-gsplat.ipynb) | Entraînement 3DGS complet sur le moteur CUDA réel `gsplat` : paramétrisation (positions, quaternions, échelles, opacités, couleurs SH), conversion caméra OpenGL vers OpenCV, parité et vitesse mesurées contre l'implémentation maison | gsplat, PyTorch CUDA |
| [3D-05-3DGS-Optimization-Tradeoffs](3D-05-3DGS-Optimization-Tradeoffs.ipynb) | Les leviers d'entraînement à la mesure sur banc comparatif : densification par clones et scissions, reset d'opacité, learning rates différenciés, plancher d'échelle — et ce que le banc court réfute des intuitions du papier | gsplat, PyTorch CUDA |
| [3D-06-Spark-Interactive-Demo](3D-06-Spark-Interactive-Demo.md) | Annexe : lecture annotée d'une application navigateur réelle à base de splats (`bmild/spark-physics`) — tri côté GPU, taxe permanente des conventions d'axes, image contre géométrie de collision, pas de temps fixe | lecture guidée (sans exécution) |

## Prérequis et exécution

- **Prérequis conceptuel** : biais spectral et Fourier features ([`3.4d-Fourier-Features`](../../ML/DataScienceWithAgents/03-DeepLearning/3.4d-Fourier-Features-Biais-Spectral-Python.ipynb), Pli 1 de l'Epic #18605).
- **Exécution** : PyTorch (CPU jouable pour la scène jouet ; GPU recommandé — ~2-3 min pour 3D-01, ~10-12 min pour 3D-02 sur RTX 3090). Les seeds sont fixés : les résultats sont reproductibles.
- **Pli 3 (3D-04, 3D-05)** : GPU requis, kernel conda `gsplat310` (Python 3.10, torch 2.4.1+cu124, roue officielle gsplat +pt24cu124) ; 3D-03 est jouable CPU. À taille de nuage fixe, l'ordre flottant des atomiques CUDA varie légèrement les trajectoires entre exécutions — les conclusions citent les statistiques robustes (perte, moyennes), pas les extrema. 3D-06 est une lecture guidée, sans exécution.
- **Dataset** : `tiny_nerf_data.npz` (scène Blender « Lego » 100×100, © les auteurs de NeRF) téléchargé au premier lancement depuis la page projet UCSD des auteurs, mis en cache dans `data/` (hors dépôt).

## Les plis de la série (Epic #18605)

- **Pli 1 — Fourier features** : [`3.4d-Fourier-Features-Biais-Spectral-Python`](../../ML/DataScienceWithAgents/03-DeepLearning/3.4d-Fourier-Features-Biais-Spectral-Python.ipynb) (ML/DataScienceWithAgents) — le socle spectral commun.
- **Pli 2 — NeRF from scratch** : 3D-01 (pipeline complet), 3D-02 (limitations mesurées).
- **Pli 3 — R-gsplat** : la transition NeRF → 3D Gaussian Splatting (Kerbl et al., SIGGRAPH 2023) avec `nerfstudio-project/gsplat` comme moteur CUDA — concepts et tri (3D-03), entraînement from scratch (3D-04), leviers d'optimisation (3D-05), annexe application réelle (3D-06).

## Références

- Mildenhall, Srinivasan, Tancik, Barron, Ramamoorthi, Ng — *NeRF: Representing Scenes as Neural Radiance Fields for View Synthesis*, ECCV 2020 ([arXiv:2003.08934](https://arxiv.org/abs/2003.08934)) — PDF archivé dans le gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA`.
- Tancik et al. — *Fourier Features Let Networks Learn High Frequency Functions in Low Dimensional Domains*, NeurIPS 2020 ([arXiv:2006.10739](https://arxiv.org/abs/2006.10739)).
- Barron et al. — *Mip-NeRF*, ICCV 2021 ([arXiv:2103.13415](https://arxiv.org/abs/2103.13415)).
- Müller et al. — *Instant-NGP*, SIGGRAPH 2022.
- Kerbl, Kopanas, Leimkühler, Drettakis — *3D Gaussian Splatting for Real-Time Radiance Field Rendering*, SIGGRAPH 2023 ([arXiv:2308.04079](https://arxiv.org/abs/2308.04079)) — PDF archivé dans le gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA`.
