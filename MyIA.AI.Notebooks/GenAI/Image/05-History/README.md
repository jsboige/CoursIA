# 05-History — Racines pré-Stable-Diffusion

[← Image Applications](../04-Applications/) | [↑ Image](../README.md)

Notebooks rétrospectifs : les outils d'avant Stable Diffusion (2021-2022) qui ont établi les paradigmes encore à l'œuvre aujourd'hui — CLIP comme fonction de perte sémantique, guidance par classifieur, diffusion guidée avant l'ère des modèles ouverts massifs.

## Notebooks

| # | Notebook | Contenu | Publication |
|---|----------|---------|-------------|
| 2 | [05-2-CLIPasso-Semantic-Sketching](05-2-CLIPasso-Semantic-Sketching.ipynb) | Le sketching sémantique : abstraction contrôlée par le nombre de traits (grille 32/16/8/4), contraste sémantique vs signal (Canny) | Vinker et al., SIGGRAPH 2022 ([arXiv:2202.05822](https://arxiv.org/abs/2202.05822)) |
| 1 | 05-1-DiscoDiffusion *(en préparation, #16477)* | La CLIP-guided diffusion pré-Stable-Diffusion | — |

![Grille d'abstraction CLIPasso — la cible chameau et ses esquisses à 32, 16, 8 puis 4 traits](assets/clipasso/grid_abstraction.png)

*Grille d'abstraction du notebook 05-2 : à mesure que le budget de traits baisse, l'esquisse abandonne le signal (contours) et ne conserve que la sémantique (l'« idée » du chameau) — sortie des runs officiels CLIPasso sur GPU.*

## Prérequis

- Environnement Python du cours (torch CUDA) ;
- Outils locaux hors repo (voir la cellule d'installation du notebook) : clone du [code officiel CLIPasso](https://github.com/yael-vinker/CLIPasso) (MIT) + compilation MSVC de [diffvg](https://github.com/BachiLi/diffvg) — les adaptations d'exécution sont documentées dans le notebook.
