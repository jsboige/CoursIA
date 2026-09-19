# 05-History — Racines pré-Stable-Diffusion

[← Image Applications](../04-Applications/) | [↑ Image](../README.md)

Notebooks rétrospectifs : les outils d'avant Stable Diffusion (2021-2022) qui ont établi les paradigmes encore à l'œuvre aujourd'hui — CLIP comme fonction de perte sémantique, guidance par classifieur, diffusion guidée avant l'ère des modèles ouverts massifs.

## Notebooks

| # | Notebook | Contenu | Publication |
|---|----------|---------|-------------|
| 2 | [05-2-CLIPasso-Semantic-Sketching](05-2-CLIPasso-Semantic-Sketching.ipynb) | Le sketching sémantique : abstraction contrôlée par le nombre de traits (grilles 32/16/8/4 — chameau du papier + robot masqué U²-Net), coût du fond non extrait (A/B masqué/brut), contraste sémantique vs signal (Canny) | Vinker et al., SIGGRAPH 2022 ([arXiv:2202.05822](https://arxiv.org/abs/2202.05822)) |
| 1 | 05-1-DiscoDiffusion *(en préparation, #16477)* | La CLIP-guided diffusion pré-Stable-Diffusion | — |

![Grille d'abstraction CLIPasso — la cible chameau et ses esquisses à 32, 16, 8 puis 4 traits](assets/clipasso/grid_abstraction.png)

*Grille d'abstraction du notebook 05-2 : à mesure que le budget de traits baisse, l'esquisse abandonne le signal (contours) et ne conserve que la sémantique (l'« idée » du chameau) — sortie des runs officiels CLIPasso sur GPU.*

![Grille d'abstraction CLIPasso sur le robot (fond masqué par U²-Net)](assets/clipasso/grid_robot_abstraction.png)

*Même grille sur une seconde cible — le robot généré de la série, fond retiré par U²-Net avant optimisation (`mask_object=1`) : chaque trait travaille pour le sujet.*

![A/B CLIPasso à 16 traits : fond masqué contre fond brut](assets/clipasso/ab_fond_masque_brut.png)

*A/B du coût du fond : à budget égal (16 traits, mêmes graines), l'esquisse masquée gagne +0.062 de similarité CLIP (0.652 contre 0.590) — sans extraction du fond l'esquisse fonctionne, mais une fraction du budget part dans le décor.*

## Prérequis

- Environnement Python du cours (torch CUDA) ;
- Outils locaux hors repo (voir la cellule d'installation du notebook) : clone du [code officiel CLIPasso](https://github.com/yael-vinker/CLIPasso) (MIT) + compilation MSVC de [diffvg](https://github.com/BachiLi/diffvg) — les adaptations d'exécution sont documentées dans le notebook.
