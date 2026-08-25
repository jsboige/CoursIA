# 03-DeepLearning — Le deep learning from scratch : ouvrir la boîte noire couche par couche

[← DataScienceWithAgents (série parente)](../README.md) | [02-ML-Cours (prérequis)](../02-ML-Cours/README.md)

**Kernel** : Python 3 · **Bibliothèques** : NumPy (implémentations from scratch), matplotlib · **Niveau** : intermédiaire (post socle ML) · **CPU** : oui

## Pourquoi cette série

Le socle [`02-ML-Cours`](../02-ML-Cours/README.md) laisse un chaînon ouvert. La descente de
gradient y est ouverte à la main ([2.2](../02-ML-Cours/2.2-Descente-de-gradient.ipynb)) — mais
sur **une droite** ; le premier réseau de neurones de la formation
([2.9](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)) est entraîné en PyTorch **boîte
noire** : `loss.backward()` et tout suit. Entre les deux, personne n'a écrit la
**rétropropagation** à la main — l'étape où l'on comprend réellement *pourquoi* un réseau apprend.

Cette série ouvre cette mécanique, un concept par notebook, avec une discipline constante :
**from scratch PUIS framework**. Chaque mécanisme est d'abord implémenté en NumPy pur (sans
autograd), **vérifié** (gradient numérique par différence finie, parité pas-à-pas avec
l'équivalent PyTorch), et seulement ensuite relié à l'API PyTorch que consomment nos autres
séries (RL, PostTraining, ML-Training-Pipeline). L'entraînement final du 2.9 et les
`optimizer = Adam(...)` des séries appliquées deviennent lisibles par construction.

## Vue d'ensemble

| Notebook | Sujet | Concept-phare | Validation |
|----------|-------|---------------|------------|
| [3.1-Retropropagation](3.1-Retropropagation.ipynb) | Le MLP et la rétropropagation à la main (NumPy pur, sans autograd) | **Le gradient vérifié** : différence finie vs analytique, parité exacte avec PyTorch | écart 1,3e-11 (seuil 1e-6) ; loss initiale, premier pas et trajectoire 3000 iters identiques à 1,1e-16 près ; init nulle = gradient nul (0,500 figé) |
| [3.2-Optimisateurs](3.2-Optimisateurs.ipynb) | Momentum, Adagrad, RMSProp, Adam et schedules, écrits en NumPy pur puis validés pas à pas contre `torch.optim` | **La parité exacte** : les 5 mises à jour sont celles de torch | GD/momentum/Adam à 1,11e-16, Adagrad bit-à-bit (0,00e+00), RMSProp à 2,22e-16 (float64, 1 pas) ; Beale : 5 trajectoires superposées (facteur 200 entre lr utilisables) ; MLP du 3.1 : 5 optimisateurs × 3 graines (RMSProp 0,059 < Adam 0,061 < … < GD 0,070) ; schedules : coût en full-batch déterministe, gain sous le plancher de bruit en mini-batch |
| [3.3-Modeles-Generatifs](3.3-Modeles-Generatifs.ipynb) | VAE, GAN et DDPM (diffusion) entraînés sur une même cible 2D à 4 modes (mélange de Gaussiennes, PyTorch CPU) puis comparés — ELBO vs adversarial vs débruitage | **Le compromis qualité/diversité** : 4 mécanismes génératifs sur les mêmes métriques (couverture de modes, entropie effective), le GMM empirique en référence « modèle exact » | médiane sur 3 graines (budget de pas commun) : GMM cov 4/4 ESS 3,96 · VAE cov 4/4 ESS 3,95 · GAN cov 3/4 ESS 2,99 (perte de diversité, un mode jamais couvert) · Diff cov 4/4 ESS 1,62 (couvre mais sous-échantillonne le mode le plus faible) — verdict nuancé, pas de « gagnant » unique |
| [3.5-Phenomenes-de-Generalisation](3.5-Phenomenes-de-Generalisation.ipynb) | Grokking et double descente reproduits en NumPy pur (MLP à embeddings + Adam à la main), confrontés à la borne PAC du 2.8 | **Le phénomène sans la boîte noire** : mémorisation → transition abrupte, et le W de la double descente | garde gradient ≤ 1e-6 (embeddings inclus) ; grok mesuré : train saturé ~500 pas, test 100 % des dizaines de milliers de pas plus tard (wd = 1) ; contre-témoin wd = 0 ; double descente : pic au seuil M ≈ n (×5 le creux), asymptote moderne sous le creux classique, 20 graines |

## Feuille de route

La suite est planifiée (issues ouvertes) : théorie de l'information appliquée — entropie, KL,
cross-entropy (#12420) ; régularisation — dropout, weight decay, early stopping (#12409) ;
attention et transformer jusqu'à un mini-GPT entraîné in notebook (#12410). Le fil
directeur ne change pas : chaque mécanisme écrit à la main, vérifié contre torch, puis
consommé via l'API officielle.

## Prérequis

- [02-ML-Cours](../02-ML-Cours/README.md) en entier — en particulier [2.2 (descente de
  gradient)](../02-ML-Cours/2.2-Descente-de-gradient.ipynb), [2.8 (théorie PAC, la borne que
  ce notebook confronte)](../02-ML-Cours/2.8-Theorie-PAC.ipynb) et
  [2.9 (le grokking boîte noire que le 3.5 rouvre à la main)](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)
- NumPy niveau [1.2](../01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb)
  (produits matriciels, broadcast)

## Environnement

```bash
pip install numpy matplotlib
```

Tous les notebooks tournent sur CPU en moins de dix minutes.
