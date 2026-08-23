# 03-DeepLearning — Le deep learning from scratch : ouvrir la boîte noire couche par couche

[← DataScienceWithAgents (série parente)](../README.md) | [02-ML-Cours (prérequis)](../02-ML-Cours/README.md)

**Kernel** : Python 3 · **Bibliothèques** : NumPy (implémentations from scratch), PyTorch (comparaisons), scikit-learn (données) · **Niveau** : intermédiaire (post socle ML) · **CPU** : oui

## Pourquoi cette série

Le socle [`02-ML-Cours`](../02-ML-Cours/README.md) laisse un chaînon ouvert. La descente de
gradient y est ouverte à la main ([2.2](../02-ML-Cours/2.2-Descente-de-gradient.ipynb)) — mais
sur **une droite** ; le premier réseau de neurones de la formation
([2.9](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)) est entraîné en PyTorch **boîte
noire** : `loss.backward()` et tout suit. Entre les deux, personne n'a écrit la **rétropropagation**
à la main — l'étape où l'on comprend réellement *pourquoi* un réseau apprend.

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

## Feuille de route

La suite est planifiée (issues ouvertes) : théorie de l'information appliquée — entropie, KL,
cross-entropy (#12420) ; optimisateurs — momentum, Adagrad, RMSProp, Adam, schedules, sur le MLP
du 3.1 (#12408) ; régularisation — dropout, weight decay, early stopping (#12409) ; attention et
transformer jusqu'à un mini-GPT entraîné in notebook (#12410) ; grokking et double descent
(#12414). Le fil directeur ne change pas : chaque mécanisme écrit à la main, vérifié contre
torch, puis consommé via l'API officielle.

## Prérequis

- [02-ML-Cours](../02-ML-Cours/README.md) en entier — en particulier [2.2 (descente de
  gradient)](../02-ML-Cours/2.2-Descente-de-gradient.ipynb), [2.3 (régression logistique, la
  cross-entropy avant le réseau)](../02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb) et
  [2.9 (le réseau boîte noire que cette série ouvre)](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)
- NumPy niveau [1.2](../01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb)
  (produits matriciels, broadcast)

## Environnement

```bash
pip install numpy scikit-learn matplotlib torch
```

Tous les notebooks tournent sur CPU en moins de trois minutes.
