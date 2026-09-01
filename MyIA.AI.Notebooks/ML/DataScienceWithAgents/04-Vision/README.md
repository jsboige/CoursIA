# 04-Vision — Vision par ordinateur : du neurone convolutif au transfer learning

[← DataScienceWithAgents (série parente)](../README.md) | [03-DeepLearning (prérequis)](../03-DeepLearning/README.md) | [Track2-GoogleADK (autre série)](../Track2-GoogleADK/README.md)

**Kernel** : Python 3 (`coursia-ml-training` compatible) · **Bibliothèques** : NumPy (implémentations from scratch), PyTorch (parité), matplotlib, Pillow · **Niveau** : intermédiaire (post 03-DeepLearning) · **CPU** : oui

## Pourquoi cette série

[`03-DeepLearning`](../03-DeepLearning/README.md) a ouvert la rétropropagation sur des **vecteurs** tabulaires : MLP, gradient vérifié, parité NumPy ↔ torch. Le passage à l'image demande une primitive nouvelle — le neurone **convolutif** — qui partage ses poids spatialement, et la question se pose immédiatement : quand on empile 20 couches convolutives, pourquoi le gradient s'effondre-t-il ? Et comment ResNet résout-il ce problème avec une addition résiduelle ?

Cette série suit la **même discipline que 03** : *from scratch PUIS framework, parité epsilon machine*. Chaque mécanisme est d'abord implémenté en NumPy pur (sans autograd), vérifié (gradient numérique par différence finie, parité pas-à-pas avec l'équivalent PyTorch), puis relié à l'API PyTorch que consomment les autres séries.

## Vue d'ensemble

| Notebook | Sujet | Concept-phare | Validation |
|----------|-------|---------------|------------|
| [4.1 — Le neurone convolutif from scratch](4.1-Conv-NumPy-Torch-Allclose.ipynb) | Conv2d NumPy pur (single + multi-canal), gradient vérifié par différence finie, parité epsilon machine avec `torch.nn.Conv2d`, pooling et invariance par translation | **La convolution n'est pas magique** : un produit scalaire local, partagé spatialement, parité NumPy/torch à epsilon machine | gradient analytique vs numérique : écart max 1e-10 ; multi-canal (3 in, 4 out) float64 : 5,33e-15 ; float32 : 1,91e-06 (précision BLAS CPU) ; invariance par translation mesurée pixel-à-pixel sur image réelle |
| 4.2 — ConvNet profonde : pourquoi les résiduelles *(PR suivante, voir feuille de route)* | Empiler 20 conv2d sans résiduelles (effondrement du gradient) vs avec résiduelles (gradient stable) | **Le skip-connection n'est pas un détail architectural** : c'est le mécanisme qui rend les réseaux profonds entraînables. **C'est le même bloc que l'attention pré-norme dans [3.4](../03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb)** | normes de gradient par couche (1 réseau profond / 1 résiduel) ; accuracy CIFAR-10 sous-ensemble (5 classes, 5000 images) ; cross-ref explicite 3.4 ↔ 4.2 |
| 4.3 — Transfer learning ResNet *(PR suivante, voir feuille de route)* | Charger ResNet18 pré-entraîné ImageNet, remplacer la tête, fine-tuner sur un petit dataset français | **Le feature extractor pré-entraîné est réutilisable** : gelé (frozen) ou fine-tuné, sur combien de paramètres et combien d'epochs ? | ResNet18 backbone gelé : 11,2 M params (98,6 % du total) ; accuracy val sous-ensemble FR (10 classes) ; comparaison frozen vs fine-tuned (3 seeds, DM-test) |

## Prérequis

- [`03-DeepLearning`](../03-DeepLearning/README.md) en entier — en particulier [3.4 (Attention-Transformer from scratch)](../03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb) qui partage le mécanisme résiduel.
- NumPy niveau [`01-PythonForDataScience/1.2`](../01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) (broadcast, produits matriciels).
- PyTorch CPU (installé via `pip install torch torchvision`).

## Environnement

```bash
pip install numpy matplotlib torch torchvision pillow
```

L'entraînement des deux notebooks de cette série reste **borné CPU** (sous-ensembles CIFAR-10 et dataset FR, < 10 min/notebook). Les seuils d'entraînement sont calibrés pour la démonstration pédagogique, pas pour la performance ImageNet — voir les notebooks pour les budgets exacts par époque et par taille de sous-ensemble.

## Lien avec les autres séries

- **`03-DeepLearning` ↔ 04-Vision** : la résiduelle du 4.2 est exactement le bloc pré-norme du mini-GPT du 3.4. C'est cette convergence qui justifie le titre de la série parente *DataScienceWithAgents* : du MLP tabulaire au Transformer en passant par le CNN, **les mêmes primitives** (forward, backward, résiduelle) se réécrivent sans surprise.
- **`Track2-GoogleADK` ↔ 04-Vision** : les notebooks de Track2 chargent des modèles pré-entraînés via des outils ADK ; le 4.3 est la version *from scratch* de la même idée (ResNet18 pré-entraîné, sans orchestration agentique).

## Feuille de route

L'Epic #12422 *« Série Vision 04 (à décider) — Évolution des architectures CNN »* est livrée par cette série :
- 4.1 — le neurone convolutif from scratch (cette PR)
- 4.2 — pourquoi la profondeur échoue (PR suivante)
- 4.3 — transfer learning ResNet (PR suivante)

Chaque notebook est atomique (1 sujet vérifiable, < 3000 lignes, ≤ 15 fichiers), avec outputs commités (C.2) et ≥ 3 exercices par notebook (C.1, jamais `raise NotImplementedError`).
