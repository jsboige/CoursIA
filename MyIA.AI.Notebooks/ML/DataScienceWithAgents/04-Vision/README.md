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
| [4.2 — ConvNet profonde : pourquoi les résiduelles](4.2-ConvNet-Profonde-Residuelles.ipynb) | 20 conv2d empilées nues (effondrement du gradient), skip naïf (gradient réparé mais passe avant qui dérive), bloc pré-norme (les deux réparés), même protocole transposé à 20 blocs d'attention, puis accuracy CIFAR-10 sur 3 graines | **Le skip-connection n'est pas un détail architectural** : c'est le mécanisme qui rend les réseaux profonds entraînables. **C'est le même bloc que l'attention pré-norme dans [3.4](../03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb)** | rapport de gradients `g_0/g_19` : `plain` 2,16e-08 contre `prenorm` 1,01 ; effondrement exponentiel en la profondeur (D = 4 → 28 : 1,47e-01 → 2,02e-12) ; `res_naif` répare le gradient mais `|h|` dérive d'un facteur 88 et la perte initiale monte à 17,4 au lieu de `ln 5` ; attention nue : rapport **plat** (0,92) alors que `|h|` est divisé par 2,1e+07 ; CIFAR-10 (5 classes, 3 graines) : `prenorm` 62,0 % ± 2,8 contre `plain` 34,0 % ± 10,0, soit +28,0 points pour un bruit de ±10,4 (rapport 2,7) |
| [4.3 — Transfer learning : réutiliser un ResNet18 pré-entraîné](4.3-TransferLearning-ResNet.ipynb) | Charger ResNet18 pré-entraîné ImageNet, greffer une tête (5 130 params), comparer gelé vs fine-tuné sur EuroSAT (Sentinel-2, 10 classes d'occupation du sol, 80+30 imgs/classe), 3 graines appariées + test de permutation des signes | **Le feature extractor pré-entraîné est réutilisable — et le prix de ne pas l'adapter se mesure** : le gelé fait déjà ~89 % ; le fine-tuné ajoute ~6 points, mais seulement avec un taux décroissant (à taux constants, l'optimiseur oscille et finit sous le gelé) | backbone gelé 11,18 M params (99,95 % du réseau) ; gelé 89,3 % ± 1,3 (5 130 params entraînés) vs fine-tuné 95,6 % ± 0,8 (Adam différencié 3e-4/3e-3, décroissance x0,3/époque, batch 64, 5 époques) ; écart apparié +6,2 pts sur 3 graines (rapport signal/bruit 3,2, p = 0,250 au test de permutation — plancher 0,125 à n = 3) |

## Prérequis

- [`03-DeepLearning`](../03-DeepLearning/README.md) en entier — en particulier [3.4 (Attention-Transformer from scratch)](../03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb) qui partage le mécanisme résiduel.
- NumPy niveau [`01-PythonForDataScience/1.2`](../01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) (broadcast, produits matriciels).
- PyTorch CPU (installé via `pip install torch torchvision`).

## Environnement

```bash
pip install numpy matplotlib torch torchvision pillow
```

L'entraînement des deux notebooks concernés (4.2 et 4.3) reste **borné CPU** (sous-ensemble CIFAR-10 pour 4.2 ; EuroSAT ~94 Mo au premier run pour 4.3 — cache partagé `~/.cache/coursia-datasets` ; < 10 min/notebook). Les seuils d'entraînement sont calibrés pour la démonstration pédagogique, pas pour la performance ImageNet — voir les notebooks pour les budgets exacts par époque et par taille de sous-ensemble. Mesure sur 4.2 : exécution complète des 48 cellules en 2 min 20 s sur CPU ; mesure sur 4.3 : exécution complète des 35 cellules en 6 min 29 s sur CPU (dont 4 min 45 s d'entraînements).

## Lien avec les autres séries

- **`03-DeepLearning` ↔ 04-Vision** : la résiduelle du 4.2 est exactement le bloc pré-norme du mini-GPT du 3.4. C'est cette convergence qui justifie le titre de la série parente *DataScienceWithAgents* : du MLP tabulaire au Transformer en passant par le CNN, **les mêmes primitives** (forward, backward, résiduelle) se réécrivent sans surprise.
- **`Track2-GoogleADK` ↔ 04-Vision** : les notebooks de Track2 chargent des modèles pré-entraînés via des outils ADK ; le 4.3 est la version *from scratch* de la même idée (ResNet18 pré-entraîné, sans orchestration agentique).

## Feuille de route

L'Epic #12422 *« Série Vision 04 (à décider) — Évolution des architectures CNN »* est livrée par cette série :
- 4.1 — [le neurone convolutif from scratch](4.1-Conv-NumPy-Torch-Allclose.ipynb) (livré)
- 4.2 — [pourquoi la profondeur échoue sans résiduelles](4.2-ConvNet-Profonde-Residuelles.ipynb) (livré)
- 4.3 — [transfer learning ResNet](4.3-TransferLearning-ResNet.ipynb) (cette PR)

Chaque notebook est atomique (1 sujet vérifiable, < 3000 lignes, ≤ 15 fichiers), avec outputs commités (C.2) et ≥ 3 exercices par notebook (C.1, jamais `raise NotImplementedError`).
