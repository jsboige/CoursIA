# `_archive/` — 03-DeepLearning

Registre de disposition (convention `_archive/`, cf
[docs/reference/_archive-convention.md](../../../../../docs/reference/_archive-convention.md)).
Chaque ligne dit par quoi le carnet a été supplanté et où le verdict est consigné.

| Fichier | Verdict | Supplété par | Verdict consigné dans |
|---------|---------|--------------|------------------------|
| `3.9f-Compression-Pruning-SOTA.ipynb` | FUSÉ (2026-10-25) — contenu intégralement préservé, rien supprimé | [`3.9e-Compression-SOTA.ipynb`](../3.9e-Compression-SOTA.ipynb) — **Part B** (élagage `torch.nn.utils.prune`), même terrain ResNet-20 / CIFAR-10, mêmes instruments | #22395 étape 3 (plan 8 → 5), PR de la lane `myia-po-2024:CoursIA-2` |

**Mode de fusion.** 3.9f n'est pas un dead-end : son contenu — le paysage de l'élagage,
« la main » (magnitude pruning en dix lignes), `prune.l1_unstructured`, local vs global,
structuré, taille/vitesse et les trois exercices — est repris **verbatim** dans la **Part B**
du carnet fusionné `3.9e-Compression-SOTA.ipynb`, avec un seul entraînement de ResNet-20
partagé (preamble commun) et une ré-exécution complète. Le carnet est archivé ici comme
**preuve de préservation**, pas supprimé. Le volet quantization de l'ancien 3.9e est la
**Part A** du même carnet fusionné (l'ancien `3.9e-Compression-Quantization-SOTA.ipynb` est
supprimé, son contenu étant intégralement porté par le nouveau `3.9e-Compression-SOTA.ipynb`).
