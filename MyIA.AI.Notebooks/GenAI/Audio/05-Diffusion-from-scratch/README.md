# Diffusion audio — construire les briques

[← Applications audio](../04-Applications/) | [↑ Audio](../README.md) | [→ Modèles SOTA](../06-Diffusion-SOTA/README.md)

Cette série pédagogique descend sous le niveau des modèles pré-entraînés pour examiner les composants d'une génération audio par diffusion. Elle relie une représentation latente, le processus de débruitage et le vocodeur qui transforme une représentation en signal écoutable. Pour comparer ces briques aux systèmes entraînés et aux modèles prêts à l'emploi, poursuivez avec [Diffusion SOTA](../06-Diffusion-SOTA/README.md).

## Comment lire ce README — Découverte

Commencez par le carnet de diffusion latente, qui construit le chemin de génération, puis passez au vocodeur pour comprendre la conversion de représentations audio en forme d'onde. L'objectif est d'examiner les mécanismes et leurs rôles, non d'obtenir un équivalent miniature des systèmes de production.

## Parcours principal — Découverte

| Notebook | Ce qu'on y apprend | Place dans le parcours |
|---|---|---|
| [05-1 — Audio diffusion latente, de zéro](Audio-05-1-AudioDiffusion-Latent-From-Scratch-Python.ipynb) | Construire en PyTorch et torchaudio une démonstration de diffusion dans un espace latent audio. | Introduit la représentation et le processus génératif. |
| [05-2 — Vocodeur de zéro](Audio-05-2-Vocoder-From-Scratch-Python.ipynb) | Étudier les composants d'un vocodeur de type HiFi-GAN, ses générateurs, discriminateurs et fonctions de perte. | Complète la génération par le passage vers un signal audio. |

## Approfondissements — Pratique

### De la diffusion à l'audio

[05-1](Audio-05-1-AudioDiffusion-Latent-From-Scratch-Python.ipynb) sert de parcours guidé dans une implémentation pédagogique : il aide à repérer ce que représentent l'espace latent et les étapes de débruitage dans un pipeline audio. Il ne faut pas le confondre avec l'exécution d'un grand modèle pré-entraîné, abordée dans la [série SOTA](../06-Diffusion-SOTA/README.md).

### Comprendre le rôle du vocodeur

[05-2](Audio-05-2-Vocoder-From-Scratch-Python.ipynb) explore la famille HiFi-GAN à travers ses composants et ses objectifs d'apprentissage. Il complète le premier carnet en isolant une autre question : comment produire une forme d'onde à partir d'une représentation intermédiaire. Consultez le notebook pour ses dépendances, son mode d'exécution et les limites de sa démonstration.

## Pour aller plus loin — Recherche

- [Diffusion SOTA](../06-Diffusion-SOTA/README.md) — comparer des modèles audio pré-entraînés.
- [Applications audio](../04-Applications/README.md) — tâches de production et d'analyse.
- [Audio](../README.md) — carte des séries et parcours du domaine.
