# Diffusion audio — comparer les modèles SOTA

[← Diffusion from scratch](../05-Diffusion-from-scratch/README.md) | [↑ Audio](../README.md)

Cette série examine des modèles audio pré-entraînés et leurs usages complémentaires : génération conditionnée par le texte avec AudioLDM, synthèse vocale avec HiFi-GAN, puis comparaison des résultats dans un carnet de synthèse. Elle fait suite aux [implémentations pédagogiques from scratch](../05-Diffusion-from-scratch/README.md) : on passe des mécanismes aux systèmes pré-entraînés, à leurs performances observées et aux compromis de leur utilisation.

## Comment lire ce README — Découverte

Lisez d'abord [AudioLDM](Audio-06-1-AudioLDM-SOTA-Comparison-Python.ipynb) pour la génération audio par diffusion, puis [HiFi-GAN](Audio-06-2-HiFiGAN-SOTA-Comparison-Python.ipynb) pour la synthèse vocale. Le carnet [A-vs-B](Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb) rassemble ensuite les comparaisons. Les tâches étant différentes, leurs sorties et mesures ne doivent pas être interprétées comme un classement direct de modèles interchangeables.

## Parcours principal — Découverte

| Notebook | Ce qu'on y apprend | Place dans le parcours |
|---|---|---|
| [06-1 — AudioLDM : génération audio](Audio-06-1-AudioLDM-SOTA-Comparison-Python.ipynb) | Utiliser un modèle pré-entraîné de diffusion audio conditionnée par le texte et examiner les effets des réglages de génération. | Première étude d'un générateur audio pré-entraîné. |
| [06-2 — HiFi-GAN : synthèse vocale](Audio-06-2-HiFiGAN-SOTA-Comparison-Python.ipynb) | Explorer un vocodeur pré-entraîné et observer les compromis de durée et de latence. | Étudie la synthèse vocale dans une tâche distincte de la génération AudioLDM. |
| [06-3 — Comparaison audio A-vs-B](Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb) | Mettre en regard les observations des expériences précédentes et lire leurs résultats de façon comparative. | Synthèse du parcours ; consulter le carnet pour le périmètre exact de la comparaison. |

## Approfondissements — Pratique

### Générer des sons avec AudioLDM

[06-1](Audio-06-1-AudioLDM-SOTA-Comparison-Python.ipynb) étudie un modèle de diffusion entraîné pour produire de l'audio à partir d'une description. Le carnet examine notamment les paramètres de guidance et les mesures spectrales, plutôt que de s'en tenir à une écoute isolée.

### Synthétiser la voix avec HiFi-GAN

[06-2](Audio-06-2-HiFiGAN-SOTA-Comparison-Python.ipynb) porte sur un vocodeur pré-entraîné. Ses mesures de durée et de latence éclairent le coût d'exécution, mais la synthèse vocale ne constitue pas la même tâche que la génération de scènes sonores d'AudioLDM.

### Rapprocher les observations

[06-3](Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb) reprend les comparaisons dans une vue de synthèse. Vérifiez dans ce carnet les conditions expérimentales et les critères utilisés avant de généraliser les résultats à d'autres modèles ou signaux.

Les expériences pré-entraînées peuvent télécharger des poids et demander un environnement matériel adapté. Les exigences, versions et conditions de licence sont précisées dans chaque notebook ; les performances dépendent de la configuration et ne se généralisent pas automatiquement à d'autres machines.

## Pour aller plus loin — Recherche

- [Diffusion from scratch](../05-Diffusion-from-scratch/README.md) — comprendre les briques pédagogiques sous-jacentes.
- [Audio avancé](../02-Advanced/README.md) — génération et traitement audio complémentaires.
- [Applications audio](../04-Applications/README.md) — autres tâches appliquées.
