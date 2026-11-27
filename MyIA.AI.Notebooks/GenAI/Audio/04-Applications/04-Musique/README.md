# Musique : comprendre, transcrire et séparer

[← Applications audio](../README.md) | [↑ Audio](../../README.md)

Cette sous-série aborde plusieurs tâches complémentaires autour du signal musical : représenter et retrouver des extraits, convertir l'audio en partition, analyser tempo et harmonie, détecter les notes, puis séparer les sources. Le fil relie les modèles appris aux méthodes classiques et insiste sur la qualité des mesures : une métrique de séparation se comprend aussi en étudiant son point de référence.

## Comment lire ce README — Découverte

La table suit l'ordre des identifiants `04-NN`, pas un classement par famille de modèles. Pour une première exploration, commencez par [MERT2](04-15-MERT2-Music-Understanding.ipynb), puis choisissez une tâche : partition globale avec [SheetSage2](04-16-SheetSage2-Audio-To-Score.ipynb), analyse musicale classique avec [MIR](04-17-MIR-Classique.ipynb), détection des notes avec [basic-pitch](04-18-Basic-Pitch-Transcription.ipynb), ou séparation mesurée avec [Demucs](04-20-Separation-Avancee-Qualite.ipynb).

## Parcours principal — Découverte

| Notebook | Ce qu'on y apprend | Place dans le parcours |
|---|---|---|
| [04-15 — MERT2 : comprendre la musique](04-15-MERT2-Music-Understanding.ipynb) | Explorer des représentations audio, la similarité et la recherche d'extraits, puis tester ce que les embeddings retiennent. | Point de départ côté représentation et compréhension. |
| [04-16 — SheetSage2 : audio vers partition](04-16-SheetSage2-Audio-To-Score.ipynb) | Transformer un enregistrement en informations musicales symboliques et confronter les prédictions à une référence connue. | Transcription globale vers une partition exploitable. |
| [04-17 — MIR classique](04-17-MIR-Classique.ipynb) | Estimer le tempo, la tonalité et les accords avec des descripteurs et méthodes classiques. | Socle de traitement du signal, en regard des modèles neuronaux. |
| [04-18 — Transcription basic-pitch](04-18-Basic-Pitch-Transcription.ipynb) | Repérer les notes, leurs hauteurs et leurs instants, puis examiner précision, rappel et seuils de détection. | Transcription note à note ; approche légère exécutable sur CPU. |
| [04-20 — Séparation avancée et qualité](04-20-Separation-Avancee-Qualite.ipynb) | Comparer des modèles de séparation sur une piste accompagnée de stems de référence et analyser les résultats par source. | Évaluation de moteurs sur un enregistrement réel. |
| [04-21 — Contre-épreuve SI-SDR](04-21-SI-SDR-Contre-Epreuve.ipynb) | Étalonner la métrique de séparation sur un mélange construit à partir de références exactes et observer l'effet du ratio d'énergie. | Complément méthodologique : interpréter le zéro de la mesure avant de classer les modèles. |

## Approfondissements — Pratique

### Représentations et transcription symbolique

[MERT2](04-15-MERT2-Music-Understanding.ipynb) examine les embeddings et leurs usages pour rapprocher des extraits. [SheetSage2](04-16-SheetSage2-Audio-To-Score.ipynb) vise une représentation symbolique plus globale : les sorties sont comparées à une vérité terrain connue. Pour un autre niveau de granularité, [basic-pitch](04-18-Basic-Pitch-Transcription.ipynb) cherche les événements note par note et permet d'observer l'effet des seuils de son décodeur.

### Situer les méthodes classiques

[MIR classique](04-17-MIR-Classique.ipynb) fournit un point de comparaison interprétable pour le tempo, la tonalité et les accords. Il aide à distinguer une mesure calculée à partir de caractéristiques du signal d'une prédiction apprise par un modèle.

### Séparation et mesure

[04-20](04-20-Separation-Avancee-Qualite.ipynb) compare des séparateurs sur des stems de référence ; [04-21](04-21-SI-SDR-Contre-Epreuve.ipynb) revient sur l'interprétation de SI-SDR à l'aide de mélanges dont les composantes sont connues. Lire les deux dans cet ordre sépare la comparaison des systèmes de l'étalonnage de la métrique utilisée pour les comparer.

Les carnets de compréhension et de séparation peuvent demander le téléchargement de poids ou un GPU ; les dépendances et licences sont précisées dans chaque notebook. Le carnet basic-pitch décrit une voie CPU. Vérifiez les conditions de réutilisation des poids et des données avant tout usage hors apprentissage.

## Pour aller plus loin — Recherche

- [Applications audio](../README.md) — contexte et autres cas d'usage.
- [Audio avancé](../../02-Advanced/README.md) — génération musicale, MIDI et séparation introductive.
- [Orchestration audio](../../03-Orchestration/README.md) — comparaison et assemblage de modèles audio.
