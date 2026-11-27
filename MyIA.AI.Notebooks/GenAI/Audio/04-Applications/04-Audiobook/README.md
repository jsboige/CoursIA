# Audiobook : du texte à la voix

[← Applications audio](../README.md) | [↑ Audio](../../README.md)

Cette série suit la fabrication d'un audiobook à partir d'un texte littéraire. Le parcours part d'une orchestration de bout en bout, puis isole les étapes qui demandent un traitement propre : lecture et segmentation du texte, annotation prosodique, synthèse vocale et assemblage. Le carnet FishAudio rassemble ensuite ces éléments dans une chaîne intégrée. Pour comparer les voix ou travailler le casting par personnage, voir aussi la [sous-série Voix](../04-Voix/README.md).

## Comment lire ce README — Découverte

Le [carnet orchestrateur](Audio-04-6-Audiobook-Pipeline-Python.ipynb) donne la vue d'ensemble. Les carnets suivants approfondissent une étape précise ; ils peuvent se lire indépendamment, mais leur ordre suit la progression du pipeline. Le [capstone FishAudio](Audio-04-13-Audiobook-FishAudio-S2Pro-Python.ipynb) montre une architecture d'implémentation plus détaillée.

## Parcours principal — Découverte

| Notebook | Ce qu'on y apprend | Place dans le parcours |
|---|---|---|
| [04-6 — Pipeline audiobook](Audio-04-6-Audiobook-Pipeline-Python.ipynb) | Orchestrer l'analyse littéraire, le script à plusieurs voix, la synthèse TTS et la compilation. | Vue d'ensemble et point de départ ; certaines étapes sont volontairement simplifiées. |
| [04-8 — Lecture analytique](04-8-Lecture-Analytique.ipynb) | Examiner un texte, distinguer narration et dialogues, et préparer une structure exploitable par la suite. | Approfondit la préparation du texte. |
| [04-10 — Annotation prosodique](Audio-04-10-Annotation-Prosodique-Python.ipynb) | Annoter les répliques pour guider l'expression et le rythme de la voix générée. | Prépare un script expressif avant la synthèse. |
| [04-11 — Génération TTS](04-11-Generation-TTS.ipynb) | Générer des segments parlés et comparer les choix de synthèse employés par le pipeline. | Produit les segments audio. |
| [04-12 — Compilation audio](Audio-04-12-Compilation-Audio-Python.ipynb) | Assembler les segments, gérer les transitions et préparer le fichier final. | Termine la chaîne de production. |
| [04-13 — Audiobook FishAudio S2-Pro](Audio-04-13-Audiobook-FishAudio-S2Pro-Python.ipynb) | Suivre une chaîne intégrée fondée sur FishAudio, ses annotations prosodiques et la vérification du résultat. | Capstone : relie les étapes dans une architecture plus complète. |

## Approfondissements — Pratique

### Préparer le texte et les voix

Commencez par [04-6](Audio-04-6-Audiobook-Pipeline-Python.ipynb) pour comprendre les rôles des étapes, puis lisez [04-8](04-8-Lecture-Analytique.ipynb) pour examiner la lecture analytique du texte. Le choix et la comparaison des moteurs vocaux sont traités dans la [sous-série Voix](../04-Voix/README.md), qui complète le casting par personnage.

### Annoter, synthétiser, compiler

[04-10](Audio-04-10-Annotation-Prosodique-Python.ipynb) prépare les indications d'expression ; [04-11](04-11-Generation-TTS.ipynb) les met en voix ; [04-12](Audio-04-12-Compilation-Audio-Python.ipynb) assemble le résultat. Le [capstone 04-13](Audio-04-13-Audiobook-FishAudio-S2Pro-Python.ipynb) permet ensuite de voir comment ces responsabilités s'articulent dans une chaîne intégrée.

Les carnets utilisent des services et bibliothèques différents selon l'étape. Consultez chaque notebook pour ses dépendances, sa configuration et les conditions d'accès aux modèles ou API. Les sorties générées dépendent de ces services et de leur configuration ; elles ne garantissent pas un rendu identique sur une autre machine.

## Pour aller plus loin — Recherche

- [Applications audio](../README.md) — autres workflows de production et sous-séries.
- [Voix](../04-Voix/README.md) — benchmark TTS, casting et évaluation subjective.
- [Audio avancé](../../02-Advanced/README.md) — synthèse vocale, clonage et traitements complémentaires.
