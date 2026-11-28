# Voix : comparer, distribuer et évaluer

[← Applications audio](../README.md) | [↑ Audio](../../README.md)

Cette sous-série traite la voix synthétique sous trois angles : comparer les moteurs TTS, choisir une voix pour un personnage et évaluer la qualité perçue. Elle complète le [parcours audiobook](../04-Audiobook/README.md) : ici, la voix devient l'objet d'étude et de mesure, plutôt qu'une étape parmi d'autres d'une chaîne de production.

## Comment lire ce README — Découverte

Suivez l'ordre de la table pour passer de la comparaison de moteurs au casting, puis à l'évaluation subjective. La grille MOS est un protocole à compléter par l'écoute : les exemples de notes du carnet servent à comprendre l'agrégation, pas à remplacer un jugement d'auditeur.

## Parcours principal — Découverte

| Notebook | Ce qu'on y apprend | Place dans le parcours |
|---|---|---|
| [04-7 — Benchmark de voix TTS](Audio-04-7-TTS-Voice-Benchmark-Python.ipynb) | Comparer des systèmes et des rendus de synthèse vocale dans un cadre commun. | Point de départ pour situer les moteurs et leurs voix. |
| [04-9 — Voice casting](Audio-04-9-Voice-Casting-Python.ipynb) | Associer une voix à un personnage et raisonner sur la distribution vocale d'un texte. | Applique le choix de voix au pipeline narratif. |
| [04-19 — Évaluation MOS](Audio-04-19-Evaluation-MOS-Python.ipynb) | Construire une évaluation subjective, agréger des notes et examiner l'incertitude et les auditeurs aberrants. | Approfondit l'évaluation de la qualité perçue. |

## Approfondissements — Pratique

### Comparer les moteurs

Le [benchmark 04-7](Audio-04-7-TTS-Voice-Benchmark-Python.ipynb) pose les bases de la comparaison : un système TTS ne se juge pas seulement à son nom ou à une sortie isolée, mais à l'écoute des rendus produits dans le contexte du carnet. Les services et modèles disponibles peuvent varier ; consultez sa configuration avant de lancer les expériences.

### Choisir une voix pour un personnage

[04-9](Audio-04-9-Voice-Casting-Python.ipynb) déplace la question de la qualité générale vers l'adéquation entre personnage, interprétation et voix. Pour replacer ce choix dans une chaîne complète, retournez au [pipeline audiobook](../04-Audiobook/README.md).

### Évaluer l'écoute avec un protocole

[04-19](Audio-04-19-Evaluation-MOS-Python.ipynb) présente une rubrique d'écoute et son agrégateur. Le protocole tient compte de l'ordre de présentation, de notes incohérentes et de l'incertitude associée aux scores ; les notes fictives du carnet illustrent le calcul, tandis qu'une véritable campagne nécessite des évaluations humaines. Les mesures automatiques présentées en complément répondent à des propriétés différentes et ne se substituent pas à l'écoute.

Les besoins logiciels, les services appelés et leurs conditions d'accès sont propres à chaque carnet. Les scores et rendus dépendent des voix, des modèles et des auditeurs utilisés ; ne les interprétez pas comme un classement universel.

## Pour aller plus loin — Recherche

- [Audiobook](../04-Audiobook/README.md) — intégrer casting, synthèse et compilation dans une production narrative.
- [Audio avancé](../../02-Advanced/README.md) — clonage vocal, prosodie expressive et conversion de timbre.
- [Applications audio](../README.md) — vue d'ensemble des workflows de production.
