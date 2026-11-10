# Audio avancé : voix, musique et séparation

[← Audio Foundation](../01-Foundation/) | [↑ Audio](../README.md) | [→ Audio Orchestration](../03-Orchestration/)

Cette série intermédiaire explore trois façons de travailler le son : synthétiser une voix, générer de la musique et séparer les sources d'un enregistrement. Elle s'adresse aux personnes à l'aise avec Python et les bases du traitement audio ; la [série Foundation](../01-Foundation/) introduit notamment la synthèse vocale et l'écoute des résultats. Pour le fil rouge podcast, on peut produire une narration, créer un habillage musical, puis séparer ou remixer des pistes.

## Comment lire ce README — Découverte

Le dépôt propose plusieurs vitesses de lecture : [choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture). Parcourez la table pour choisir une technique ; utilisez les itinéraires et approfondissements pour relier les carnets ; passez à [Audio Orchestration](../03-Orchestration/) pour comparer et assembler les modèles.

## Parcours principal — Découverte

Les numéros ci-dessous sont les étapes de cette sous-série. Elles présentent des outils complémentaires ; il n'est pas nécessaire d'installer tous les modèles pour suivre un itinéraire.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Chatterbox TTS](02-1-Chatterbox-TTS.ipynb) | Synthétiser une voix et faire varier expressivité, guidance et conditionnement vocal. | Intermédiaire | [Voix](#voix) |
| 2 | [XTTS : clonage vocal](02-2-XTTS-Voice-Cloning.ipynb) | Conditionner une voix par un extrait, changer de langue et examiner la similarité du locuteur. | Intermédiaire | [Voix](#voix) |
| 3 | [MusicGen](02-3-MusicGen-Generation.ipynb) | Générer de la musique instrumentale à partir d'un texte ou d'une mélodie de référence et explorer le sampling. | Intermédiaire | [Musique](#musique) |
| 4 | [Demucs](02-4-Demucs-Source-Separation.ipynb) | Séparer voix, batterie, basse et autres sources, visualiser et remixer les pistes ; examiner le SDR. | Intermédiaire | [Séparation](#séparation) |
| 5 | [Gateway TTS multi-modèles](02-5-Multi-Model-TTS-Gateway.ipynb) | Interroger un service de synthèse, contrôler sa disponibilité et comparer les moteurs déployés. | Intermédiaire | [Voix](#voix) |
| 6 | [Génération MIDI](02-6-MIDI-Generation.ipynb) | Produire et continuer des séquences symboliques, puis les synthétiser avec FluidSynth. | Intermédiaire | [Musique](#musique) |
| 7 | [YuE2 : chansons complètes](02-7-YuE2-Song-Generation.ipynb) | Passer des paroles et d'un style à une chanson, puis explorer reprise et édition d'une partition. | Avancé | [Musique](#musique) |
| 8 | [TTS expressif](02-8-Expressive-TTS.ipynb) | Expérimenter les tags de prosodie et comparer Fish S2 Pro et Dia TTS. | Avancé | [Voix](#voix) |
| 9 | [ACE-Step](02-9-AceStep-Music-Generation.ipynb) | Générer une chanson à partir de paroles structurées et étudier les paramètres de génération. | Intermédiaire | [Musique](#musique) |

## Approfondissements — Pratique

### Voix

Commencez par [Chatterbox](02-1-Chatterbox-TTS.ipynb) : fixez le texte et faites varier `exaggeration` ou `cfg_weight` pour distinguer expressivité et fidélité au conditionnement. [XTTS](02-2-XTTS-Voice-Cloning.ipynb) prolonge cette expérience par le clonage sans entraînement supplémentaire et la comparaison entre langues. La similarité calculée et l'écoute répondent à des questions différentes ; la qualité et la durée de l'extrait de référence influencent le résultat.

Le [gateway](02-5-Multi-Model-TTS-Gateway.ipynb) déplace la question vers une application : vérifier la disponibilité d'un service, comparer les moteurs effectivement déployés et choisir un routage. Le carnet [TTS expressif](02-8-Expressive-TTS.ipynb) explore ensuite les tags de prosodie, Fish S2 Pro et Dia ; il suppose déjà les notions de synthèse des premiers carnets. Utilisez une voix de référence uniquement avec le consentement du locuteur et vérifiez les droits d'utilisation des modèles et des enregistrements.

### Musique

[MusicGen](02-3-MusicGen-Generation.ipynb) part d'une description ou d'une mélodie pour produire un signal sonore instrumental. Le carnet [MIDI](02-6-MIDI-Generation.ipynb) produit au contraire des événements musicaux modifiables : le rendu audio demande ensuite un synthétiseur et une banque de sons. Cette distinction aide à choisir entre un son directement exploitable et une partition que l'on peut retravailler.

Pour ajouter des paroles, [ACE-Step](02-9-AceStep-Music-Generation.ipynb) introduit les balises de structure et l'effet des paramètres de génération. [YuE2](02-7-YuE2-Song-Generation.ipynb) va plus loin : planification symbolique, génération sémantique, synthèse et décodage, ainsi que reprise et édition. Son carnet demande Linux et un GPU adapté ; les poids YuE2-3B sont sous licence **CC BY-NC 4.0**, qui interdit l'usage commercial. Consultez le carnet pour les conditions et les avis tiers avant toute réutilisation.

### Séparation

[Demucs](02-4-Demucs-Source-Separation.ipynb) prend le chemin inverse de la génération : il extrait des pistes d'un mélange. L'exemple synthétique permet d'examiner les sources et la métrique SDR ; sur un enregistrement réel, l'absence de sources de référence complique cette évaluation. La séparation peut laisser des artefacts et ne donne pas automatiquement les pistes originales. Utilisez des enregistrements dont vous détenez les droits nécessaires.

## Installation et limites — Pratique

Chaque carnet indique ses dépendances propres et la configuration de ses modèles. Les générations locales demandent généralement un GPU NVIDIA et le téléchargement de poids ; la mémoire et le temps dépendent du modèle, de sa variante et de la machine. Demucs et le carnet MIDI décrivent aussi une exécution CPU, plus lente. Le carnet MIDI nécessite en outre FluidSynth ; YuE2 précise sa configuration Linux/GPU et ACE-Step décrit le déchargement vers la RAM pour réduire l'occupation GPU.

Le gateway et certaines expériences TTS appellent des **services** : leur disponibilité, les modèles déployés et les éventuels identifiants doivent être vérifiés avant l'exécution. Un message de démonstration ou une section sautée faute de dépendance ne constitue pas une génération réelle. Les sorties enregistrées illustrent une configuration donnée ; elles ne garantissent ni la même performance ni la même qualité sur une autre machine.

## Pour aller plus loin — Recherche

La [comparaison multi-modèles](../03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb) met les approches en regard ; la [série Audio](../README.md) présente les autres modules et leurs applications. Pour un inventaire à jour des carnets, consultez le [catalogue du dépôt](../../../../COURSE_CATALOG.generated.md).

## Ressources — Référence

- [Documentation Audio principale](../README.md)
- [Environnement GenAI](../../00-GenAI-Environment/README.md)
- Les carnets citent les projets et publications propres à chaque modèle, ainsi que les licences et conditions utiles à leur utilisation.
