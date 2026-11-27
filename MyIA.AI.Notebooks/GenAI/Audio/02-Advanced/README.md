# Audio avancé : voix, musique, effets sonores et séparation

[← Audio Foundation](../01-Foundation/) | [↑ Audio](../README.md) | [→ Audio Orchestration](../03-Orchestration/)

Cette série intermédiaire explore quatre façons de travailler le son : synthétiser une voix, générer de la musique, créer des effets sonores et des bruitages décrits en texte, puis séparer les sources d'un enregistrement. Le dernier carnet ferme le parcours côté compréhension : un LLM omni-modal qui écoute l'audio et répond en texte. Elle s'adresse aux personnes à l'aise avec Python et les bases du traitement audio ; la [série Foundation](../01-Foundation/) introduit notamment la synthèse vocale et l'écoute des résultats. Pour le fil rouge podcast, on peut produire une narration, créer un habillage musical, ajouter des ambiances sonores, puis séparer ou remixer des pistes.

## Comment lire ce README — Découverte

Le dépôt propose plusieurs vitesses de lecture : [choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture). Parcourez la table pour choisir une technique ; utilisez les itinéraires et approfondissements pour relier les carnets ; passez à [Audio Orchestration](../03-Orchestration/) pour comparer et assembler les modèles.

## Parcours principal — Découverte

Les numéros ci-dessous sont les étapes de cette sous-série. Elles présentent des outils complémentaires ; il n'est pas nécessaire d'installer tous les modèles pour suivre un itinéraire.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Chatterbox TTS](Audio-02-1-Chatterbox-TTS-Python.ipynb) | Synthétiser une voix et faire varier expressivité, guidance et conditionnement vocal. | Intermédiaire | [Voix](#voix) |
| 2 | [XTTS : clonage vocal](02-2-XTTS-Voice-Cloning.ipynb) | Conditionner une voix par un extrait, changer de langue et examiner la similarité du locuteur. | Intermédiaire | [Voix](#voix) |
| 3 | [MusicGen](02-3-MusicGen-Generation.ipynb) | Générer de la musique instrumentale à partir d'un texte ou d'une mélodie de référence et explorer le sampling. | Intermédiaire | [Musique](#musique) |
| 4 | [Demucs](02-4-Demucs-Source-Separation.ipynb) | Séparer voix, batterie, basse et autres sources, visualiser et remixer les pistes ; examiner le SDR. | Intermédiaire | [Séparation](#séparation) |
| 5 | [Gateway TTS multi-modèles](Audio-02-5-Multi-Model-TTS-Gateway-Python.ipynb) | Interroger un service de synthèse, contrôler sa disponibilité et comparer les moteurs déployés. | Intermédiaire | [Voix](#voix) |
| 6 | [Génération MIDI](Audio-02-6-MIDI-Generation-Python.ipynb) | Produire et continuer des séquences symboliques, puis les synthétiser avec FluidSynth. | Intermédiaire | [Musique](#musique) |
| 7 | [YuE2 : chansons complètes](Audio-02-7-YuE2-Song-Generation-Python.ipynb) | Passer des paroles et d'un style à une chanson, puis explorer reprise et édition d'une partition. | Avancé | [Musique](#musique) |
| 8 | [TTS expressif](02-8-Expressive-TTS.ipynb) | Expérimenter les tags de prosodie et comparer Fish S2 Pro et Dia TTS. | Avancé | [Voix](#voix) |
| 9 | [ACE-Step](Audio-02-9-AceStep-Music-Generation-Python.ipynb) | Générer une chanson à partir de paroles structurées et étudier les paramètres de génération. | Intermédiaire | [Musique](#musique) |
| 10 | [Effets sonores AudioLDM2](Audio-02-10-Effets-Sonores-AudioLDM2-Python.ipynb) | Générer des effets sonores à partir d'un texte, mesurer étapes, durée et guidance, puis discriminer un effet d'une musique. | Intermédiaire | [Effets sonores](#effets-sonores) |
| 11 | [AudioGen](Audio-02-11-Text-to-Audio-Bruitages-Python.ipynb) | Générer des scènes sonores décrites en texte et comparer le paradigme autoregressif à la diffusion d'[AudioLDM-S](../06-Diffusion-SOTA/06-1-AudioLDM-SOTA-Comparison.ipynb). | Intermédiaire | [Bruitages](#bruitages) |
| 12 | [RVC v2 : conversion de voix chantée](Audio-02-12-SVS-Singing-Voice-RVC-Python.ipynb) | Remplacer le timbre d'un chant en préservant la mélodie : charger un checkpoint, mesurer trajectoire f0, transposition et paramètre protect sur CPU, puis convertir une voix de parole (couple avant/après dans `assets/`). | Avancé | [Voix](#voix) |
| 13 | [LLM audio omni-modal](Audio-02-13-Audio-LLM-Omni-Modal-Qwen2Audio-Python.ipynb) | Écouter avec un LLM : charger Qwen2-Audio en int8 local (~9,5 Go de VRAM), mesurer compréhension, transcription et stabilité du contenu à travers la conversion de timbre (couple source/RVC), avec contrôle croisé Whisper, et le mettre en regard d'Audio Flamingo. | Avancé | [Compréhension](#compréhension) |
| 14 | [Transcription audio Qwen3](Audio-02-14-Transcription-Audio-Qwen3-Python.ipynb) | Transcrire la parole avec un moteur de la génération Qwen3, le confronter à un témoin hors famille Qwen et à la génération précédente, et lire l'écart sur le même signal. | Avancé | [Voix](#voix) |
| 15 | [Qwen3-Omni : écoute multimodale](Audio-02-15-Omni-Modal-Qwen3-Python.ipynb) | Poser une question en texte à un modèle omni-modal sur un extrait audio, chargé en 4 bits sur un GPU de 24 Go : distinguer l'axe du timbre, qui discrimine deux voix, de l'axe du contenu, qui ne les discrimine pas. | Avancé | [Voix](#voix) |

## Approfondissements — Pratique

### Voix

Commencez par [Chatterbox](Audio-02-1-Chatterbox-TTS-Python.ipynb) : fixez le texte et faites varier `exaggeration` ou `cfg_weight` pour distinguer expressivité et fidélité au conditionnement. [XTTS](02-2-XTTS-Voice-Cloning.ipynb) prolonge cette expérience par le clonage sans entraînement supplémentaire et la comparaison entre langues. La similarité calculée et l'écoute répondent à des questions différentes ; la qualité et la durée de l'extrait de référence influencent le résultat.

Le [gateway](Audio-02-5-Multi-Model-TTS-Gateway-Python.ipynb) déplace la question vers une application : vérifier la disponibilité d'un service, comparer les moteurs effectivement déployés et choisir un routage. Le carnet [TTS expressif](02-8-Expressive-TTS.ipynb) explore ensuite les tags de prosodie, Fish S2 Pro et Dia ; il suppose déjà les notions de synthèse des premiers carnets. La [conversion RVC v2](Audio-02-12-SVS-Singing-Voice-RVC-Python.ipynb) prend le chant enregistré pour point de départ : elle remplace le timbre en préservant la mélodie, mesurée note par note, sur CPU et avec un checkpoint de voix synthétique. Une seconde source — une voix de parole générée par le TTS [Kokoro](../01-Foundation/01-5-TTS-Local-ONNX.ipynb) — montre que le même moteur convertit chant et parole ; le couple avant/après est committé dans `assets/`. Utilisez une voix de référence uniquement avec le consentement du locuteur et vérifiez les droits d'utilisation des modèles et des enregistrements.

La [transcription Qwen3](Audio-02-14-Transcription-Audio-Qwen3-Python.ipynb) ferme la boucle côté perception : sur le même couple audio, un moteur de reconnaissance vocale de la génération Qwen3 est confronté à un témoin hors famille Qwen et à la génération précédente. Le dépôt ne documente pas le texte exact de ces extraits, donc le carnet ne note aucune transcription : il compare les moteurs sur le même signal, et mesure l'écart de génération plutôt que de le supposer.

Le carnet [Qwen3-Omni](Audio-02-15-Omni-Modal-Qwen3-Python.ipynb) va dans l'autre sens : il écoute. Un modèle omni-modal reçoit un extrait audio et une question, et répond en texte ; le carnet pose la même question aux deux fichiers du couple `assets/` et compare. Il montre que l'axe du timbre est décrit avec justesse et qu'il sépare les deux voix, tandis que l'axe du contenu est dégradé et ne les sépare pas — sur un signal que trois moteurs d'années différentes lisent mal. C'est le carnet à lire pour savoir ce qu'un moteur d'écoute restitue réellement, et pour mesurer le coût d'un tel moteur : un checkpoint de plus de trente milliards de paramètres, quantifié en 4 bits pour tenir dans la mémoire d'un GPU grand public.

### Musique

[MusicGen](02-3-MusicGen-Generation.ipynb) part d'une description ou d'une mélodie pour produire un signal sonore instrumental. Le carnet [MIDI](Audio-02-6-MIDI-Generation-Python.ipynb) produit au contraire des événements musicaux modifiables : le rendu audio demande ensuite un synthétiseur et une banque de sons. Cette distinction aide à choisir entre un son directement exploitable et une partition que l'on peut retravailler.

Pour ajouter des paroles, [ACE-Step](Audio-02-9-AceStep-Music-Generation-Python.ipynb) introduit les balises de structure et l'effet des paramètres de génération. [YuE2](Audio-02-7-YuE2-Song-Generation-Python.ipynb) va plus loin : planification symbolique, génération sémantique, synthèse et décodage, ainsi que reprise et édition. Son carnet demande Linux et un GPU adapté ; les poids YuE2-3B sont sous licence **CC BY-NC 4.0**, qui interdit l'usage commercial. Consultez le carnet pour les conditions et les avis tiers avant toute réutilisation.

### Effets sonores

[AudioLDM2](Audio-02-10-Effets-Sonores-AudioLDM2-Python.ipynb) génère des effets sonores décrits par le texte : aboiement, pluie sur une tôle, verre brisé. Le carnet mesure ce qui distingue un effet d'une musique — largeur de bande, hauteur du centroïde, densité d'attaques — et l'effet réel des paramètres de génération (étapes, durée, guidance, graine). Les poids `cvssp/audioldm2` sont sous licence **CC BY-NC-SA 4.0**, qui interdit l'usage commercial ; le carnet détaille en outre les deux correctifs de compatibilité requis sous transformers 5.x.

### Séparation

[Demucs](02-4-Demucs-Source-Separation.ipynb) prend le chemin inverse de la génération : il extrait des pistes d'un mélange. L'exemple synthétique permet d'examiner les sources et la métrique SDR ; sur un enregistrement réel, l'absence de sources de référence complique cette évaluation. La séparation peut laisser des artefacts et ne donne pas automatiquement les pistes originales. Utilisez des enregistrements dont vous détenez les droits nécessaires.

### Bruitages

[AudioGen](Audio-02-11-Text-to-Audio-Bruitages-Python.ipynb) génère des bruitages et des scènes sonores décrites en texte : un modèle autoregressif écrit l'audio comme une séquence de tokens de codec, conditionné par un encodeur de texte. Le carnet mesure le temps réel (RTF) et la mémoire occupée, chiffre l'effet de la température et du top-k sur la diversité, et compare le positionnement à la diffusion d'[AudioLDM-S](../06-Diffusion-SOTA/06-1-AudioLDM-SOTA-Comparison.ipynb) — textures rapides contre compositions multi-concepts — ainsi qu'à [MusicGen](02-3-MusicGen-Generation.ipynb), même moteur dédié à la musique. Les poids `audiogen-medium` sont soumis à leur propre licence sur Hugging Face.

### Compréhension

[Qwen2-Audio](Audio-02-13-Audio-LLM-Omni-Modal-Qwen2Audio-Python.ipynb) prend le chemin inverse de toute la série : au lieu de produire ou de transformer l'audio, le modèle **l'écoute** et répond en texte dans un tour de conversation. Le carnet charge le moteur réel en int8 local (~9,5 Go de VRAM, environ une minute à froid), pose trois épreuves mesurées — compréhension, transcription, stabilité du contenu à travers la conversion de timbre du carnet 02-12 — avec un contrôle croisé Whisper qui montre que la dégradation entendue est dans le signal, puis met l'architecture en regard d'Audio Flamingo (Kong et al. 2024), lu depuis la copie archivée au gisement bibliographique : tokens audio lus par le LLM contre attention croisée à porte. Les poids `Qwen2-Audio-7B-Instruct` sont soumis à leur propre licence sur Hugging Face.

## Installation et limites — Pratique

Chaque carnet indique ses dépendances propres et la configuration de ses modèles. Les générations locales demandent généralement un GPU NVIDIA et le téléchargement de poids ; la mémoire et le temps dépendent du modèle, de sa variante et de la machine. Demucs et le carnet MIDI décrivent aussi une exécution CPU, plus lente. Le carnet MIDI nécessite en outre FluidSynth ; YuE2 précise sa configuration Linux/GPU et ACE-Step décrit le déchargement vers la RAM pour réduire l'occupation GPU. AudioLDM2 documente ses deux correctifs de compatibilité pour transformers 5.x et tourne en float16 sous 2,5 Go de VRAM. La conversion RVC v2 s'exécute entièrement sur CPU via le kernel WSL `rvc-wsl` (environnement conda `rvc`, Python 3.10), avec un temps de conversion de l'ordre de deux fois la durée du signal. Le LLM audio omni-modal se charge en int8 via le kernel `python3` (env conda `coursia-canonical`) : ~9,5 Go de VRAM pour 8,4 Md de parametres, la quantification passant par `BitsAndBytesConfig` sous transformers 5.x.

Le gateway et certaines expériences TTS appellent des **services** : leur disponibilité, les modèles déployés et les éventuels identifiants doivent être vérifiés avant l'exécution. Un message de démonstration ou une section sautée faute de dépendance ne constitue pas une génération réelle. Les sorties enregistrées illustrent une configuration donnée ; elles ne garantissent ni la même performance ni la même qualité sur une autre machine.

Le carnet [Qwen3-Omni](Audio-02-15-Omni-Modal-Qwen3-Python.ipynb) exige un GPU NVIDIA d'au moins 24 Go de mémoire vidéo : le checkpoint officiel dépasse 65 Go en `bfloat16` et n'y tient qu'après quantification en 4 bits à la volée, opération dont le carnet mesure le temps de chargement. Le carnet note aussi ce que la quantification change : le modèle exécuté n'est plus exactement le checkpoint publié, et les erreurs de transcription peuvent être amplifiées.

## Pour aller plus loin — Recherche

La [comparaison multi-modèles](../03-Orchestration/Audio-03-1-Multi-Model-Audio-Comparison-Python.ipynb) met les approches en regard ; la [série Audio](../README.md) présente les autres modules et leurs applications. Pour un inventaire à jour des carnets, consultez le [catalogue du dépôt](../../../../COURSE_CATALOG.generated.md).

## Ressources — Référence

- [Documentation Audio principale](../README.md)
- [Environnement GenAI](../../00-GenAI-Environment/README.md)
- Les carnets citent les projets et publications propres à chaque modèle, ainsi que les licences et conditions utiles à leur utilisation.
