# Introduction Pratique à l'IA Générative

Ce document vous présente une introduction pratique aux principales applications de l'intelligence artificielle générative, avec des exercices concrets pour découvrir les technologies de génération d'images, de texte et de transcription audio.

## 1. Génération d'Images

### Vue d'ensemble des technologies

L'IA générative pour les images repose sur différents types de modèles, chacun ayant ses spécificités et avantages :

#### Types de modèles disponibles

**1. Modèles basés sur Stable Diffusion**
- Technologies les plus anciennes et éprouvées
- Génération rapide (quelques secondes par image)
- Écosystème riche avec des milliers de variantes
- Limitation : difficulté avec les prompts complexes
- Avantage : qualité artistique élevée avec les bons prompts

**2. Modèles de type Flux**
- Architecture plus récente, similaire à ChatGPT
- Temps de génération plus long (20 secondes ou plus)
- Meilleure compréhension des compositions complexes
- Promptage plus naturel et intuitif
- Écosystème de variantes en développement

**3. Solutions commerciales**
- ChatGPT (capacités de génération récemment améliorées)
- Midjourney (qualité reconnue, solution payante)

### Flux de travail recommandé

1. **Composition initiale** : Utiliser un modèle récent pour créer la structure de base
2. **Raffinement artistique** : Passer en mode image-to-image sur des modèles plus esthétiques
3. **Finitions** : Utiliser des logiciels traditionnels (Photoshop/Illustrator) pour les textes et détails

### Plateformes et outils recommandés

#### Modèles Flux et alternatives récentes
- **HiDream** : [https://hidream.org/](https://hidream.org/)
  - Modèle concurrent de Flux
  - Interface simple et efficace

- **Vivago AI** : [https://vivago.ai/img-generation?activeTab=text-to-image](https://vivago.ai/img-generation?activeTab=text-to-image)
  - Fonctionnalités additionnelles (payantes)
  - Interface utilisateur soignée

- **Recraft AI** : [https://www.recraft.ai](https://www.recraft.ai)
  - Modèle de type Flux
  - Nombreuses fonctionnalités d'édition

#### Modèles Stable Diffusion
- **Stable UI** : [https://aqualxx.github.io/stable-ui/](https://aqualxx.github.io/stable-ui/)
  - Interface collaborative
  - Accès à de nombreux modèles communautaires
  - Système de file d'attente rapide

- **Dezgo** : [https://dezgo.com/text2image/](https://dezgo.com/text2image/)
  - Application web bien conçue
  - Interface utilisateur intuitive

#### Plateformes officielles et catalogues
- **Flux Original** : [https://huggingface.co/spaces/black-forest-labs/FLUX.1-dev](https://huggingface.co/spaces/black-forest-labs/FLUX.1-dev)
- **Flux Redux** : [https://huggingface.co/spaces/black-forest-labs/FLUX.1-Redux-dev](https://huggingface.co/spaces/black-forest-labs/FLUX.1-Redux-dev)
- **CivitAI** : [https://civitai.com](https://civitai.com)
  - Catalogue complet des modèles légaux
  - Possibilité de tester directement en ligne
  - Milliers de variantes disponibles

### Conseils pratiques

- **Expérimentation** : Testez différents modèles pour comprendre leurs spécificités
- **Promptage** : Adaptez votre style de prompt selon le type de modèle
- **Workflow hybride** : Combinez plusieurs modèles selon leurs forces respectives
- **Intégration** : Utilisez l'IA comme point de départ, finalisez avec des outils traditionnels

## 2. Génération de Texte (Chat)

Pour cet exercice, nous allons utiliser **Open WebUI**, une interface web open-source, riche en fonctionnalités et conviviale, conçue pour interagir avec une grande variété de modèles de langage (LLM).

### Accès et première utilisation

1.  **Ouvrez votre navigateur** et rendez-vous à l'adresse de notre instance hébergée : [https://pauwels.open-webui.myia.io/](https://pauwels.open-webui.myia.io/)
2.  **Créez un compte** en cliquant sur "Sign up". Une simple adresse e-mail suffit.
3.  Une fois connecté, vous êtes prêt à interagir avec les modèles de langage disponibles.

### Tour d'horizon des fonctionnalités

Open WebUI est bien plus qu'une simple interface de chat. Elle transforme l'interaction avec les LLM en une expérience puissante et intégrée. Voici quelques-unes de ses fonctionnalités les plus notables pour l'utilisateur :

#### Interaction Enrichie

*   **Compréhension de documents (RAG) :** L'une des fonctionnalités phares est le "Retrieval-Augmented Generation". Vous pouvez déposer des documents (PDF, Word, etc.) dans l'interface, puis poser des questions au modèle sur leur contenu en utilisant le préfixe `#`. Le modèle "lit" le document pour vous répondre.
*   **Navigation sur le Web :** De la même manière, vous pouvez demander au modèle de lire le contenu d'une page web en tapant `#` suivi de l'URL.
*   **Génération d'images intégrée :** L'interface peut se connecter à des modèles de génération d'images, permettant de créer des visuels directement depuis le chat.
*   **Support Markdown et LaTeX :** Formatez vos prompts et visualisez les réponses avec une mise en forme complexe, incluant les équations mathématiques.

#### Gestion des Conversations

*   **Multi-modèle :** Engagez une conversation avec plusieurs modèles simultanément pour comparer leurs réponses ou exploiter leurs forces respectives. Vous pouvez interpeller un modèle spécifique dans une conversation en utilisant `@` suivi de son nom.
*   **Organisation :** Classez vos conversations dans des dossiers, taguez-les pour les retrouver facilement, et "clonez" une session de chat pour explorer une autre branche de discussion sans perdre l'historique.
*   **Prompts personnalisés :** Créez et sauvegardez des prompts récurrents via le système de "Prompt Presets", accessibles rapidement avec la commande `/`.

#### Gestion des Modèles

*   **Model Builder :** Créez facilement de nouveaux modèles ou des "personnalités" en combinant un modèle de base avec des instructions spécifiques (un "system prompt"), directement depuis l'interface.
*   **Intégration Communautaire :** Importez facilement des modèles depuis la communauté Ollama ou des prompts depuis la communauté Open WebUI.

#### Audio et Voix

*   **Entrée vocale :** Dictez vos prompts au lieu de les taper.
*   **Synthèse vocale (TTS) :** Écoutez les réponses du modèle, avec une intégration possible de services comme Azure Speech.
*   **Appels Vidéo/Audio :** Pour les modèles compatibles, il est même possible d'avoir des interactions en "appel" avec l'IA.

Cette plateforme constitue un véritable couteau suisse pour explorer les capacités des modèles de langage, de la simple conversation à des applications complexes basées sur vos propres documents.

## 3. Transcription Audio

Nous allons maintenant explorer la capacité de l'IA à transcrire un fichier audio en texte à l'aide de **Whisper-WebUI**, une interface graphique basée sur le modèle [Whisper d'OpenAI](https://github.com/openai/whisper).

### Accès à l'outil

1.  Ouvrez votre navigateur et allez à l'URL suivante : [https://whisper-webui.myia.io/](https://whisper-webui.myia.io/)
2.  Utilisez les identifiants suivants pour vous connecter :
    *   **Login:** `admin`
    *   **Password:** `goldman`
3.  Une fois connecté, vous pouvez simplement glisser-déposer un fichier audio (MP3, WAV, etc.) dans l'interface pour lancer la transcription.

### Fonctionnalités principales

Whisper-WebUI offre de nombreuses fonctionnalités pour faciliter la génération de sous-titres et la transcription :

*   **Choix du modèle :** Vous pouvez sélectionner différentes implémentations de Whisper pour optimiser la vitesse et l'utilisation des ressources :
    *   `openai/whisper` (l'original)
    *   `SYSTRAN/faster-whisper` (utilisé par défaut, plus rapide)
    *   `Vaibhavs10/insanely-fast-whisper` (une autre alternative rapide)

*   **Sources multiples :** Transcrivez l'audio à partir de :
    *   Fichiers locaux (glisser-déposer)
    *   URL Youtube
    *   Enregistrement direct depuis le microphone

*   **Formats d'export :** Les sous-titres générés peuvent être téléchargés dans plusieurs formats :
    *   `.srt` (format standard pour les vidéos)
    *   `.vtt` (format pour le web)
    *   `.txt` (transcription brute sans horodatage)

*   **Traduction intégrée :**
    *   **Audio vers Texte :** Traduisez directement un discours d'une autre langue vers l'anglais.
    *   **Texte vers Texte :** Traduisez les fichiers de sous-titres générés en utilisant les modèles NLLB de Facebook ou l'API DeepL.

*   **Traitement avancé :**
    *   **Pré-traitement :** Détecte et supprime les silences (avec Silero VAD) ou sépare la musique de fond des voix (avec UVR).
    *   **Post-traitement :** Identifie les différents locuteurs dans l'audio (diarisation) grâce au modèle `pyannote`.

Cet outil constitue une solution complète pour la transcription et la traduction audio, allant de la simple conversion d'un fichier à des flux de travail plus complexes.

---

*Ce document constitue une introduction pratique aux outils d'IA générative. N'hésitez pas à expérimenter avec les différentes plateformes proposées pour découvrir leurs spécificités et trouver celles qui correspondent le mieux à vos besoins.*