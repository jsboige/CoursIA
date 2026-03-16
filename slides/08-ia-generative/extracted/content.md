<!-- Slide number: 1 -->
# Intelligence Artificielle Générative
1
Intelligence Artificielle – VIII

Panorama, enjeux et pratiques de l’IA générative

Découvrir les bases et les grands principes de l’IA générative
Comprendre les différents usages applicatifs (texte, image, audio…)
Identifier les limites et les enjeux éthiques

IA 101

### Notes:

<!-- Slide number: 2 -->
# Plan du cours
2
Introduction
Résolution de problèmes
Bases de connaissances et logique
Incertitude et modèles probabilistes
Apprentissage
Traitement du langage naturel
Elargissements
 IA Générative
IA 101

### Notes:

<!-- Slide number: 3 -->
# Introduction à l’IA Générative
3
Qu’est-ce que l’IA générative :
Création de textes, images, audio, vidéo à partir de modèles probabilistes en réponse à des prompts (+ d’autres modalités)
Exploitation d’algorithmes avancés d’apprentissage profond entrainés par des  jeux de données massifs.
Exemples:
ChatGPT (texte)
Stable Diffusion / Flux (images)
Hunyuan (vidéo)
Whisper (audio/speech-to-text)
Audiocraft (musique)
Github Copilot (code)

CS 405

<!-- Slide number: 4 -->
# IA générative: Une révolution
4
Adoption rapide, impact massif
2017 : « Attention is All you need »
Scaling Laws: GPT 1 (117m), GPT 2 (1,5B), GPT 3 (175B), GPT 4 (1000G)
ChatGPT : 1 million d’utilisateurs en 5 jours, 100M en 2 mois.
Impact sur le marketing, la rédaction et l’assistance client.
Défis :
Coût d’entraînement, biais des modèles, complexité des prompts, intervention/interprétation humaine nécessaire.
Approche multidisciplinaire
Apprentissage automatique, traitement du langage naturel, vision par ordinateur.
Utilisation conjointe des embeddings et des mécanismes d’attention.
Systèmes ISPO
Input, Storage, Process, Output
Caractéristiques:
Vitesse, précision, régularité,
polyvalence, fiabilité, mémoire, programmable

![Une image contenant texte, Police, capture d’écran, logo Description générée automatiquement](Image6.jpg)
CS 405

<!-- Slide number: 5 -->
# Les données : Fondement des modèles
5
Importance des données en IA générative
Qualité et représentativité des données.
"Garbage in, Garbage out"
Biais possibles : genre, culture, contexte géographique.
Risque d’hallucination, nécessite pré-traitement, audit
Pipeline
Acquisition → Nettoyage → Préparation → Annotation
Données synthétiques : Alternative pour
Créer des données nouvelles en masse (saturation des données humaines de qualité)
protéger la confidentialité.
2025: Model Collapse
Scalabilité et coût énergétique
Nécessité d’infrastructures puissantes (datacenters).
Optimisations possibles : modèles distillés, datacenters verts.
Méthodes d’entraînement
Apprentissage de base
Très coûteux, modèles fondationnels
Fine-Tuning
Ajustement spécifique, Loras, RL
Apprentissage en contexte
Peu couteux, prompt engineering
Activité: Sources de données
Classe, Maison, Transport, Loisirs => Mots ?

![Une image contenant texte, capture d’écran, Police, ligne Description générée automatiquement](Image6.jpg)
CS 405

<!-- Slide number: 6 -->
# Fonctionnement des LLMs
6

![](Image7.jpg)
Tokens
Représentation numérique des mots
Vocabulaire de 50k/128k
Embeddings
Représentation vectorielle des mots/phrases
Permet de calculer leur proximité sémantique.
King - Man + Woman = Queen.
Activité: Mind-Meld
Par deux, mots aléatoires simultanés
Puis Mots à « mi-distance »
Réseaux de neurones
Constitués de couches interconnectées
Les poids de ces connexions sont ajustés
Rétropropagation  Autodifférentiation
 Concept d’attention
Importance relative des mots
Dans un contexte donné
« I saw the man with the telescope »
Activité: Mots polysémiques
Définition
Flèches d’attention
Transformers
Architecture clé des LLMs modernes
Avancées architecturales:
MOE, Sparse Attention, Rope Scaling etc.
Multimodalité
Alternatives récentes
Mamba (State Space Models), Jamba (scalabilité linéaire)
Diffusion

![](Image13.jpg)

![](Image9.jpg)

![](Image6.jpg)

![](Image11.jpg)
CS 405

<!-- Slide number: 7 -->
# Modèles probabilistes
7

![Une image contenant capture d’écran, texte, diagramme, Tracé Description générée automatiquement](Image12.jpg)
Génération de texte / Transformers
Les Mots sont choisis en séquence
en fonction de leur probabilité d’occurrence
dans un contexte donné (= mots qui précèdent).
Paramètres de génération :
Température :
Contrôle la variabilité des résultats.
Distribution sur le vocabulaire
Top-n sampling :
Limite le choix aux mots les plus probables
Top-p: Jusqu’à un seuil de distribution cumulatif
Top-k:  k mots les plus probables.
Génération d’image / Modèle de diffusion
Ajout d’un bruit gaussien probabiliste
Apprentissage du débruitage
Génération depuis un espace latent
Conditionnement par attention (texte, image etc.)
Paramètres
N-steps: Nombre d’étapes de débruitage
Cfg-scale (Classifier-Free Guidance)
Conformité au conditionnement
Accents, Prompts négatifs
Diriger par le texte
Denoising strength (img2img)
Quantité de changement
Paramètres communs
Seed:
Reproductibilité
Activité
Expérimentation de paramètres (seed fixe)

![](Image8.jpg)

![](Image10.jpg)

![](Image16.jpg)

![Une image contenant texte, capture d’écran, diagramme, Police Description générée automatiquement](Image18.jpg)
CS 405

<!-- Slide number: 8 -->
# Applications: Usage individuels
8
Design et graphisme
Création de prototypes visuels, dessins, photos
Outils : MidJourney, Stable Diffusion, ChatGPT, Gemini nano banana.
Littérature et rédaction créative
Écriture de scénarios, récits interactifs, co-écriture, poésie.
Outils: ChatGPT, Claude, Llama etc.
Entreprenariat et innovation
Idéation, validation d’idées, élaboration de stratégies
Prototypage, faisabilité
Compagnons IA
Soutien psychologique, coaching, romance
Ex: Replika

![Une image contenant dessin, clipart, créativité, illustration Description générée automatiquement](Image10.jpg)

![Une image contenant noir, obscurité Description générée automatiquement](Image8.jpg)

![Une image contenant Visage humain, lèvre, art Description générée automatiquement](Image6.jpg)
CS 405

<!-- Slide number: 9 -->
# Applications: Entreprise
9

![Une image contenant capture d’écran, Graphique, Caractère coloré, diagramme Description générée automatiquement](Image11.jpg)
Positionnement Métier
Ex: Microsoft Copilot
Communication d’entreprise
Synthèse de contenu
Résumer des textes complexes et extraire les thèmes majeurs.
Stratégies de communication
Structuration d’arguments persuasifs et réduction des biais
Marketing et interaction client
Création de campagnes
Contenu pour réseaux sociaux, blogs, vidéos publicitaires.
Génération de slogans et de storyboards publicitaires
Chatbots conversationnels, FAQ dynamique.
Recrutement et formation
Génération de descriptions de poste inclusives et attractives.
Résumé automatique des candidatures
Identifier les points forts et faibles.
Conception de scénarios et questions d’entretien personnalisés.
Personnalisation des parcours de formation.
Analytics et prise de décision
Automatisation des pipelines de données : extraction, validation, et nettoyage.
Modélisation avancée : résolution de problèmes complexes
Visualisation rapide : génération de graphiques interactifs
Synthèse rapide : résumer des tableaux de bord complexes
Activité: Campagne Marketing fictive: Nouveau Soda
Un slogan, 1 visuel, 3 posts réseaux sociaux, 1 scnéario de pub

![](Image6.jpg)

![Une image contenant graphisme, texte, art, léger Description générée automatiquement](Image13.jpg)
CS 405

<!-- Slide number: 10 -->
# Applications sectorielles
10
Santé
Génération de rapports médicaux, assistance au diagnostic.
Chatbots médicaux pour le suivi
Génération de supports pédagogiques
Éducation
Création de supports pédagogiques
Synthèse et vulgarisation des contenus complexes
Mise en place d’assistants pédagogiques interactifs
Création de quiz dynamiques
Finance et gestion des risques
Extraction d’informations à partir de rapports financiers
Prévisions avancées :
utilisation de données pour suivre les stocks ou indices
Automatisation des chaînes d'information
génération d’indicateurs, d’alphas
Détection d’anomalies dans des transactions complexes
Recherche et sciences
Synthèse automatique d’articles académiques
Exploration documentaire et rédaction scientifique
Automatisation de la validation
optimisation de modèles mathématiques
Activité:
Prévision Trading Crypto par graphiques avec indicateurs

![](Image12.jpg)

![Une image contenant capture d’écran, art Description générée automatiquement](Image8.jpg)

![Une image contenant musique, concert, léger Description générée automatiquement](Image6.jpg)

![Une image contenant texte, habits, masque à gaz, capture d’écran Description générée automatiquement](Image14.jpg)
CS 405

<!-- Slide number: 11 -->
# Techniques : Génération de texte
11
Prompt Engineering
Instructions explicites et exemples (« few-shot learning »)
Variantes lexicales et stylistiques
Qui, Quoi, Pour qui, Quel objectif, Quelle cible, quel format, quel style etc.
Prompts Systèmes
Structuration pour des tâches complexes, (COT)
Évaluation comparative, Exploration (ToT)
Retrieval Augmented Generation (RAG)
Combinaison de modèles génératifs et bases documentaires
Calibration des données, chunks, embedding, requêtes et contexte
pour éviter le bruit et améliorer la pertinence des réponses.
Function Calling et outils intégrés
Appels de fonctions via des API
Génération structurée, décoration, paramètres
Orchestration et pipelines
Outils pour la structuration des workflows
Fonctions sémantiques, natives
Composition de prompts, de modèles
Ex: Semantic-kernel, Langchain
Agentique avancée
Coordination entre agents pour des tâches complexes
Conversations collaboratives, prompts systèmes et fonctions spécifiques
Ex: AutoGen, Semantic-Kernel
Vibe Coding
Copilot, Cline, Roo (extensions vscode)
CLIs (Claude code, Gemini, Qwen, Mistral etc.)
CS 405

<!-- Slide number: 12 -->
# Techniques: Multimodalité
12
Graphiques:
Modèles de diffusion pour générer des visuels
Dall-e, Stable diffusion, Flux
Txt2Img, Img2Img, Inpainting, Outpainting, Finetuning (Loras), Upscaling, ControlNet
Vision
GPT-4o, O1, QwenVL, InternVL
Nombreux Benchmarks
Génération Vidéo
SD: Deforum, AnimateDiff
Ad-hoc: Hunyuan, Wan, Google Veo 3, Sora, Runway, Kling AI
3D
Représentation:
Meshes, Radiance Fields (Nerfs), VoxNet (Convolution) Point clouds etc.
Génération:
DreamFusion, Trellis (ex: Trellis + Comfy)
Audio
Speech-To-Text
Whisper, Moonshine
Text-To-Speech
Elevenlabs, Kokoro
Musique
Audiocraft, AudioLDM, UniAudio
Code,
UX Variées, Contexte ?
VsCode: Copilot, Cline, Continue
Maths :
Modèles de Reflexion
Propriétaires: OpenAI, Google
Open-Source: Deepseek
CS 405

<!-- Slide number: 13 -->
# Ecosystème GenAI
13
Modèles et APIs
APIs propriétaires
OpenAI, Anthropic, Google, Mistral, etc.
Aggrégateur: OpenRouter
Modèles Locaux
Llama, Mistral, Gemini, Ms Phi, Qwen, DeepSeek etc.
Diffuseurs: Hugging Face, Github
Nombreux Benchmarks
Hébergement
Cloud
LLM Hosting
Hugging Face, Groq
Location de GPUs
Runpod, VastAI
Grand clouds généralistes
AWS, Azure, Google etc.
Local
Oobabooga, Ollama, Vllm
Quants (gguf, exl2/3, AWQ etc.)
Containerisation
Docker/Kubernetes
Hybride
Ex: Tailscale (réseau)
Image
Modèles: Stable-Diffusion, Flux, Qwen Image Edit, Z-image Turbo, CivitAI
Apps: Forge, ComfyUI
Conversationnel
Généralistes:
Open-webui, SillyTarvern
Workflows Pro / LLMOps:
Dify, Langflow

![Une image contenant symbole, logo, Graphique, Police Description générée automatiquement](Image6.jpg)

![Une image contenant clipart, dessin humoristique, smiley, émoticône Description générée automatiquement](Image8.jpg)

![Une image contenant cube Description générée automatiquement avec une confiance faible](Image10.jpg)

![Une image contenant Graphique, blanc, symbole, noir Description générée automatiquement](Image12.jpg)

![Une image contenant Police, Graphique, cercle, logo Description générée automatiquement](Image16.jpg)

![Une image contenant grenouille, amphibien, Rainette, ordinateur Description générée automatiquement](Image24.jpg)

![Une image contenant capture d’écran, Graphique, Police, graphisme Description générée automatiquement](Image18.jpg)

![Une image contenant clipart, croquis, dessin, dessin humoristique Description générée automatiquement](Image20.jpg)

![Une image contenant conception, origami Description générée automatiquement](Image26.jpg)

![](Image28.jpg)

![Une image contenant Graphique, graphisme, rouge, Police Description générée automatiquement](Image32.jpg)

![](Image38.jpg)

![Une image contenant Graphique, Police, capture d’écran, logo Description générée automatiquement](Image40.jpg)
CS 405

<!-- Slide number: 14 -->
# Enjeux Ethiques et sociétaux
14
Biais et discrimination
Présence de stéréotypes
dans les données d’entraînement.
Technique de débiaisage des modèles
Illusions
Hallucinations
Réponses incorrectes mais plausibles
Illusion de correction
Confiance exagérée des utilisateurs dans les résultats
Impact Environnemental
Coûts énergétiques (GPUs)
Apprentissage
Activité: Dataset biaisé
Conception d’un dataset synthétique
Ajout d’un biais
Détection du biais

![](Image6.jpg)
CS 405

<!-- Slide number: 15 -->
# Régulation et droit
15
Propriété intellectuelle
Droits sur les contenus générés.
Modèles open-source vs propriétaires.
Protection des données
Risques : Confidentialité et conformité au RGPD.
Bonnes pratiques :
Anonymisation des données.
Formation des équipes sur la règlementation.
Normes émergentes et recommandations
Initiatives internationales :
Régulation européenne (AI Act – en vigueur depuis 01/08/2024).
Position des États-Unis sur l’IA.
11/02/25: Trump signe un Executive Order bloquant les régulations IA des états
Exemples pratiques :
Agentic AI Foundation (9/12/25): OpenAI, Anthropic et Block établissent MCP (Model Context Protocol) comme standard mondial pour les agents IA.
Licences open-source responsables.
Droits des IAs
Bientôt: IA surhumaine, émergence de la conscience artificielle
Droits des agents, autonomie ? Pouvoir économique (Cryptos) ?
CS 405

<!-- Slide number: 16 -->
# Risques et limites
16
Fiabilité des modèles
Hallucinations et fabrications
Impact sur la confiance utilisateur.
Nécessité de tests rigoureux avant le déploiement en entreprise.
Solutions :
Développement d’algorithmes robustes.
Mécanismes de vérification croisée entre plusieurs modèles.
Tests et validations
« Auditeurs IA » identifient des biais dans des scénarios fictifs.
Activité: Auditeur:
Recommandation Voyage, classe
Sources de données in/out, Test
Sécurité des modèles
Risques de mauvaise utilisation
Armes bactériologiques, nucléaires, pédopornographie etc.
Risques de perte de contrôle
Cf. Anthropic: niveaux de sécurité
Constitutional AI
Points critiques
Perte d’emplois liée à l’automatisation.
Homogénéisation des contenus créatifs.
Risque d’adopter des modèles insuffisamment audités pour des tâches critiques.
Gestion des biais et des hallucinations.
Sensibilisation aux enjeux de confidentialité.
Détection et gestion des contenus générés frauduleusement
Deepfakes
Activité: Constitutional AI
Définition d’une Constitution
Création d’un prompt système
Test sur modèle ablitéré
CS 405

<!-- Slide number: 17 -->
# Responsabilité sociale
17
Rôle des entreprises vs utilisateurs
Entreprises :
Transparence des modèles.
Codes éthiques.
Utilisateurs :
Formation sur les limites des modèles IA.
Adoption responsable dans les secteurs critiques.
Sensibilisation sur les forces et faiblesses des systèmes d’IA générative.
Impact Environnemental
Rapport IEA 2025
Consommation des datacenter x2 en 3 ans (= Japon)
 IA pour le bien commun
IA pour des solutions écologiques ou sociales.
Outils pour la santé publique ou l’éducation dans des zones sous-développées.
Surveiller la déforestation ou améliorer la gestion des ressources en eau.
Activité: Propositions novatrices
Avec et sans guidance
CS 405

<!-- Slide number: 18 -->
# Défis pratiques de l’adoption
18
Compatibilité technologique
Adaptation aux systèmes existants (CRM, ERP).
Gestion des bases vectorielles dans des flux de travail établis.
Confidentialité
Maîtrise des flux de données
Scalabilité et coûts
PMEs avec des budgets limités.
Infrastructure technique nécessaire pour gérer de grands modèles.
Réalité du ROI
Gartner 2025: Adoption massive (75% des entreprises) mais « AI Fatigue » et ROI tangibles peu nombreux au-delà (rédaction, code)
Optimisations possibles :
Solutions open-source pour réduire les coûts.
Utilisation de modèles plus légers comme les distillations pour les déploiements locaux.
Modèles spécialisés SOTA sur des tâches
Confidentialité maîtrisée
CS 405

<!-- Slide number: 19 -->
# Questions?
19
IA 101

### Notes:

<!-- Slide number: 20 -->
# Merci
20
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: