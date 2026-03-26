---
theme: ../theme-ia101
title: "08 IA Generative"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

---
layout: cover
---

# Intelligence Artificielle Generative

Intelligence Artificielle -- VIII

**Panorama, enjeux et pratiques de l'IA generative**

- Decouvrir les bases et les grands principes de l'IA generative
- Comprendre les differents usages applicatifs (texte, image, audio...)
- Identifier les limites et les enjeux ethiques

---

# Plan du cours

- I. Introduction
- II. Resolution de problemes
- III. Bases de connaissances et logique
- IV. Incertitude et modèles probabilistes
- V. Apprentissage
- VI. Traitement du langage naturel
- VII. Elargissements
- **VIII. IA Generative** ← *vous etes ici*

---

# Introduction a l'IA Generative

- **Qu'est-ce que l'IA generative ?**
  - Creation de textes, images, audio, video a partir de modèles probabilistes
  - En reponse a des prompts (+ autres modalites)
  - Exploitation d'algorithmes d'apprentissage profond sur des jeux de données massifs
- **Exemples :**
  - ChatGPT (texte), Stable Diffusion / Flux (images)
  - Hunyuan (video), Whisper (audio/speech-to-text)
  - Audiocraft (musique), Github Copilot (code)

---

---
layout: image-right
image: ./images/img_001.png
---

# IA generative : Une revolution

- **Adoption rapide, impact massif**
  - 2017 : "Attention is All you need"
  - Scaling Laws : GPT-1 (117M) → GPT-2 (1.5B) → GPT-3 (175B) → GPT-4 (1T+)
  - ChatGPT : 1M utilisateurs en 5 jours, 100M en 2 mois
- **Defis :**
  - Cout d'entrainement, biais des modèles
  - Complexite des prompts, intervention humaine necessaire
- **Approche multidisciplinaire**
  - ML + NLP + Vision par ordinateur
  - Embeddings + mecanismes d'attention

---

# Systèmes ISPO

- **Input, Storage, Process, Output** : les quatre fonctions fondamentales d'un système informatique
  - **Input** : données d'entree (texte, image, audio, video)
  - **Storage** : mémoire des poids du modèle et du contexte de la conversation
  - **Process** : inference par le modèle (attention, génération token par token)
  - **Output** : resultat genere (texte, image, code, audio...)
- Proprietes : vitesse, precision, regularite, polyvalence, fiabilite, programmabilite

---

---
layout: image-right
image: ./images/img_002.png
---

# Les données : Qualite et biais

- **Importance des données en IA generative**
  - Qualite et representativite des données
  - "Garbage in, Garbage out"
  - Biais possibles : genre, culture, contexte geographique
  - Risque d'hallucination → pre-traitement, audit
- **Pipeline de données**
  - Acquisition → Nettoyage → Preparation → Annotation
- **Données synthetiques**
  - Alternative pour creer en masse, proteger la confidentialite
  - 2025 : risque de Model Collapse

---

---
layout: image-right
image: ./images/img_005.png
---

# Les données : Entrainement et cout

- **Scalabilite et cout energetique**
  - Necessite d'infrastructures puissantes (datacenters)
  - Optimisations : modèles distilles, datacenters verts
- **Methodes d'entrainement**
  - *Apprentissage de base* : tres couteux, modèles fondationnels
  - *Fine-Tuning* : ajustement specifique, LoRAs, RL
  - *Apprentissage en contexte* : peu couteux, prompt engineering
- **Activite : Sources de données**
  - Classe, Maison, Transport, Loisirs → Mots ?

---

---
layout: image-right
image: ./images/img_003.png
---

# Fonctionnement des LLMs : Tokens et Embeddings

- **Tokens**
  - Représentation numerique des mots
  - Vocabulaire de 50k a 128k tokens
- **Embeddings**
  - Représentation vectorielle des mots/phrases
  - Permet de calculer la proximite semantique
  - *King - Man + Woman = Queen*
- **Activite : Mind-Meld**
  - Par deux, mots aleatoires simultanes
  - Puis mots a "mi-distance"

---
layout: image-right
image: ./images/img_007.png
---

# Fonctionnement des LLMs : Tokens et Embeddings

- **Tokens**
  - Représentation numerique des mots
  - Vocabulaire de 50k a 128k tokens
- **Embeddings**
  - Représentation vectorielle des mots/phrases
  - Permet de calculer la proximite semantique
  - *King - Man + Woman = Queen*
- **Activite : Mind-Meld**
  - Par deux, mots aleatoires simultanes
  - Puis mots a "mi-distance"

---

---
layout: image-right
image: ./images/img_004.png
---

# Fonctionnement des LLMs : Attention et Transformers

- **Concept d'attention**
  - Importance relative des mots dans un contexte donne
  - *"I saw the man with the telescope"*
- **Activite : Mots polysemiques** -- définition + fleches d'attention
- **Transformers** : architecture cle des LLMs modernes
  - Avancees : MoE, Sparse Attention, RoPE Scaling, Multimodalite
- **Alternatives recentes** : Mamba, Jamba, Diffusion

---
layout: image-right
image: ./images/img_006.png
---

# Fonctionnement des LLMs : Attention et Transformers

- **Concept d'attention**
  - Importance relative des mots dans un contexte donne
  - *"I saw the man with the telescope"*
- **Activite : Mots polysemiques** -- définition + fleches d'attention
- **Transformers** : architecture cle des LLMs modernes
  - Avancees : MoE, Sparse Attention, RoPE Scaling, Multimodalite
- **Alternatives recentes** : Mamba, Jamba, Diffusion

---

---
layout: image-right
image: ./images/img_008.png
---

# Modeles probabilistes : Génération de texte

- **Les mots sont choisis en sequence**
  - En fonction de leur probabilité d'occurrence
  - Dans un contexte donne (= mots qui precedent)
- **Parametres de génération :**
  - *Temperature* : controle la variabilite des resultats
  - *Top-p sampling* : seuil de distribution cumulatif
  - *Top-k sampling* : k mots les plus probables

---
layout: image-right
image: ./images/img_009.png
---

# Modeles probabilistes : Génération de texte

- **Les mots sont choisis en sequence**
  - En fonction de leur probabilité d'occurrence
  - Dans un contexte donne (= mots qui precedent)
- **Parametres de génération :**
  - *Temperature* : controle la variabilite des resultats
  - *Top-p sampling* : seuil de distribution cumulatif
  - *Top-k sampling* : k mots les plus probables

---
layout: image-right
image: ./images/img_010.png
---

# Modeles probabilistes : Génération de texte

- **Les mots sont choisis en sequence**
  - En fonction de leur probabilité d'occurrence
  - Dans un contexte donne (= mots qui precedent)
- **Parametres de génération :**
  - *Temperature* : controle la variabilite des resultats
  - *Top-p sampling* : seuil de distribution cumulatif
  - *Top-k sampling* : k mots les plus probables

---

---
layout: image-right
image: ./images/img_011.png
---

# Modeles probabilistes : Génération d'images

- **Modele de diffusion**
  - Ajout de bruit gaussien, apprentissage du debruitage
  - Génération depuis un espace latent
  - Conditionnement par attention (texte, image, etc.)
- **Parametres :**
  - *N-steps* : etapes de debruitage
  - *CFG-scale* : conformite au conditionnement
  - *Denoising strength* (img2img) : quantite de changement
  - *Seed* : reproductibilite
- **Activite : Experimentation de parametres** (seed fixe)

---
layout: image-right
image: ./images/img_012.png
---

# Modeles probabilistes : Génération d'images

- **Modele de diffusion**
  - Ajout de bruit gaussien, apprentissage du debruitage
  - Génération depuis un espace latent
  - Conditionnement par attention (texte, image, etc.)
- **Parametres :**
  - *N-steps* : etapes de debruitage
  - *CFG-scale* : conformite au conditionnement
  - *Denoising strength* (img2img) : quantite de changement
  - *Seed* : reproductibilite
- **Activite : Experimentation de parametres** (seed fixe)

---

# Applications : Usages individuels

- **Design et graphisme**
  - Prototypes visuels, dessins, photos
  - Outils : MidJourney, Stable Diffusion, ChatGPT, Gemini
- **Litterature et redaction creative**
  - Scenarios, recits interactifs, co-ecriture, poesie
  - Outils : ChatGPT, Claude, Llama
- **Entreprenariat et innovation**
  - Ideation, validation d'idees, prototypage
- **Compagnons IA**
  - Soutien psychologique, coaching, romance (ex: Replika)

---
layout: image-right
image: ./images/img_015.png
---

# Applications : Usages individuels

- **Design et graphisme**
  - Prototypes visuels, dessins, photos
  - Outils : MidJourney, Stable Diffusion, ChatGPT, Gemini
- **Litterature et redaction creative**
  - Scenarios, recits interactifs, co-ecriture, poesie
  - Outils : ChatGPT, Claude, Llama
- **Entreprenariat et innovation**
  - Ideation, validation d'idees, prototypage
- **Compagnons IA**
  - Soutien psychologique, coaching, romance (ex: Replika)

---
layout: image-right
image: ./images/img_014.png
---

# Applications : Usages individuels

- **Design et graphisme**
  - Prototypes visuels, dessins, photos
  - Outils : MidJourney, Stable Diffusion, ChatGPT, Gemini
- **Litterature et redaction creative**
  - Scenarios, recits interactifs, co-ecriture, poesie
  - Outils : ChatGPT, Claude, Llama
- **Entreprenariat et innovation**
  - Ideation, validation d'idees, prototypage
- **Compagnons IA**
  - Soutien psychologique, coaching, romance (ex: Replika)

---
layout: image-right
image: ./images/img_013.png
---

# Applications : Usages individuels

- **Design et graphisme**
  - Prototypes visuels, dessins, photos
  - Outils : MidJourney, Stable Diffusion, ChatGPT, Gemini
- **Litterature et redaction creative**
  - Scenarios, recits interactifs, co-ecriture, poesie
  - Outils : ChatGPT, Claude, Llama
- **Entreprenariat et innovation**
  - Ideation, validation d'idees, prototypage
- **Compagnons IA**
  - Soutien psychologique, coaching, romance (ex: Replika)

---

---
layout: image-right
image: ./images/img_016.png
---

# Applications : Entreprise (1/2)

- **Positionnement Metier** (ex: Microsoft Copilot)
- **Communication d'entreprise**
  - Synthese de contenu, themes majeurs
  - Structuration d'arguments persuasifs
- **Marketing et interaction client**
  - Contenu réseaux sociaux, blogs, videos publicitaires
  - Slogans, storyboards publicitaires
  - Chatbots conversationnels, FAQ dynamique

---

---
layout: image-right
image: ./images/img_017.png
---

# Applications : Entreprise (2/2)

- **Recrutement et formation**
  - Descriptions de poste inclusives
  - Resume automatique des candidatures
  - Scenarios d'entretien personnalises
  - Parcours de formation adaptatifs
- **Analytics et prise de decision**
  - Automatisation des pipelines de données
  - Modelisation avancee, visualisation rapide
  - Synthese de tableaux de bord complexes
- **Activite : Campagne Marketing fictive : Nouveau Soda**
  - Un slogan, 1 visuel, 3 posts réseaux sociaux, 1 scenario de pub

---
layout: image-right
image: ./images/img_018.jpg
---

# Applications : Entreprise (2/2)

- **Recrutement et formation**
  - Descriptions de poste inclusives
  - Resume automatique des candidatures
  - Scenarios d'entretien personnalises
  - Parcours de formation adaptatifs
- **Analytics et prise de decision**
  - Automatisation des pipelines de données
  - Modelisation avancee, visualisation rapide
  - Synthese de tableaux de bord complexes
- **Activite : Campagne Marketing fictive : Nouveau Soda**
  - Un slogan, 1 visuel, 3 posts réseaux sociaux, 1 scenario de pub

---

# Applications sectorielles

- **Sante** : rapports medicaux, assistance au diagnostic, chatbots de suivi
- **Education** : supports pedagogiques, vulgarisation, quiz dynamiques, assistants interactifs
- **Finance** : extraction de rapports, previsions, detection d'anomalies
- **Recherche** : synthese d'articles, exploration documentaire, optimisation de modèles
- **Activite :** Prevision Trading Crypto par graphiques avec indicateurs

---
layout: image-right
image: ./images/img_021.png
---

# Applications sectorielles

- **Sante** : rapports medicaux, assistance au diagnostic, chatbots de suivi
- **Education** : supports pedagogiques, vulgarisation, quiz dynamiques, assistants interactifs
- **Finance** : extraction de rapports, previsions, detection d'anomalies
- **Recherche** : synthese d'articles, exploration documentaire, optimisation de modèles
- **Activite :** Prevision Trading Crypto par graphiques avec indicateurs

---
layout: image-right
image: ./images/img_020.png
---

# Applications sectorielles

- **Sante** : rapports medicaux, assistance au diagnostic, chatbots de suivi
- **Education** : supports pedagogiques, vulgarisation, quiz dynamiques, assistants interactifs
- **Finance** : extraction de rapports, previsions, detection d'anomalies
- **Recherche** : synthese d'articles, exploration documentaire, optimisation de modèles
- **Activite :** Prevision Trading Crypto par graphiques avec indicateurs

---
layout: image-right
image: ./images/img_019.jpg
---

# Applications sectorielles

- **Sante** : rapports medicaux, assistance au diagnostic, chatbots de suivi
- **Education** : supports pedagogiques, vulgarisation, quiz dynamiques, assistants interactifs
- **Finance** : extraction de rapports, previsions, detection d'anomalies
- **Recherche** : synthese d'articles, exploration documentaire, optimisation de modèles
- **Activite :** Prevision Trading Crypto par graphiques avec indicateurs

---
layout: image-right
image: ./images/img_022.jpg
---

# Applications sectorielles

- **Sante** : rapports medicaux, assistance au diagnostic, chatbots de suivi
- **Education** : supports pedagogiques, vulgarisation, quiz dynamiques, assistants interactifs
- **Finance** : extraction de rapports, previsions, detection d'anomalies
- **Recherche** : synthese d'articles, exploration documentaire, optimisation de modèles
- **Activite :** Prevision Trading Crypto par graphiques avec indicateurs

---

# Techniques : Génération de texte

- **Prompt Engineering** : instructions explicites, few-shot learning, variantes stylistiques
- **Prompts Systèmes** : structuration pour taches complexes (CoT, ToT)
- **RAG** (Retrieval Augmented Génération)
  - Combinaison modèles generatifs + bases documentaires
  - Chunks, embeddings, requetes contextuelles
- **Function Calling** : appels API, génération structuree
- **Orchestration** : Semantic Kernel, LangChain
- **Agentique avancee** : coordination multi-agents (AutoGen, Semantic Kernel)
- **Vibe Coding** : Copilot, Cline, Roo (VS Code) + CLIs (Claude Code, Gemini, etc.)

> **Pipeline RAG** : Question → Embedding → Recherche vectorielle → Contexte + Question → LLM → Reponse fondee

---

---
layout: columns
---

# Techniques : Multimodalite

<div class="columns">
<div class="col-left">

- **Graphiques**
  - Dall-E, Stable Diffusion, Flux
  - Txt2Img, Img2Img, Inpainting, ControlNet, LoRAs
- **Vision**
  - GPT-4o, O1, QwenVL, InternVL
- **Video**
  - SD: Deforum, AnimateDiff
  - Hunyuan, Wan, Veo 3, Sora, Runway, Kling AI
- **3D**
  - Représentation: Meshes, NeRFs, VoxNet, Point Clouds
  - Génération: DreamFusion, Trellis

</div>
<div class="col-right">

- **Audio**
  - STT: Whisper, Moonshine
  - TTS: ElevenLabs, Kokoro
  - Musique: Audiocraft, AudioLDM, UniAudio
- **Code**
  - VS Code: Copilot, Cline, Continue
- **Maths**
  - Modeles de reflexion
  - Proprietaires: OpenAI, Google
  - Open-Source: DeepSeek

</div>
</div>

---

# Ecosysteme GenAI : Modeles et APIs

- **APIs proprietaires** : OpenAI, Anthropic, Google, Mistral
  - Aggregateur : OpenRouter
- **Modeles locaux** : Llama, Mistral, Gemini, Phi, Qwen, DeepSeek
  - Diffuseurs : Hugging Face, Github
  - Nombreux benchmarks

<div style="display:flex; justify-content:flex-end; align-items:center; gap:24px; margin-top:24px;">
<img src="./images/img_023.png" alt="OpenRouter" style="height:120px;">
<img src="./images/img_024.png" alt="HuggingFace" style="height:120px;">
</div>

---

# Ecosysteme GenAI : Hebergement et outils

- **Cloud** : Hugging Face, Groq, Runpod, VastAI, AWS/Azure/GCP
- **Local** : Oobabooga, Ollama, vLLM
  - Quantification : GGUF, EXL2/3, AWQ
  - Containerisation Docker/Kubernetes
- **Image** : Stable Diffusion, Flux, Qwen Image Edit, CivitAI
  - Apps : Forge, ComfyUI
- **Conversationnel** : Open-WebUI, SillyTavern
  - Workflows Pro : Dify, Langflow

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:10px; margin-top:12px; align-items:center; justify-items:center;">
<img src="./images/img_027.png" alt="Groq" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_026.png" alt="VastAI" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_029.png" alt="Ollama" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_028.png" alt="vLLM" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_031.jpg" alt="StabilityAI" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_033.png" alt="SillyTavern" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_034.png" alt="OpenWebUI" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="./images/img_035.png" alt="Dify" style="max-height:55px; max-width:90px; object-fit:contain;">
</div>

---

---
layout: image-right
image: ./images/img_036.png
---

# Enjeux ethiques et societaux

- **Biais et discrimination**
  - Stereotypes dans les données d'entrainement
  - Techniques de debiaisage des modèles
- **Illusions**
  - Hallucinations : reponses incorrectes mais plausibles
  - Confiance exageree des utilisateurs
- **Impact environnemental**
  - Couts energetiques (GPUs, datacenters)
- **Activite : Dataset biaise**
  - Concevoir un dataset synthetique, ajouter un biais, le detecter

---

# Regulation et droit

- **Propriete intellectuelle**
  - Droits sur les contenus generes
  - Modeles open-source vs proprietaires
- **Protection des données**
  - Conformite RGPD, anonymisation
- **Normes emergentes**
  - AI Act europeen (en vigueur 01/08/2024)
  - Executive Order US sur l'IA (02/2025)
  - Agentic AI Foundation : MCP comme standard mondial (12/2025)
- **Droits des IAs**
  - IA surhumaine, conscience artificielle, autonomie economique ?

> **Chronologie** : RGPD (2018) → AI Act EU (08/2024) → Executive Order US (02/2025) → MCP standard (12/2025)

---

# Risques et limites

- **Fiabilite** : hallucinations, fabrications, impact confiance
  - Solutions : algorithmes robustes, verification croisee multi-modèles
- **Tests et validation**
  - "Auditeurs IA" : detection de biais en scenarios fictifs
  - **Activite :** recommandation voyage, sources de données in/out
- **Securite** : risques de mauvaise utilisation, perte de controle
  - Niveaux de securite Anthropic, Constitutional AI
- **Points critiques** : perte d'emplois, homogeneisation creative, deepfakes
  - **Activite : Constitutional AI** → definir une constitution, tester

> **Niveaux Anthropic** : ASL-1 (pas de risque) → ASL-2 (risque modere, garde-fous) → ASL-3 (capacites avancees, controle renforce) → ASL-4+ (autonomie, risque systemique)

---

# Responsabilite sociale

- **Role des entreprises** : transparence, codes ethiques
- **Role des utilisateurs** : formation, adoption responsable
- **Impact environnemental**
  - Rapport IEA 2025 : consommation datacenters x2 en 3 ans (= Japon)
- **IA pour le bien commun**
  - Solutions ecologiques, sante publique, education
  - Surveillance deforestation, gestion des ressources en eau
- **Activite : Propositions novatrices** (avec et sans guidance)

> **Chiffres cles** : GPT-4 entrainement ≈ 50 GWh | 1 requete ChatGPT ≈ 10x une recherche Google | Datacenters IA : 4% electricite mondiale d'ici 2030 (IEA)

---

# Defis pratiques de l'adoption

- **Compatibilite technologique** : adaptation CRM/ERP, bases vectorielles
- **Confidentialite** : maitrise des flux de données
- **Scalabilite et couts** : PMEs, infrastructure technique
- **Realite du ROI**
  - Gartner 2025 : 75% d'adoption mais "AI Fatigue"
  - ROI tangibles limites (redaction, code)
- **Optimisations :**
  - Solutions open-source, modèles distilles
  - Modeles specialises SOTA, confidentialite maitrisee

---

---
layout: center
---

# Questions?

---

---
layout: cover
---

# Merci

Jean-Sylvain Boige
jsboige@myia.org

> **Notebooks associes :** `MyIA.AI.Notebooks/GenAI/`
> Tutoriels DALL-E, Stable Diffusion, ComfyUI, Qwen Image Edit, LLMs