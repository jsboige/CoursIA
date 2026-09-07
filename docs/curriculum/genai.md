<!--
  FICHIER GENERE — ne pas editer a la main.
  Cette page de parcours est derivee du catalogue de notebooks par
  scripts/notebook_tools/generate_parcours.py, puis regeneree chaque jour
  sur `main` par .github/workflows/catalog-cron.yml. Toute edition manuelle
  sera silencieusement ecrasee au prochain passage du cron. Pour corriger
  une derive (comptes, enumerations), corriger la SOURCE (le catalogue /
  les metadonnees de notebook) ou le generateur — jamais cette page.
  Cf .claude/rules/catalog-pr-hygiene.md (les artefacts generes
  appartiennent a l'automatisation).
-->

# GenAI Multimodale

**Génération d'images, audio, vidéo et texte**

Génération d'images (DALL-E, Stable Diffusion, Qwen, ComfyUI), synthèse vocale, génération musicale, vidéo, et orchestration de modèles. Inclut les workflows Vibe-Coding et les pipelines de production.

## Statistiques

| Métrique | Valeur |
|----------|--------|
| Notebooks | 199 |
| PRODUCTION | 0 |
| BETA | 180 |
| ALPHA | 19 |

## GenAI/00-GenAI-Environment (6 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [GenAI Environment Setup - CoursIA](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-1-Environment-Setup.ipynb) | BETA | Non |
| 2 | [Docker Services Management - GenAI](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-2-Docker-Services-Management.ipynb) | BETA | Non |
| 3 | [Configuration des API Endpoints](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-3-API-Endpoints-Configuration.ipynb) | BETA | Non |
| 4 | [Environment Validation - GenAI](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-4-Environment-Validation.ipynb) | BETA | Non |
| 5 | [00-5: ComfyUI Local - Test Rapide](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb) | BETA | Non |
| 6 | [Deploiement Docker Local des Services GenAI](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-6-Local-Docker-Deployment.ipynb) | BETA | Non |

## GenAI/Audio (31 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [OpenAI TTS - Synthese Vocale par API](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb) | BETA | Non |
| 2 | [OpenAI Whisper STT - Reconnaissance Vocale par API](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) | BETA | Non |
| 3 | [Opérations de Base sur l'Audio](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-3-Basic-Audio-Operations.ipynb) | BETA | Non |
| 4 | [Whisper Local - Transcription GPU avec faster-whisper](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb) | BETA | Non |
| 5 | [Kokoro TTS Local - Synthese Vocale Legere](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-5-Kokoro-TTS-Local.ipynb) | BETA | Non |
| 6 | [Chatterbox TTS - Synthese Vocale Expressive](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb) | BETA | Non |
| 7 | [XTTS v2 - Clonage Vocal Zero-Shot](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-2-XTTS-Voice-Cloning.ipynb) | BETA | Non |
| 8 | [MusicGen - Generation Musicale par IA](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-3-MusicGen-Generation.ipynb) | BETA | Non |
| 9 | [Demucs v4 - Separation de Sources Audio](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-4-Demucs-Source-Separation.ipynb) | BETA | Non |
| 10 | [Multi-Model TTS Gateway - Synthese Vocale Multi-Modèles](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb) | BETA | Non |
| 11 | [Generation MIDI avec midi-model (SkyTNT)](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-6-MIDI-Generation.ipynb) | BETA | Non |
| 12 | [Generation de Chansons Completes : YuE vs…](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-7-Song-Generation.ipynb) | BETA | Non |
| 13 | [TTS Expressif : Fish S2 Pro et Modèles SOTA](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb) | BETA | Non |
| 14 | [Ace-Step v1.5 - Generation Musicale avec Paroles](../../MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-9-AceStep-Music-Generation.ipynb) | BETA | Non |
| 15 | [Comparaison Multi-Modèles Audio](../../MyIA.AI.Notebooks/GenAI/Audio/03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb) | BETA | Non |
| 16 | [Orchestration de Pipelines Audio](../../MyIA.AI.Notebooks/GenAI/Audio/03-Orchestration/03-2-Audio-Pipeline-Orchestration.ipynb) | BETA | Non |
| 17 | [OpenAI Realtime Voice API](../../MyIA.AI.Notebooks/GenAI/Audio/03-Orchestration/03-3-Realtime-Voice-API.ipynb) | BETA | Non |
| 18 | [Creation de Contenu Audio Educatif](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-1-Educational-Audio-Content.ipynb) | BETA | Non |
| 19 | [P3 - Annotation Prosodique pour TTS Agentique](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-10-Annotation-Prosodique.ipynb) | BETA | Non |
| 20 | [P4 — Generation TTS pour Audiobook](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-11-Generation-TTS.ipynb) | BETA | Non |
| 21 | [P5 — Compilation Audio pour Audiobook](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-12-Compilation-Audio.ipynb) | BETA | Oui |
| 22 | [Audiobook Agentique avec FishAudio S2-Pro](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-13-Audiobook-FishAudio-S2Pro.ipynb) | BETA | Non |
| 23 | [Voice Leading Rendu GenAI — donner un spectre aux…](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-14-VoiceLeading-Rendu-GenAI.ipynb) | BETA | Non |
| 24 | [Pipeline de Transcription et Sous-titrage](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-2-Transcription-Pipeline.ipynb) | BETA | Non |
| 25 | [Workflow de Composition Musicale](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-3-Music-Composition-Workflow.ipynb) | BETA | Non |
| 26 | [Synchronisation Audio-Video (Passerelle)](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-4-Audio-Video-Sync.ipynb) | BETA | Non |
| 27 | [Live Coding Musical pilote par LLM](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-5-LiveCoding-LLM-Music.ipynb) | BETA | Non |
| 28 | [Pipeline Audiobook Agentique](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-6-Audiobook-Pipeline.ipynb) | BETA | Non |
| 29 | [Benchmark TTS : Comparaison des Modèles Vocaux pour…](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-7-TTS-Voice-Benchmark.ipynb) | BETA | Non |
| 30 | [Lecture Analytique pour Audiobook](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-8-Lecture-Analytique.ipynb) | BETA | Oui |
| 31 | [Voice Casting : Attribution de voix TTS par personnage](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-9-Voice-Casting.ipynb) | BETA | Non |

## GenAI/CaseStudies (5 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Duel Verbal : Barbie vs l'Âne de Shrek](../../MyIA.AI.Notebooks/GenAI/CaseStudies/Barbie-Schreck/barbie-schreck.ipynb) | BETA | Non |
| 2 | [Vue d'ensemble : un duel d'agents Père Fouras vs…](../../MyIA.AI.Notebooks/GenAI/CaseStudies/Fort-Boyard/fort-boyard-python.ipynb) | ALPHA | Non |
| 3 | [Docteur vs ChatGPT : Chatbot medical multi-agent](../../MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/medical_chatbot.ipynb) | BETA | Non |
| 4 | [Doctor vs ChatGPT: Multi-Agent Medical Chatbot](../../MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/medical_chatbot_en.ipynb) | ALPHA | Non |
| 5 | [Générateur de Recettes PDF](../../MyIA.AI.Notebooks/GenAI/CaseStudies/Recipe-Maker/receipe_maker.ipynb) | BETA | Non |

## GenAI/FallacyDetection (4 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [01 — Introduction : taxonomies de sophismes et terrain…](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/01_taxonomy_intro.ipynb) | ALPHA | Oui |
| 2 | [02 — Paysage des datasets de detection de sophismes](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/02_fallacy_datasets_landscape.ipynb) | BETA | Non |
| 3 | [03 — Écart de couverture taxonomique : académique vs…](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/03_taxonomy_coverage_gap.ipynb) | BETA | Oui |
| 4 | [04 — Matrice de couverture cross-notebooks](../../MyIA.AI.Notebooks/GenAI/FallacyDetection/04_coverage_matrix.ipynb) | BETA | Oui |

## GenAI/FineTuning (7 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [FT-01 : Introduction au Fine-Tuning](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning.ipynb) | BETA | Non |
| 2 | [FT-02 : QLoRA — Fine-Tuning avec Quantization](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-02-QLoRA-Quantization.ipynb) | BETA | Non |
| 3 | [FT-03 : Supervised Fine-Tuning (SFT) — Enseigner un…](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-03-Supervised-FineTuning-SFT.ipynb) | BETA | Non |
| 4 | [FT-04 : RLHF et Alignement — Préférences Humaines et…](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-04-RLHF-DPO.ipynb) | BETA | Non |
| 5 | [FT-05 : Fusion et Routage de Modèles -- Combiner les…](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-ModelMerging-Routing.ipynb) | BETA | Non |
| 6 | [FT-05: Model Merging and Routing -- Combining…](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-ModelMerging-Routing_en.ipynb) | BETA | Non |
| 7 | [FT-06 : LoRA vision-langage — fine-tune du décodeur de…](../../MyIA.AI.Notebooks/GenAI/FineTuning/FT-06-Vision-Language-LoRA.ipynb) | BETA | Non |

## GenAI/Image (17 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [OpenAI DALL-E 3 - Generation d'Images](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb) | BETA | Non |
| 2 | [GPT-5 Multimodal - Analyse et Génération d'Images](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-2-GPT-5-Image-Generation.ipynb) | BETA | Non |
| 3 | [Opérations de Base sur les Images](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb) | BETA | Non |
| 4 | [Stable Diffusion Forge - SD XL Turbo](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb) | BETA | Non |
| 5 | [Qwen Image-Edit 2.5 - API ComfyUI](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-5-Qwen-Image-Edit.ipynb) | BETA | Non |
| 6 | [Qwen Image Edit 2509 - Édition Avancée d'Images](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-5b-Qwen-Image-Edit-2509.ipynb) | BETA | Non |
| 7 | [FLUX.1 - Génération d'Images Avancée](../../MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb) | BETA | Non |
| 8 | [Stable Diffusion 3.5 - Génération de Pointe](../../MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-3-Stable-Diffusion-3-5.ipynb) | BETA | Non |
| 9 | [Z-Image (Lumina-2) : Generation Avancee avec ComfyUI](../../MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-4-Z-Image-Lumina2.ipynb) | BETA | Non |
| 10 | [Bonsai-Image : Generation Text-to-Image avec…](../../MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-5-Bonsai-Image-Ternary.ipynb) | BETA | Non |
| 11 | [Comparaison Multi-Modèles : SDXL Lightning-4step,…](../../MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-1-Multi-Model-Comparison.ipynb) | BETA | Non |
| 12 | [Workflow Orchestration - Chaînage Multi-Modèles](../../MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-2-Workflow-Orchestration.ipynb) | BETA | Non |
| 13 | [Performance Optimization pour la Génération d'Images](../../MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-3-Performance-Optimization.ipynb) | BETA | Non |
| 14 | [Educational Content Generation - GenAI](../../MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-1-Educational-Content-Generation.ipynb) | BETA | Non |
| 15 | [Creative Workflows - GenAI](../../MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-2-Creative-Workflows.ipynb) | BETA | Non |
| 16 | [Production Integration - GenAI](../../MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-3-Production-Integration.ipynb) | BETA | Non |
| 17 | [Génération d’un patron de point de croix à partir d’une…](../../MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb) | ALPHA | Non |

## GenAI/Integrations-DotNet (10 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Aspire : orchestrer notre pile GenAI en C#](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/01-Aspire-Orchestration-GenAi.ipynb) | BETA | Non |
| 2 | [Aspire : orchestrer la pile GenAI réelle du cluster](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/02-Aspire-GenAiStack-Reel.ipynb) | BETA | Non |
| 3 | [Aspire 3 : Observabilite .NET moderne — Serilog,…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/03-Aspire-Observabilite.ipynb) | BETA | Non |
| 4 | [Aspire : un agent streaming en C# — Channels,…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/04-Aspire-Streaming-Agent.ipynb) | BETA | Non |
| 5 | [Aspire : des tests d'intégration modernes —…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/05-Aspire-Tests-Integration.ipynb) | BETA | Oui |
| 6 | [Aspire : garde-fous du code d'agent — l'analyseur…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/06-Aspire-GardeFous-Roslyn.ipynb) | ALPHA | Oui |
| 7 | [Aspire : le routeur MultiConnector — vetting en ligne,…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/07-Aspire-SemanticFleet-MultiConnector.ipynb) | BETA | Non |
| 8 | [Aspire : l'asynchrone aux frontieres natives -…](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb) | BETA | Oui |
| 9 | [GitHub Copilot SDK en C# : binding, streaming, Scrutor](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/CopilotSDK/01-GitHub-Copilot-SDK-Binding.ipynb) | BETA | Non |
| 10 | [EF Core : des requêtes vérifiées à la compilation](../../MyIA.AI.Notebooks/GenAI/Integrations-DotNet/EFCore/01-EFCore-Requetes-Compilees.ipynb) | BETA | Oui |

## GenAI/Plateformes-Conversationnelles (20 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [L'assistant de l'editeur — la quatrieme face du plugin](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/interroger-lassistant-de-lediteur-par-l-api.ipynb) | BETA | Non |
| 2 | [Joindre un fichier au chatbot — ignore, annote, ou…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/joindre-un-fichier-au-chatbot-par-l-api.ipynb) | BETA | Non |
| 3 | [Mesurer la dérive d'un copilot — le gate par étape ne…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/mesurer-la-derive-dun-copilot.ipynb) | BETA | Oui |
| 4 | [Obtenir des données structurées — la case json, le…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb) | BETA | Non |
| 5 | [Ingestion RAG d'un corpus long structure](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-3-RAG-et-Embeddings/ingestion-corpus-long-rag.ipynb) | BETA | Oui |
| 6 | [Séparer les environnements de vecteurs](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-3-RAG-et-Embeddings/separer-les-environnements-de-vecteurs.ipynb) | BETA | Oui |
| 7 | [Auditer un serveur MCP qu'on n'a pas ecrit](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-4-MCP-Server/auditer-un-serveur-mcp.ipynb) | BETA | Non |
| 8 | [Consommer vs exposer le MCP — les deux sens du fil](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb) | BETA | Oui |
| 9 | [Choisir le modèle derrière son chatbot — une…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-5-Multi-Provider/eval-choisir-son-modele.ipynb) | BETA | Non |
| 10 | [Presenter AI Engine par son API — instance jetable…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb) | BETA | Non |
| 11 | [Parcours QA — ce que l'API ne voit pas](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/05-Playwright-AI-Engine/00-Parcours-QA-AI-Engine.ipynb) | ALPHA | Non |
| 12 | [Auditer la conformite visuelle — ce que le smoke test…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/06-Securite-et-Methode/auditer-la-conformite-visuelle.ipynb) | BETA | Non |
| 13 | [Parcours QA-OWUI — Notebook chapeau de la mission](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/00-Parcours-QA-OWUI.ipynb) | ALPHA | Oui |
| 14 | [Module 01 — Découverte de Playwright & Open WebUI](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/01-decouverte/01-Decouverte-QA-OWUI.ipynb) | BETA | Oui |
| 15 | [Module 02 — Navigation & Authentification](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/02-navigation-authentification/02-Navigation-Auth-QA-OWUI.ipynb) | BETA | Oui |
| 16 | [Module 03 — Chat & Streaming LLM](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb) | BETA | Oui |
| 17 | [Module 04 — RAG, Outils MCP & Fonctionnalités avancées](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/04-rag-tools-avances/04-RAG-Tools-QA-OWUI.ipynb) | BETA | Oui |
| 18 | [Module 05 — Multi-tenant, API Testing & CI/CD](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb) | BETA | Oui |
| 19 | [Module 06 — Tester les nouveautés v0.10 (« l'ère…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb) | BETA | Non |
| 20 | [Différencier plusieurs assistants — mesurer ce qu'un…](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/differencier-les-assistants.ipynb) | BETA | Non |

## GenAI/PostTraining (16 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [PT-01 — Introduction et vue d'ensemble](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_01_intro_post_training.ipynb) | BETA | Non |
| 2 | [PT-02 — Supervised Fine-Tuning baseline (SFT)](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_02_sft_baseline.ipynb) | BETA | Non |
| 3 | [PT-03 — Direct Préférence Optimization (DPO)](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_03_dpo_direct_preference.ipynb) | ALPHA | Non |
| 4 | [PT-04 — Group Relative Policy Optimization (GRPO)](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_04_grpo_deepseek_r1.ipynb) | ALPHA | Non |
| 5 | [PT-05 — Reinforcement Learning with Verifiable Rewards…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_05_rlvr_verifiable_rewards.ipynb) | BETA | Non |
| 6 | [PT-06 — Evaluation Comparative du Post-Training](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_06_eval_comparative.ipynb) | BETA | Non |
| 7 | [PT-07 — Détecter le reward hacking avec rewardspy](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_07_rewardspy_reward_hacking.ipynb) | BETA | Oui |
| 8 | [PT-08 — GRPO from scratch : la mécanique du signal de…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_08_grpo_from_scratch_toy_env.ipynb) | BETA | Non |
| 9 | [PT-09 — RLOO (REINFORCE Leave-One-Out) from scratch :…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_09_rloo_from_scratch_toy_env.ipynb) | BETA | Oui |
| 10 | [PT-10 — GAE from scratch : pourquoi un mini-critic ?…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_10_gae_from_scratch_toy_env.ipynb) | BETA | Non |
| 11 | [PT-11 — GRPO + RLVR sur Qwen3.5-0.8B : la série…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_11_grpo_qwen35_rlvr.ipynb) | BETA | Non |
| 12 | [PT-11 — RLVR sur VRAI LLM (Qwen3.5-0.8B) +…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_11_grpo_qwen_rlvr_on_verifiers.ipynb) | BETA | Non |
| 13 | [PT-11b — RLVR multi-seed sur Qwen3.5-0.8B (4 seeds ×…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_11b_multiseed_qwen35_4x100.ipynb) | ALPHA | Non |
| 14 | [PT-11c — RLVR sur Qwen3-1.7B/2B (cran au-dessus de…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_11c_grpo_qwen17_rlvr.ipynb) | ALPHA | Non |
| 15 | [PT-12 — Crédit différé multi-step : GAE-λ sur un…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_12_multistep_delayed_credit.ipynb) | ALPHA | Oui |
| 16 | [PT-13 — Les trois biais du loss GRPO et leurs…](../../MyIA.AI.Notebooks/GenAI/PostTraining/PT_13_dapo_drgrpo_corrections.ipynb) | ALPHA | Oui |

## GenAI/RAG-et-Memoire-Semantique (10 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Hands-On Grounding — Qdrant en mémoire](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/01-Hands-On-Grounding.ipynb) | BETA | Oui |
| 2 | [02 — Retrieval avancé : HyDE, reranking et évaluation](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb) | BETA | Oui |
| 3 | [Embeddings from scratch — word2vec skip-gram, la…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/03-Embeddings-From-Scratch.ipynb) | BETA | Oui |
| 4 | [Tokenisation from scratch — l'unité de compte de tout…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/04-Tokenisation-From-Scratch.ipynb) | ALPHA | Oui |
| 5 | [Stockage vectoriel réel — persistance, index ANN (HNSW)…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05-Stockage-Vectoriel.ipynb) | BETA | Oui |
| 6 | [RAG 05b — Mode serveur Qdrant : compromis exact/ANN ef…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05b-Stockage-Vectoriel-Serveur.ipynb) | BETA | Non |
| 7 | [06 — Kernel Memory in-process : la couche d'abstraction…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/06-KernelMemory-InProcess.ipynb) | BETA | Non |
| 8 | [RAG 07 — Kernel Memory Python : ingestion, recherche et…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/07-KernelMemory-Python-Quickstart.ipynb) | BETA | Non |
| 9 | [RAG 08 — Kernel Memory et la recherche hybride : BM25 +…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/08-KernelMemory-Hybrid-Search.ipynb) | BETA | Non |
| 10 | [RAG 09 — Au-delà du texte : le plafond multimodal du…](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/09-KernelMemory-Multimodal.ipynb) | BETA | Non |

## GenAI/SemanticKernel (15 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [SK-1-Fundamentals : Introduction a Semantic Kernel](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb) | BETA | Non |
| 2 | [SK-2-Functions : Function Calling, Memory et…](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb) | BETA | Non |
| 3 | [SK-3-Agents : Agent Framework Semantic Kernel](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/03-SemanticKernel-Agents.ipynb) | BETA | Non |
| 4 | [SK-4-Filters : Filtres et Observabilite](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb) | BETA | Non |
| 5 | [SK-5-VectorStores : RAG avec Qdrant](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-VectorStores.ipynb) | BETA | Non |
| 6 | [SK-6-ProcessFramework : Workflows et Orchestration](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb) | BETA | Non |
| 7 | [SK-7-MultiModal : Images, Audio et Vision](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/07-SemanticKernel-MultiModal.ipynb) | BETA | Non |
| 8 | [SK-8-MCP : Model Context Protocol et Integration](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/08-SemanticKernel-MCP.ipynb) | BETA | Non |
| 9 | [SK-9-Building-CLR : Interoperabilite Python/.NET via…](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/09-SemanticKernel-Building-CLR.ipynb) | BETA | Non |
| 10 | [SK-10-NotebookMaker : Système Multi-Agents pour…](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/10-SemanticKernel-NotebookMaker.ipynb) | BETA | Non |
| 11 | [Conception Automatique de Notebook par Agents IA](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb) | BETA | Non |
| 12 | [Projet Createur de Mail personnalise](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/Cr%C3%A9ateur%20de%20mail%20personnalis%C3%A9.ipynb) | BETA | Non |
| 13 | [Notebook de travail — Titanic: exploration, préparation…](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/Notebook-Generated.ipynb) | BETA | Oui |
| 14 | [Notebook de conception de Notebook](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/Semantic-kernel-AutoInteractive.ipynb) | BETA | Non |
| 15 | [Jeu de devinette : Père Fouras vs Laurent Jalabert](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/fort-boyard-python.ipynb) | BETA | Non |

## GenAI/Texte (29 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [10. Hébergement Local de Modèles Génératifs](../../MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb) | BETA | Non |
| 2 | [10b. Mécanique d'inférence LLM : construire et mesurer…](../../MyIA.AI.Notebooks/GenAI/Texte/10b_Inference_Mechanics.ipynb) | BETA | Non |
| 3 | [10c. Stratégies pour contextes longs — budget de…](../../MyIA.AI.Notebooks/GenAI/Texte/10c_Long_Context_Strategies.ipynb) | BETA | Non |
| 4 | [10d. TensorSharp : pilote d'inférence LLM native .NET](../../MyIA.AI.Notebooks/GenAI/Texte/10d_TensorSharp_DotNet_Inference.ipynb) | BETA | Non |
| 5 | [10e. LLamaSharp : bake-off binding .NET de llama.cpp](../../MyIA.AI.Notebooks/GenAI/Texte/10e_LLamaSharp_DotNet_BakeOff.ipynb) | BETA | Non |
| 6 | [10f. ONNX Runtime GenAI : jambe finale du bake-off .NET](../../MyIA.AI.Notebooks/GenAI/Texte/10f_ORTGenAI_DotNet_BakeOff.ipynb) | BETA | Non |
| 7 | [11. Quantization](../../MyIA.AI.Notebooks/GenAI/Texte/11_Quantization.ipynb) | BETA | Non |
| 8 | [12. Test Time Scaling](../../MyIA.AI.Notebooks/GenAI/Texte/12_Test_Time_Scaling.ipynb) | BETA | Non |
| 9 | [13. Orchestration agentique du test-time scaling](../../MyIA.AI.Notebooks/GenAI/Texte/13_Agentic_Orchestration.ipynb) | BETA | Non |
| 10 | [13b — Évaluation d'agents : succès, coût, ablation et…](../../MyIA.AI.Notebooks/GenAI/Texte/13b_Agent_Evaluation.ipynb) | BETA | Non |
| 11 | [14. Memoire persistante pour le test-time scaling](../../MyIA.AI.Notebooks/GenAI/Texte/14_Persistent_Memory.ipynb) | BETA | Non |
| 12 | [15. Tree-of-Thoughts sur de vrais problemes de…](../../MyIA.AI.Notebooks/GenAI/Texte/15_Tree_of_Thoughts_Search.ipynb) | BETA | Non |
| 13 | [16. Scaling du test-time compute (Snell 2024)](../../MyIA.AI.Notebooks/GenAI/Texte/16_Scaling_Test_Time_Compute.ipynb) | BETA | Non |
| 14 | [17. Modèles a raisonnement natif vs scaling du…](../../MyIA.AI.Notebooks/GenAI/Texte/17_Native_Reasoning_vs_Scaling.ipynb) | BETA | Non |
| 15 | [18. Plugins Semantic Kernel pour le test-time scaling](../../MyIA.AI.Notebooks/GenAI/Texte/18_Semantic_Kernel_Plugins.ipynb) | BETA | Non |
| 16 | [19. Orchestration et tâches planifiées avec Open WebUI…](../../MyIA.AI.Notebooks/GenAI/Texte/19_OWUI_Orchestration.ipynb) | BETA | Non |
| 17 | [1. Introduction a l'IA generative avec l'API OpenAI](../../MyIA.AI.Notebooks/GenAI/Texte/1_OpenAI_Intro.ipynb) | BETA | Non |
| 18 | [20. OWUI Native API v0.9.6 — introspection REST et…](../../MyIA.AI.Notebooks/GenAI/Texte/20_OWUI_Native_API.ipynb) | BETA | Non |
| 19 | [22 — Évaluer les sorties générées : BLEU, ROUGE,…](../../MyIA.AI.Notebooks/GenAI/Texte/22_Evaluating_Generated_Text.ipynb) | BETA | Non |
| 20 | [TAL — du mot aux dépendances : le pipeline linguistique…](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) | BETA | Oui |
| 21 | [2. Prompt Engineering : Techniques Avancées](../../MyIA.AI.Notebooks/GenAI/Texte/2_PromptEngineering.ipynb) | ALPHA | Non |
| 22 | [3. Structured Outputs : Sorties JSON Garanties](../../MyIA.AI.Notebooks/GenAI/Texte/3_Structured_Outputs.ipynb) | BETA | Non |
| 23 | [Function Calling : Connecter les LLMs au Monde Réel](../../MyIA.AI.Notebooks/GenAI/Texte/4_Function_Calling.ipynb) | BETA | Non |
| 24 | [5. RAG Modern - Retrieval Augmented Generation](../../MyIA.AI.Notebooks/GenAI/Texte/5_RAG_Modern.ipynb) | BETA | Non |
| 25 | [PDF et Web Search : Sources Documentaires avec OpenAI](../../MyIA.AI.Notebooks/GenAI/Texte/6_PDF_Web_Search.ipynb) | BETA | Non |
| 26 | [Code Interpreter : Exécution de Code avec OpenAI](../../MyIA.AI.Notebooks/GenAI/Texte/7_Code_Interpreter.ipynb) | BETA | Non |
| 27 | [8. Reasoning Models](../../MyIA.AI.Notebooks/GenAI/Texte/8_Reasoning_Models.ipynb) | BETA | Non |
| 28 | [9. Production Patterns](../../MyIA.AI.Notebooks/GenAI/Texte/9_Production_Patterns.ipynb) | BETA | Non |
| 29 | [9b. Prompt Security & Red-Teaming sur notre stack…](../../MyIA.AI.Notebooks/GenAI/Texte/9b_Prompt_Security_RedTeam.ipynb) | BETA | Non |

## GenAI/Vibe-Coding (8 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Claude CLI - Les Bases](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb) | BETA | Oui |
| 2 | [Claude CLI - Gestion des Sessions](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/02-Claude-CLI-Sessions.ipynb) | BETA | Oui |
| 3 | [Claude CLI - References et Contexte](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/03-Claude-CLI-References.ipynb) | BETA | Oui |
| 4 | [Claude CLI - Agents et Subagents](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/04-Claude-CLI-Agents.ipynb) | BETA | Oui |
| 5 | [Claude CLI - Automatisation Avancee](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/05-Claude-CLI-Automatisation.ipynb) | BETA | Non |
| 6 | [Claude Code via Claudish](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/notebooks/01-claude-code-via-claudish.ipynb) | BETA | Non |
| 7 | [CSharpRepl attache a un process .NET vivant](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb) | ALPHA | Oui |
| 8 | [Garde-fous Roslyn pour le code genere par agent](../../MyIA.AI.Notebooks/GenAI/Vibe-Coding/docs/Roslyn-Code-Guardrails.ipynb) | BETA | Oui |

## GenAI/Video (21 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Opérations de Base sur les Videos](../../MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-1-Video-Operations-Basics.ipynb) | BETA | Non |
| 2 | [GPT-5 Video Understanding - Comprehension Video par IA](../../MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-2-GPT-5-Video-Understanding.ipynb) | BETA | Non |
| 3 | [Qwen2.5-VL Video Analysis - Comprehension Video Locale](../../MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-3-Qwen-VL-Video-Analysis.ipynb) | BETA | Non |
| 4 | [Video Enhancement - Real-ESRGAN et Interpolation de…](../../MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb) | ALPHA | Non |
| 5 | [AnimateDiff - Introduction a la Generation…](../../MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-5-AnimateDiff-Introduction.ipynb) | BETA | Non |
| 6 | [HunyuanVideo](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-1-HunyuanVideo-Generation.ipynb) | BETA | Non |
| 7 | [LTX-Video - Generation Video Rapide et Legere](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-2-LTX-Video-Lightweight.ipynb) | BETA | Non |
| 8 | [Wan 2.1/2.2 - Generation Video Multilingue](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-3-Wan-Video-Generation.ipynb) | BETA | Non |
| 9 | [SVD - Stable Video Diffusion (Image-to-Video)](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-4-SVD-Image-to-Video.ipynb) | ALPHA | Non |
| 10 | [LTX-2 - Generation Audiovisuelle Conjointe (Video +…](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-5-LTX2-Audiovisual.ipynb) | BETA | Non |
| 11 | [MiniMax H3 (Hailuo 3.0) — Architecture, capacités… et…](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb) | BETA | Non |
| 12 | [CogVideoX - Generation Video depuis Texte (Open…](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-7-CogVideoX-Text-to-Video.ipynb) | BETA | Non |
| 13 | [Comparaison Multi-Modèles de Generation Video](../../MyIA.AI.Notebooks/GenAI/Video/03-Orchestration/03-1-Multi-Model-Video-Comparison.ipynb) | BETA | Non |
| 14 | [Orchestration de Pipelines Video](../../MyIA.AI.Notebooks/GenAI/Video/03-Orchestration/03-2-Video-Workflow-Orchestration.ipynb) | ALPHA | Non |
| 15 | [ComfyUI - Workflows Video via API](../../MyIA.AI.Notebooks/GenAI/Video/03-Orchestration/03-3-ComfyUI-Video-Workflows.ipynb) | BETA | Non |
| 16 | [Generation de Videos Educatives](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-1-Educational-Video-Generation.ipynb) | BETA | Non |
| 17 | [Workflows Video Creatifs](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-2-Creative-Video-Workflows.ipynb) | BETA | Non |
| 18 | [Sora API - Generation Video Cloud](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-3-Sora-API-Cloud-Video.ipynb) | BETA | Non |
| 19 | [Pipeline Video de Production](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-4-Production-Video-Pipeline.ipynb) | BETA | Non |
| 20 | [MiniMax H3 (Hailuo) — Génération vidéo par le service…](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-5-MiniMax-H3-Cloud-Video.ipynb) | BETA | Non |
| 21 | [MiniMax video-01 (v1) — Service cloud generation video…](../../MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-5b-MiniMax-video-01-v1-Cloud-Video.ipynb) | BETA | Non |
