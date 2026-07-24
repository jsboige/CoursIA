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
| Notebooks | 135 |
| PRODUCTION | 0 |
| BETA | 125 |
| ALPHA | 10 |

## GenAI (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | GenAI E2E Quant Validation | BETA | Non |

## GenAI/00-GenAI-Environment (6 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | 🚀 GenAI Environment Setup - CoursIA | BETA | Non |
| 2 | 🐳 Docker Services Management - GenAI | BETA | Non |
| 3 | 🔗 Configuration des API Endpoints | BETA | Non |
| 4 | ✅ Environment Validation - GenAI | BETA | Non |
| 5 | 00-5: ComfyUI Local - Test Rapide | BETA | Non |
| 6 | Deploiement Docker Local des Services GenAI | BETA | Non |

## GenAI/Audio (30 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | OpenAI TTS - Synthese Vocale par API | BETA | Non |
| 2 | OpenAI Whisper STT - Reconnaissance Vocale par API | BETA | Non |
| 3 | Opérations de Base sur l'Audio | BETA | Non |
| 4 | Whisper Local - Transcription GPU avec faster-whisper | BETA | Non |
| 5 | Kokoro TTS Local - Synthese Vocale Legere | BETA | Non |
| 6 | Chatterbox TTS - Synthese Vocale Expressive | BETA | Non |
| 7 | XTTS v2 - Clonage Vocal Zero-Shot | BETA | Non |
| 8 | MusicGen - Generation Musicale par IA | BETA | Non |
| 9 | Demucs v4 - Separation de Sources Audio | BETA | Non |
| 10 | Multi-Model TTS Gateway - Synthese Vocale Multi-Modèles | BETA | Non |
| 11 | Generation MIDI avec midi-model (SkyTNT) | BETA | Non |
| 12 | Generation de Chansons Completes : YuE vs SongGeneratio | BETA | Non |
| 13 | TTS Expressif : Fish S2 Pro et Modèles SOTA | BETA | Non |
| 14 | Ace-Step v1.5 - Generation Musicale avec Paroles | BETA | Non |
| 15 | Comparaison Multi-Modèles Audio | BETA | Non |
| 16 | Orchestration de Pipelines Audio | BETA | Non |
| 17 | OpenAI Realtime Voice API | BETA | Non |
| 18 | Creation de Contenu Audio Educatif | BETA | Non |
| 19 | P3 - Annotation Prosodique pour TTS Agentique | BETA | Non |
| 20 | P4 — Generation TTS pour Audiobook | BETA | Non |
| 21 | P5 — Compilation Audio pour Audiobook | BETA | Oui |
| 22 | Audiobook Agentique avec FishAudio S2-Pro | BETA | Non |
| 23 | Pipeline de Transcription et Sous-titrage | BETA | Non |
| 24 | Workflow de Composition Musicale | BETA | Non |
| 25 | Synchronisation Audio-Video (Passerelle) | BETA | Non |
| 26 | Live Coding Musical pilote par LLM | BETA | Non |
| 27 | Pipeline Audiobook Agentique | BETA | Non |
| 28 | Benchmark TTS : Comparaison des Modèles Vocaux pour l'A | BETA | Non |
| 29 | Lecture Analytique pour Audiobook | BETA | Oui |
| 30 | Voice Casting : Attribution de voix TTS par personnage | BETA | Non |

## GenAI/CaseStudies (3 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Duel Verbal : Barbie vs l'Âne de Shrek | BETA | Non |
| 2 | Docteur vs ChatGPT : Chatbot medical multi-agent | BETA | Non |
| 3 | Générateur de Recettes PDF | BETA | Non |

## GenAI/FineTuning (5 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | FT-01 : Introduction au Fine-Tuning | BETA | Non |
| 2 | FT-02 : QLoRA — Fine-Tuning avec Quantization | BETA | Non |
| 3 | FT-03 : Supervised Fine-Tuning (SFT) — Instruction Foll | BETA | Non |
| 4 | FT-04 : RLHF et Alignement — Préférences Humaines et DP | BETA | Non |
| 5 | FT-05 : Fusion et Routage de Modèles -- Combiner les Ex | BETA | Non |

## GenAI/Image (17 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | OpenAI DALL-E 3 - Generation d'Images | BETA | Non |
| 2 | 🤖 GPT-5 Multimodal - Analyse et Génération d'Images | BETA | Non |
| 3 | 🖼️ Opérations de Base sur les Images | BETA | Non |
| 4 | Notebook: Stable Diffusion Forge - SD XL Turbo | BETA | Non |
| 5 | Notebook: Qwen Image-Edit 2.5 - API ComfyUI | BETA | Non |
| 6 | Qwen Image Edit 2509 - Édition Avancée d'Images | BETA | Non |
| 7 | FLUX.1 - Génération d'Images Avancée | BETA | Non |
| 8 | Stable Diffusion 3.5 - Génération de Pointe | BETA | Non |
| 9 | Z-Image (Lumina-2) : Generation Avancee avec ComfyUI | BETA | Non |
| 10 | Bonsai-Image : Generation Text-to-Image avec Quantizati | BETA | Non |
| 11 | Comparaison Multi-Modèles : SDXL Lightning-4step, Z-Ima | BETA | Non |
| 12 | Workflow Orchestration - Chaînage Multi-Modèles | BETA | Non |
| 13 | 🚀 Performance Optimization pour la Génération d'Images | BETA | Non |
| 14 | 🎓 Educational Content Generation - GenAI | BETA | Non |
| 15 | Creative Workflows - GenAI | BETA | Non |
| 16 | 🏭 Production Integration - GenAI | BETA | Non |
| 17 | Génération d’un patron de point de croix à partir d’une | ALPHA | Non |

## GenAI/Open-WebUI (7 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Parcours QA-OWUI — Notebook chapeau de la mission | ALPHA | Oui |
| 2 | Module 01 — Découverte de Playwright & Open WebUI | BETA | Oui |
| 3 | Module 02 — Navigation & Authentification | BETA | Oui |
| 4 | Module 03 — Chat & Streaming LLM | BETA | Oui |
| 5 | Module 04 — RAG, Outils MCP & Fonctionnalités avancées | BETA | Oui |
| 6 | Module 05 — Multi-tenant, API Testing & CI/CD | BETA | Oui |
| 7 | Module 06 — Tester les nouveautés v0.10 (« l'ère agenti | BETA | Non |

## GenAI/PostTraining (7 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | PT-01 — Introduction et vue d'ensemble | BETA | Non |
| 2 | PT-02 — Supervised Fine-Tuning baseline (SFT) | BETA | Non |
| 3 | PT-03 — Direct Préférence Optimization (DPO) | ALPHA | Non |
| 4 | PT-04 — Group Relative Policy Optimization (GRPO) | ALPHA | Non |
| 5 | PT-05 — Reinforcement Learning with Verifiable Rewards  | ALPHA | Non |
| 6 | PT-06 — Evaluation Comparative du Post-Training | BETA | Non |
| 7 | PT-07 — Détecter le reward hacking avec rewardspy | BETA | Oui |

## GenAI/RAG-et-Memoire-Semantique (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Hands-On Grounding — Qdrant en mémoire | BETA | Oui |

## GenAI/SemanticKernel (15 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | SK-1-Fundamentals : Introduction a Semantic Kernel | BETA | Non |
| 2 | SK-2-Functions : Function Calling, Memory et Fonctionna | BETA | Non |
| 3 | SK-3-Agents : Agent Framework Semantic Kernel | BETA | Non |
| 4 | SK-4-Filters : Filtres et Observabilite | BETA | Non |
| 5 | SK-5-VectorStores : RAG avec Qdrant | BETA | Non |
| 6 | SK-6-ProcessFramework : Workflows et Orchestration | BETA | Non |
| 7 | SK-7-MultiModal : Images, Audio et Vision | BETA | Non |
| 8 | SK-8-MCP : Model Context Protocol et Integration | BETA | Non |
| 9 | SK-9-Building-CLR : Interoperabilite Python/.NET via py | BETA | Non |
| 10 | SK-10-NotebookMaker : Système Multi-Agents pour Generat | BETA | Non |
| 11 | Projet Createur de Mail personnalise | BETA | Non |
| 12 | Notebook de travail | BETA | Oui |
| 13 | Notebook de conception de Notebook | BETA | Non |
| 14 | Jeu de devinette : Père Fouras vs Laurent Jalabert | ALPHA | Non |
| 15 | Jeu de devinette : Père Fouras vs Laurent Jalabert | BETA | Non |

## GenAI/Texte (20 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | 10. Hébergement Local de Modèles Génératifs | BETA | Non |
| 2 | 11. Quantization des LLMs | BETA | Non |
| 3 | 12 - Test-Time Scaling : le second axe de mise a l'eche | BETA | Non |
| 4 | 13. Orchestration agentique du test-time scaling | BETA | Non |
| 5 | 14. Memoire persistante pour le test-time scaling | BETA | Non |
| 6 | 15. Tree-of-Thoughts sur de vrais problemes de recherch | BETA | Non |
| 7 | 16. Scaling du test-time compute (Snell 2024) | BETA | Non |
| 8 | 17. Modèles a raisonnement natif vs scaling du test-tim | BETA | Non |
| 9 | 18. Plugins Semantic Kernel pour le test-time scaling | BETA | Non |
| 10 | 19. Orchestration et tâches planifiées avec Open WebUI  | BETA | Non |
| 11 | 1. Introduction a l'IA generative avec l'API OpenAI | BETA | Non |
| 12 | 20. OWUI Native API v0.9.6 — introspection REST et surf | BETA | Non |
| 13 | 2. Prompt Engineering : Techniques Avancées | ALPHA | Non |
| 14 | 3. Structured Outputs : Sorties JSON Garanties | BETA | Non |
| 15 | Function Calling : Connecter les LLMs au Monde Réel | BETA | Non |
| 16 | 5. RAG Modern - Retrieval Augmented Generation | BETA | Non |
| 17 | PDF et Web Search : Sources Documentaires avec OpenAI | BETA | Non |
| 18 | Code Interpreter : Exécution de Code avec OpenAI | BETA | Non |
| 19 | Modèles de Raisonnement : gpt-5-mini | BETA | Non |
| 20 | Patterns de Production : APIs Avancées OpenAI | BETA | Non |

## GenAI/Vibe-Coding (6 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Claude CLI - Les Bases | BETA | Oui |
| 2 | Claude CLI - Gestion des Sessions | BETA | Oui |
| 3 | Claude CLI - References et Contexte | BETA | Oui |
| 4 | Claude CLI - Agents et Subagents | BETA | Oui |
| 5 | Claude CLI - Automatisation Avancee | BETA | Non |
| 6 | Claude Code via Claudish | BETA | Non |

## GenAI/Video (17 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Opérations de Base sur les Videos | BETA | Non |
| 2 | GPT-5 Video Understanding - Comprehension Video par IA | BETA | Non |
| 3 | Qwen2.5-VL Video Analysis - Comprehension Video Locale | BETA | Non |
| 4 | Video Enhancement - Real-ESRGAN et Interpolation de Fra | ALPHA | Non |
| 5 | AnimateDiff - Introduction a la Generation Text-to-Vide | BETA | Non |
| 6 | HunyuanVideo - Generation Video Haute Qualite**Module : | BETA | Non |
| 7 | LTX-Video - Generation Video Rapide et Legere | BETA | Non |
| 8 | Wan 2.1/2.2 - Generation Video Multilingue | BETA | Non |
| 9 | SVD - Stable Video Diffusion (Image-to-Video) | ALPHA | Non |
| 10 | LTX-2 - Generation Audiovisuelle Conjointe (Video + Aud | BETA | Non |
| 11 | Comparaison Multi-Modèles de Generation Video | BETA | Non |
| 12 | Orchestration de Pipelines Video | ALPHA | Non |
| 13 | ComfyUI - Workflows Video via API | BETA | Non |
| 14 | Generation de Videos Educatives | BETA | Non |
| 15 | Workflows Video Creatifs | BETA | Non |
| 16 | Sora API - Generation Video Cloud | BETA | Non |
| 17 | Pipeline Video de Production | BETA | Non |
