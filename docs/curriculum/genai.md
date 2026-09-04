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
| 1 | GenAI Environment Setup - CoursIA | BETA | Non |
| 2 | Docker Services Management - GenAI | BETA | Non |
| 3 | Configuration des API Endpoints | BETA | Non |
| 4 | Environment Validation - GenAI | BETA | Non |
| 5 | 00-5: ComfyUI Local - Test Rapide | BETA | Non |
| 6 | Deploiement Docker Local des Services GenAI | BETA | Non |

## GenAI/Aspire (8 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Aspire : orchestrer notre pile GenAI en C# | BETA | Non |
| 2 | Aspire : orchestrer la pile GenAI réelle du cluster | BETA | Non |
| 3 | Aspire 3 : Observabilite .NET moderne — Serilog,… | BETA | Non |
| 4 | Aspire : un agent streaming en C# — Channels,… | BETA | Non |
| 5 | Aspire : des tests d'intégration modernes —… | BETA | Oui |
| 6 | Aspire : garde-fous du code d'agent — l'analyseur… | ALPHA | Oui |
| 7 | Aspire : le routeur MultiConnector — vetting en ligne,… | BETA | Non |
| 8 | Aspire : l'asynchrone aux frontieres natives -… | BETA | Oui |

## GenAI/Audio (31 notebooks)

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
| 12 | Generation de Chansons Completes : YuE vs… | BETA | Non |
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
| 23 | Voice Leading Rendu GenAI — donner un spectre aux… | BETA | Non |
| 24 | Pipeline de Transcription et Sous-titrage | BETA | Non |
| 25 | Workflow de Composition Musicale | BETA | Non |
| 26 | Synchronisation Audio-Video (Passerelle) | BETA | Non |
| 27 | Live Coding Musical pilote par LLM | BETA | Non |
| 28 | Pipeline Audiobook Agentique | BETA | Non |
| 29 | Benchmark TTS : Comparaison des Modèles Vocaux pour… | BETA | Non |
| 30 | Lecture Analytique pour Audiobook | BETA | Oui |
| 31 | Voice Casting : Attribution de voix TTS par personnage | BETA | Non |

## GenAI/CaseStudies (5 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Duel Verbal : Barbie vs l'Âne de Shrek | BETA | Non |
| 2 | Vue d'ensemble : un duel d'agents Père Fouras vs… | ALPHA | Non |
| 3 | Docteur vs ChatGPT : Chatbot medical multi-agent | BETA | Non |
| 4 | Doctor vs ChatGPT: Multi-Agent Medical Chatbot | ALPHA | Non |
| 5 | Générateur de Recettes PDF | BETA | Non |

## GenAI/CopilotSDK (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | GitHub Copilot SDK en C# : binding, streaming, Scrutor | BETA | Non |

## GenAI/EFCore (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | EF Core : des requêtes vérifiées à la compilation | BETA | Oui |

## GenAI/FallacyDetection (4 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | 01 — Introduction : taxonomies de sophismes et terrain… | ALPHA | Oui |
| 2 | 02 — Paysage des datasets de detection de sophismes | BETA | Non |
| 3 | 03 — Écart de couverture taxonomique : académique vs… | BETA | Oui |
| 4 | 04 — Matrice de couverture cross-notebooks | BETA | Oui |

## GenAI/FineTuning (7 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | FT-01 : Introduction au Fine-Tuning | BETA | Non |
| 2 | FT-02 : QLoRA — Fine-Tuning avec Quantization | BETA | Non |
| 3 | FT-03 : Supervised Fine-Tuning (SFT) — Enseigner un… | BETA | Non |
| 4 | FT-04 : RLHF et Alignement — Préférences Humaines et… | BETA | Non |
| 5 | FT-05 : Fusion et Routage de Modèles -- Combiner les… | BETA | Non |
| 6 | FT-05: Model Merging and Routing -- Combining… | BETA | Non |
| 7 | FT-06 : LoRA vision-langage — fine-tune du décodeur de… | BETA | Non |

## GenAI/Image (17 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | OpenAI DALL-E 3 - Generation d'Images | BETA | Non |
| 2 | GPT-5 Multimodal - Analyse et Génération d'Images | BETA | Non |
| 3 | Opérations de Base sur les Images | BETA | Non |
| 4 | Stable Diffusion Forge - SD XL Turbo | BETA | Non |
| 5 | Qwen Image-Edit 2.5 - API ComfyUI | BETA | Non |
| 6 | Qwen Image Edit 2509 - Édition Avancée d'Images | BETA | Non |
| 7 | FLUX.1 - Génération d'Images Avancée | BETA | Non |
| 8 | Stable Diffusion 3.5 - Génération de Pointe | BETA | Non |
| 9 | Z-Image (Lumina-2) : Generation Avancee avec ComfyUI | BETA | Non |
| 10 | Bonsai-Image : Generation Text-to-Image avec… | BETA | Non |
| 11 | Comparaison Multi-Modèles : SDXL Lightning-4step,… | BETA | Non |
| 12 | Workflow Orchestration - Chaînage Multi-Modèles | BETA | Non |
| 13 | Performance Optimization pour la Génération d'Images | BETA | Non |
| 14 | Educational Content Generation - GenAI | BETA | Non |
| 15 | Creative Workflows - GenAI | BETA | Non |
| 16 | Production Integration - GenAI | BETA | Non |
| 17 | Génération d’un patron de point de croix à partir d’une… | ALPHA | Non |

## GenAI/Plateformes-Conversationnelles (20 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | L'assistant de l'editeur — la quatrieme face du plugin | BETA | Non |
| 2 | Joindre un fichier au chatbot — ignore, annote, ou… | BETA | Non |
| 3 | Mesurer la dérive d'un copilot — le gate par étape ne… | BETA | Oui |
| 4 | Obtenir des données structurées — la case json, le… | BETA | Non |
| 5 | Ingestion RAG d'un corpus long structure | BETA | Oui |
| 6 | Séparer les environnements de vecteurs | BETA | Oui |
| 7 | Auditer un serveur MCP qu'on n'a pas ecrit | BETA | Non |
| 8 | Consommer vs exposer le MCP — les deux sens du fil | BETA | Oui |
| 9 | Choisir le modèle derrière son chatbot — une… | BETA | Non |
| 10 | Presenter AI Engine par son API — instance jetable… | BETA | Non |
| 11 | Parcours QA — ce que l'API ne voit pas | ALPHA | Non |
| 12 | Auditer la conformite visuelle — ce que le smoke test… | BETA | Non |
| 13 | Parcours QA-OWUI — Notebook chapeau de la mission | ALPHA | Oui |
| 14 | Module 01 — Découverte de Playwright & Open WebUI | BETA | Oui |
| 15 | Module 02 — Navigation & Authentification | BETA | Oui |
| 16 | Module 03 — Chat & Streaming LLM | BETA | Oui |
| 17 | Module 04 — RAG, Outils MCP & Fonctionnalités avancées | BETA | Oui |
| 18 | Module 05 — Multi-tenant, API Testing & CI/CD | BETA | Oui |
| 19 | Module 06 — Tester les nouveautés v0.10 (« l'ère… | BETA | Non |
| 20 | Différencier plusieurs assistants — mesurer ce qu'un… | BETA | Non |

## GenAI/PostTraining (16 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | PT-01 — Introduction et vue d'ensemble | BETA | Non |
| 2 | PT-02 — Supervised Fine-Tuning baseline (SFT) | BETA | Non |
| 3 | PT-03 — Direct Préférence Optimization (DPO) | ALPHA | Non |
| 4 | PT-04 — Group Relative Policy Optimization (GRPO) | ALPHA | Non |
| 5 | PT-05 — Reinforcement Learning with Verifiable Rewards… | BETA | Non |
| 6 | PT-06 — Evaluation Comparative du Post-Training | BETA | Non |
| 7 | PT-07 — Détecter le reward hacking avec rewardspy | BETA | Oui |
| 8 | PT-08 — GRPO from scratch : la mécanique du signal de… | BETA | Non |
| 9 | PT-09 — RLOO (REINFORCE Leave-One-Out) from scratch :… | BETA | Oui |
| 10 | PT-10 — GAE from scratch : pourquoi un mini-critic ?… | BETA | Non |
| 11 | PT-11 — GRPO + RLVR sur Qwen3.5-0.8B : la série… | BETA | Non |
| 12 | PT-11 — RLVR sur VRAI LLM (Qwen3.5-0.8B) +… | BETA | Non |
| 13 | PT-11b — RLVR multi-seed sur Qwen3.5-0.8B (4 seeds ×… | ALPHA | Non |
| 14 | PT-11c — RLVR sur Qwen3-1.7B/2B (cran au-dessus de… | ALPHA | Non |
| 15 | PT-12 — Crédit différé multi-step : GAE-λ sur un… | ALPHA | Oui |
| 16 | PT-13 — Les trois biais du loss GRPO et leurs… | ALPHA | Oui |

## GenAI/RAG-et-Memoire-Semantique (10 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Hands-On Grounding — Qdrant en mémoire | BETA | Oui |
| 2 | 02 — Retrieval avancé : HyDE, reranking et évaluation | BETA | Oui |
| 3 | Embeddings from scratch — word2vec skip-gram, la… | BETA | Oui |
| 4 | Tokenisation from scratch — l'unité de compte de tout… | ALPHA | Oui |
| 5 | Stockage vectoriel réel — persistance, index ANN (HNSW)… | BETA | Oui |
| 6 | RAG 05b — Mode serveur Qdrant : compromis exact/ANN ef… | BETA | Non |
| 7 | 06 — Kernel Memory in-process : la couche d'abstraction… | BETA | Non |
| 8 | RAG 07 — Kernel Memory Python : ingestion, recherche et… | BETA | Non |
| 9 | RAG 08 — Kernel Memory et la recherche hybride : BM25 +… | BETA | Non |
| 10 | RAG 09 — Au-delà du texte : le plafond multimodal du… | BETA | Non |

## GenAI/SemanticKernel (15 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | SK-1-Fundamentals : Introduction a Semantic Kernel | BETA | Non |
| 2 | SK-2-Functions : Function Calling, Memory et… | BETA | Non |
| 3 | SK-3-Agents : Agent Framework Semantic Kernel | BETA | Non |
| 4 | SK-4-Filters : Filtres et Observabilite | BETA | Non |
| 5 | SK-5-VectorStores : RAG avec Qdrant | BETA | Non |
| 6 | SK-6-ProcessFramework : Workflows et Orchestration | BETA | Non |
| 7 | SK-7-MultiModal : Images, Audio et Vision | BETA | Non |
| 8 | SK-8-MCP : Model Context Protocol et Integration | BETA | Non |
| 9 | SK-9-Building-CLR : Interoperabilite Python/.NET via… | BETA | Non |
| 10 | SK-10-NotebookMaker : Système Multi-Agents pour… | BETA | Non |
| 11 | Conception Automatique de Notebook par Agents IA | BETA | Non |
| 12 | Projet Createur de Mail personnalise | BETA | Non |
| 13 | Notebook de travail — Titanic: exploration, préparation… | BETA | Oui |
| 14 | Notebook de conception de Notebook | BETA | Non |
| 15 | Jeu de devinette : Père Fouras vs Laurent Jalabert | BETA | Non |

## GenAI/Texte (29 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | 10. Hébergement Local de Modèles Génératifs | BETA | Non |
| 2 | 10b. Mécanique d'inférence LLM : construire et mesurer… | BETA | Non |
| 3 | 10c. Stratégies pour contextes longs — budget de… | BETA | Non |
| 4 | 10d. TensorSharp : pilote d'inférence LLM native .NET | BETA | Non |
| 5 | 10e. LLamaSharp : bake-off binding .NET de llama.cpp | BETA | Non |
| 6 | 10f. ONNX Runtime GenAI : jambe finale du bake-off .NET | BETA | Non |
| 7 | 11. Quantization | BETA | Non |
| 8 | 12. Test Time Scaling | BETA | Non |
| 9 | 13. Orchestration agentique du test-time scaling | BETA | Non |
| 10 | 13b — Évaluation d'agents : succès, coût, ablation et… | BETA | Non |
| 11 | 14. Memoire persistante pour le test-time scaling | BETA | Non |
| 12 | 15. Tree-of-Thoughts sur de vrais problemes de… | BETA | Non |
| 13 | 16. Scaling du test-time compute (Snell 2024) | BETA | Non |
| 14 | 17. Modèles a raisonnement natif vs scaling du… | BETA | Non |
| 15 | 18. Plugins Semantic Kernel pour le test-time scaling | BETA | Non |
| 16 | 19. Orchestration et tâches planifiées avec Open WebUI… | BETA | Non |
| 17 | 1. Introduction a l'IA generative avec l'API OpenAI | BETA | Non |
| 18 | 20. OWUI Native API v0.9.6 — introspection REST et… | BETA | Non |
| 19 | 22 — Évaluer les sorties générées : BLEU, ROUGE,… | BETA | Non |
| 20 | TAL — du mot aux dépendances : le pipeline linguistique… | BETA | Oui |
| 21 | 2. Prompt Engineering : Techniques Avancées | ALPHA | Non |
| 22 | 3. Structured Outputs : Sorties JSON Garanties | BETA | Non |
| 23 | Function Calling : Connecter les LLMs au Monde Réel | BETA | Non |
| 24 | 5. RAG Modern - Retrieval Augmented Generation | BETA | Non |
| 25 | PDF et Web Search : Sources Documentaires avec OpenAI | BETA | Non |
| 26 | Code Interpreter : Exécution de Code avec OpenAI | BETA | Non |
| 27 | 8. Reasoning Models | BETA | Non |
| 28 | 9. Production Patterns | BETA | Non |
| 29 | 9b. Prompt Security & Red-Teaming sur notre stack… | BETA | Non |

## GenAI/Vibe-Coding (8 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Claude CLI - Les Bases | BETA | Oui |
| 2 | Claude CLI - Gestion des Sessions | BETA | Oui |
| 3 | Claude CLI - References et Contexte | BETA | Oui |
| 4 | Claude CLI - Agents et Subagents | BETA | Oui |
| 5 | Claude CLI - Automatisation Avancee | BETA | Non |
| 6 | Claude Code via Claudish | BETA | Non |
| 7 | CSharpRepl attache a un process .NET vivant | ALPHA | Oui |
| 8 | Garde-fous Roslyn pour le code genere par agent | BETA | Oui |

## GenAI/Video (21 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Opérations de Base sur les Videos | BETA | Non |
| 2 | GPT-5 Video Understanding - Comprehension Video par IA | BETA | Non |
| 3 | Qwen2.5-VL Video Analysis - Comprehension Video Locale | BETA | Non |
| 4 | Video Enhancement - Real-ESRGAN et Interpolation de… | ALPHA | Non |
| 5 | AnimateDiff - Introduction a la Generation… | BETA | Non |
| 6 | HunyuanVideo | BETA | Non |
| 7 | LTX-Video - Generation Video Rapide et Legere | BETA | Non |
| 8 | Wan 2.1/2.2 - Generation Video Multilingue | BETA | Non |
| 9 | SVD - Stable Video Diffusion (Image-to-Video) | ALPHA | Non |
| 10 | LTX-2 - Generation Audiovisuelle Conjointe (Video +… | BETA | Non |
| 11 | MiniMax H3 (Hailuo 3.0) — Architecture, capacités… et… | BETA | Non |
| 12 | CogVideoX - Generation Video depuis Texte (Open… | BETA | Non |
| 13 | Comparaison Multi-Modèles de Generation Video | BETA | Non |
| 14 | Orchestration de Pipelines Video | ALPHA | Non |
| 15 | ComfyUI - Workflows Video via API | BETA | Non |
| 16 | Generation de Videos Educatives | BETA | Non |
| 17 | Workflows Video Creatifs | BETA | Non |
| 18 | Sora API - Generation Video Cloud | BETA | Non |
| 19 | Pipeline Video de Production | BETA | Non |
| 20 | MiniMax H3 (Hailuo) — Génération vidéo par le service… | BETA | Non |
| 21 | MiniMax video-01 (v1) — Service cloud generation video… | BETA | Non |
