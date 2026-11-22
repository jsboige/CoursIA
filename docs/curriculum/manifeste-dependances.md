# Manifeste des dependances du cursus

Fichier genere par `scripts/notebook_tools/dependency_manifest.py` (#27544) sur `351d2e840d99f3c7fd8ad09143a05a634216f9fc`, sans reseau. Politique : `scripts/notebook_tools/dependency_manifest_policy.json`. Ne pas editer a la main : la sortie est regeneree a chaque execution de l'organe.

Mesure : 1996 carnets, fichiers de dependances du cursus et hors cursus, 15 series, 283 groupes de repertoires, 72 groupes inclus dans l'image CPU, 47 conflits de versions.

**Origine des motifs** : `mesure` = deduit d'une lecture du depot ; `declaration` = regle ecrite dans la politique versionnee, contestable.

## 1. Table par serie et sous-serie

| Groupe | Serie | Sous-serie | Noyaux | Fichiers de dependances | Carnets | GPU | Cle d'API (nb) | Service reseau | Verdict | Service optionnel | Motifs (origine) | Lacunes de declaration |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `MyIA.AI.Notebooks` |  | - | .NET | aucun | 1 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/CaseStudies` | CaseStudies | - | Python | MyIA.AI.Notebooks/CaseStudies/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Diagnostic-Medical/solution` | CaseStudies | Diagnostic-Medical | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Diagnostic-Medical/student` | CaseStudies | Diagnostic-Medical | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Planification-Oncologie/solution` | CaseStudies | Planification-Oncologie | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Planification-Oncologie/student` | CaseStudies | Planification-Oncologie | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Reseau-Electrique-Intelligent/solution` | CaseStudies | Reseau-Electrique-Intelligent | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/CaseStudies/Reseau-Electrique-Intelligent/student` | CaseStudies | Reseau-Electrique-Intelligent | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/GameTheory` | GameTheory | - | Python, .NET, autre, Rust | MyIA.AI.Notebooks/GameTheory/requirements.txt | 130 | non | 2 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | scikit-learn, torch |
| `MyIA.AI.Notebooks/GameTheory/Coalitions` | GameTheory | Coalitions | Python, autre | aucun | 5 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics` | GameTheory | Dynamics | .NET, Python, autre, Rust | aucun | 21 | non | 2 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux` | GameTheory | Metajeux | .NET, Python | aucun | 9 | non | - | - | **inclus** | non | - | torch |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice` | GameTheory | SocialChoice | .NET, Python, autre, Rust | aucun | 21 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/GameTheory/gateway` | GameTheory | gateway | Python | MyIA.AI.Notebooks/GameTheory/gateway/requirements.txt | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/GenAI` | GenAI | - | Python, autre, .NET | MyIA.AI.Notebooks/GenAI/requirements-audio.txt, MyIA.AI.Notebooks/GenAI/requirements-video.txt, MyIA.AI.Notebooks/GenAI/requirements.txt | 0 | non | - | - | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : fichier de dependances optionnel : MyIA.AI.Notebooks/GenAI/requirements-audio.txt, MyIA.AI.Notebooks/GenAI/requirements-video.txt | - |
| `MyIA.AI.Notebooks/GenAI/00-GenAI-Environment` | GenAI | 00-GenAI-Environment | Python | aucun | 7 | oui | 5 | ComfyUI, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 9 | pyyaml |
| `MyIA.AI.Notebooks/GenAI/3D` | GenAI | 3D | Python, autre | aucun | 9 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 4 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation` | GenAI | Audio | Python | aucun | 5 | oui | 2 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced` | GenAI | Audio | Python, autre | aucun | 12 | oui | 4 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 11 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 7 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/03-Orchestration` | GenAI | Audio | Python, autre | aucun | 5 | oui | 2 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/04-Applications` | GenAI | Audio | Python | aucun | 6 | oui | 4 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-Audiobook` | GenAI | Audio | Python | aucun | 6 | non | 5 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 16 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-Musique` | GenAI | Audio | autre, Python | aucun | 6 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 5 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-Voix` | GenAI | Audio | Python | aucun | 3 | non | 2 | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/05-Diffusion-from-scratch` | GenAI | Audio | Python | aucun | 2 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Audio/06-Diffusion-SOTA` | GenAI | Audio | Python | aucun | 3 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/_archive` | GenAI | Audio | Python | aucun | 1 | oui | - | orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : orchestrateur GenAI / TTS API, orchestrateur GenAI / Whisper API ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/CaseStudies/Barbie-Schreck` | GenAI | CaseStudies | Python | aucun | 1 | non | 1 | ComfyUI | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI | - |
| `MyIA.AI.Notebooks/GenAI/CaseStudies/Fort-Boyard` | GenAI | CaseStudies | Python | aucun | 2 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot` | GenAI | CaseStudies | Python | aucun | 2 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/CaseStudies/Recipe-Maker` | GenAI | CaseStudies | Python | aucun | 1 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/FallacyDetection` | GenAI | FallacyDetection | Python | aucun | 5 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/FineTuning` | GenAI | FineTuning | Python | aucun | 20 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 19 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | peft |
| `MyIA.AI.Notebooks/GenAI/HumorDetection` | GenAI | HumorDetection | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Image/01-Foundation` | GenAI | Image | Python | aucun | 9 | non | 5 | ComfyUI | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 27 | - |
| `MyIA.AI.Notebooks/GenAI/Image/02-Advanced` | GenAI | Image | Python, autre | aucun | 5 | oui | 6 | ComfyUI | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 10 | - |
| `MyIA.AI.Notebooks/GenAI/Image/03-Orchestration` | GenAI | Image | Python | aucun | 4 | oui | 2 | ComfyUI | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 4 | - |
| `MyIA.AI.Notebooks/GenAI/Image/04-Applications` | GenAI | Image | Python | aucun | 6 | non | 6 | ComfyUI | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 7 | - |
| `MyIA.AI.Notebooks/GenAI/Image/05-History` | GenAI | Image | Python | aucun | 8 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Image/examples` | GenAI | Image | Python | aucun | 3 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 10 | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet` | GenAI | Integrations-DotNet | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire` | GenAI | Integrations-DotNet | .NET | aucun | 11 | non | - | ComfyUI, Forge (SD.Next) | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI, Forge (SD.Next) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/CSharpRepl` | GenAI | Integrations-DotNet | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/CopilotSDK` | GenAI | Integrations-DotNet | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Orleans` | GenAI | Integrations-DotNet | .NET | aucun | 4 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Scrutor` | GenAI | Integrations-DotNet | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots` | GenAI | Plateformes-Conversationnelles | Python | aucun | 7 | non | 4 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 16 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-2-Forms` | GenAI | Plateformes-Conversationnelles | Python | aucun | 2 | non | 1 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-3-RAG-et-Embeddings` | GenAI | Plateformes-Conversationnelles | Python | aucun | 2 | non | 5 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-4-MCP-Server` | GenAI | Plateformes-Conversationnelles | Python | aucun | 4 | non | 5 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 8 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-5-Multi-Provider` | GenAI | Plateformes-Conversationnelles | Python | aucun | 3 | non | 3 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/05-Playwright-AI-Engine` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | 2 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/06-Securite-et-Methode` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 5 | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/01-decouverte` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/02-navigation-authentification` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/04-rag-tools-avances` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10` | GenAI | Plateformes-Conversationnelles | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/PostTraining` | GenAI | PostTraining | Python, .NET | MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt | 27 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 11 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique` | GenAI | RAG-et-Memoire-Semantique | Python, .NET | aucun | 18 | oui | 4 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 33 | - |
| `MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/_archive` | GenAI | RAG-et-Memoire-Semantique | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Capability` | GenAI | Security | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 3 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Control` | GenAI | Security | Python | aucun | 1 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Security/Oversight` | GenAI | Security | Python | aucun | 7 | non | 2 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 4 | - |
| `MyIA.AI.Notebooks/GenAI/Security/RedTeam` | GenAI | Security | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Tooling` | GenAI | Security | Python | aucun | 1 | non | 2 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel` | GenAI | SemanticKernel | Python, .NET | aucun | 25 | non | 3 | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 8 | - |
| `MyIA.AI.Notebooks/GenAI/Texte` | GenAI | Texte | Python, .NET | MyIA.AI.Notebooks/GenAI/Texte/requirements-structured-outputs.txt | 45 | oui | 8 | TTS (FishAudio), orchestrateur GenAI / TTS | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 8 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : TTS (FishAudio), orchestrateur GenAI / TTS ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 37 | peft, trl |
| `MyIA.AI.Notebooks/GenAI/Texte/TransformerVariants` | GenAI | Texte | Python | aucun | 7 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/01-decouverte/demo-2-references-contexte/ressources/projet-exemple` | GenAI | Vibe-Coding | - | MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/01-decouverte/demo-2-references-contexte/ressources/projet-exemple/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks` | GenAI | Vibe-Coding | Python | aucun | 5 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/notebooks` | GenAI | Vibe-Coding | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/analyzers` | GenAI | Vibe-Coding | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/GenAI/Video/01-Foundation` | GenAI | Video | Python | aucun | 6 | oui | 1 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/Video/02-Advanced` | GenAI | Video | Python | aucun | 8 | oui | 3 | ComfyUI | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 6 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/GenAI/Video/03-Orchestration` | GenAI | Video | Python | aucun | 3 | oui | 4 | ComfyUI | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | - |
| `MyIA.AI.Notebooks/GenAI/Video/04-Applications` | GenAI | Video | Python | aucun | 6 | oui | 2 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) | - |
| `MyIA.AI.Notebooks/GenAI/_research` | GenAI | _research | .NET, Python | aucun | 2 | oui | 4 | ComfyUI | **exclu** | oui | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), bitsandbytes, torchaudio, torchvision) ; declaration : service conteneurise requis (patron Planners) : ComfyUI ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 9 | - |
| `MyIA.AI.Notebooks/IIT` | IIT | - | Python, autre | MyIA.AI.Notebooks/IIT/requirements.txt | 10 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series` | IIT | ICT-Series | autre, Python, .NET | MyIA.AI.Notebooks/IIT/ICT-Series/requirements-torchlens.txt | 69 | oui | 1 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 4 carnet(s) de la serie ; mesure : conflit de versions d'interpreteur : MyIA.AI.Notebooks/IIT/ICT-Series/pyproject.toml [tool.coursia.pinned_env.requires-python] exige Python >=3.9,<3.10, le noyau canonique ict-py313 est Python 3.13 ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 5 | datasets, peft, scikit-learn, torch, transformers, trl |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-02-SelfSortingMorphogenesis` | IIT | ICT-Series | Python | aucun | 3 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-05-CausalEmergence` | IIT | ICT-Series | autre, Python | aucun | 3 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats` | IIT | ICT-Series | Python | aucun | 5 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity` | IIT | ICT-Series | Python, .NET, autre | aucun | 13 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine` | IIT | ICT-Series | Python | aucun | 3 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie | torch |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes` | IIT | ICT-Series | Python | aucun | 6 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie | torch |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity` | InformationCalcul | Complexity | .NET, Python, Rust | aucun | 46 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression` | InformationCalcul | Compression | .NET, Python | aucun | 18 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 12 | torch |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression_lean` | InformationCalcul | Compression | autre | aucun | 1 | non | - | - | **exclu** | non | mesure : noyau non-Python (autre) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/InformationCalcul/InformationTheory` | InformationCalcul | InformationTheory | Python | aucun | 2 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks` | ML | DataScienceWithAgents | Python | aucun | 6 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours` | ML | DataScienceWithAgents | Python, .NET, autre | MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/requirements.txt | 49 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), torchvision) | transformers |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning` | ML | DataScienceWithAgents | .NET, Python | aucun | 31 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 12 carnet(s) de la serie | diffusers, scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/_archive` | ML | DataScienceWithAgents | Python | aucun | 3 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie | torch, torchvision |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision` | ML | DataScienceWithAgents | .NET, Python, autre | MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/requirements.txt | 15 | oui | 2 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 12 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), torchvision) | python-dotenv |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/05-Wavelet-Scattering` | ML | DataScienceWithAgents | Python | aucun | 6 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie | scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees` | ML | DataScienceWithAgents | Python | MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/requirements.txt | 0 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day1-Foundations/Labs` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day2-Document-Agents/Labs/Lab2-RFP-Analysis` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day2-Document-Agents/Labs/Lab3-CV-Screening` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day3-Data-Agents/Labs/Lab4-DataWrangling` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day3-Data-Agents/Labs/Lab5-Viz-ML` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day3-Data-Agents/Labs/Lab6-First-Agent` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day3-Data-Agents/Labs/Lab7-Data-Analysis-Agent` | ML | DataScienceWithAgents | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents` | ML | DataScienceWithAgents | Python | MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/requirements.txt | 0 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day4-Foundations` | ML | DataScienceWithAgents | Python | aucun | 2 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star` | ML | DataScienceWithAgents | Python | aucun | 7 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day6-MLE-Star` | ML | DataScienceWithAgents | Python | aucun | 3 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day7-Production` | ML | DataScienceWithAgents | Python | aucun | 2 | non | 1 | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/ML/ML.Net` | ML | ML.Net | .NET, Python | aucun | 29 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 4 | scikit-learn |
| `MyIA.AI.Notebooks/NLP` | NLP | - | Python, .NET | aucun | 20 | non | - | - | **inclus** | non | - | scikit-learn |
| `MyIA.AI.Notebooks/Physique/Chaines` | Physique | Chaines | Python, .NET | aucun | 14 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Physique/Constructeur` | Physique | Constructeur | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Physique/InformationQuantique` | Physique | InformationQuantique | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Physique/Integrales` | Physique | Integrales | Python | aucun | 4 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Physique/Jauge` | Physique | Jauge | Python | aucun | 4 | non | - | - | **inclus** | non | - | torch |
| `MyIA.AI.Notebooks/Physique/Numerique` | Physique | Numerique | Python | aucun | 2 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/Probas` | Probas | - | Python | MyIA.AI.Notebooks/Probas/requirements.txt | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Applications` | Probas | Applications | Python | aucun | 4 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation` | Probas | Applications | Python, autre | aucun | 8 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Causalite` | Probas | Causalite | Python | aucun | 12 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory` | Probas | DecisionTheory | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat` | Probas | DecisionTheory | Python | aucun | 5 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer` | Probas | DecisionTheory | .NET, autre, Python | aucun | 12 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC` | Probas | DecisionTheory | Python | aucun | 8 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Fondations` | Probas | Fondations | .NET, Python | aucun | 4 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Infer` | Probas | Infer | .NET, Python | aucun | 22 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/Probas/Infer/gateway` | Probas | Infer | - | MyIA.AI.Notebooks/Probas/Infer/gateway/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/Probas/Infer/scripts` | Probas | Infer | - | MyIA.AI.Notebooks/Probas/Infer/scripts/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/Probas/PyMC` | Probas | PyMC | Python | aucun | 20 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/QuantConnect` | QuantConnect | - | Python, autre, .NET | MyIA.AI.Notebooks/QuantConnect/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline` | QuantConnect | ML-Training-Pipeline | Python | aucun | 18 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/Python` | QuantConnect | Python | Python, autre | aucun | 66 | oui | 2 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 9 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/Python/research` | QuantConnect | Python | Python | aucun | 2 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean` | QuantConnect | kelly_lean | autre, Python | aucun | 6 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal` | QuantConnect | partner-course-quant-trading | Python | aucun | 4 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Sector-Momentum` | QuantConnect | partner-course-quant-trading | Python | aucun | 4 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/01-ML-RandomForest` | QuantConnect | partner-course-quant-trading | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/02-ML-XGBoost` | QuantConnect | partner-course-quant-trading | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/03-Framework-Composite` | QuantConnect | partner-course-quant-trading | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/AllWeather` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/BTC-ML` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/CSharp-BTC-EMA-Cross` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/CSharp-BTC-MACD-ADX` | QuantConnect | projects | .NET, Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/CSharp-CTG-Momentum` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Chronos-Foundation-Forecasting` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Congress-Trades-Copy` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Corrective-AI` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Crypto-LSTM-Prediction` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/DL-LSTM` | QuantConnect | projects | Python | aucun | 1 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/DualMomentum` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/DynamicVIXSpyRegime-QC` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Index` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Stocks` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Ensemble-DLinear-TFT` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/FamaFrench` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Filing-Language-Stability` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ForexCarry` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_FamaFrenchAllWeather` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_MomentumRegime` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/FuturesTrend` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Gaussian-Direction-Classifier` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/GraphSAGE-MultiAsset-Ranking` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/HAR-RV-Kelly` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/InverseVolatility-Rank` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/LSTM-Forecasting` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/LongShortHarvest-QC` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-Classification` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning` | QuantConnect | projects | Python | aucun | 1 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-EnhancedPairs` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-Ensemble` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-FeatureEngineering` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment` | QuantConnect | projects | Python | aucun | 1 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-HeadShoulders-CNN` | QuantConnect | projects | Python | aucun | 1 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-RandomForest` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-Regression` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-Reversion-Trending` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-SVM` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-TextClassification` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Mamba-Crypto-Ranking` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/MomentumStrategy` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Option-Wheel` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Options-VGT` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/OptionsIncome` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/PairsTrading` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid/paper_harness` | QuantConnect | projects | - | MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid/paper_harness/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) ; declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-Optimization-ML` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/RL-Options-Hedging` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/RL-Portfolio` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/RegimeSwitching` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Reinforcement-Learning-Trading` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor` | QuantConnect | projects | Python | aucun | 10 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/RiskParity` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Sector-ML-Classification` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/SectorMomentum` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Sparse-Index-Tracking-QC` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Stoploss-Volatility-ML` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/TFT-Crypto-Ranking` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/Temporal-CNN-Prediction` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Trend-Following` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/TrendFilteredMeanReversion` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/TrendStocks-Alpha` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/TrendStocksLite` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/TurnOfMonth` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/VIX-TermStructure` | QuantConnect | projects | Python | aucun | 2 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Vol-Ensemble-Conservative` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Vol-GARCH-Target` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/_docs` | QuantConnect | projects | Python | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | - |
| `MyIA.AI.Notebooks/QuantConnect/research` | QuantConnect | research | Python | aucun | 26 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (TensorFlow) | torch |
| `MyIA.AI.Notebooks/RL` | RL | - | Python, .NET | MyIA.AI.Notebooks/RL/requirements.txt | 32 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/RL/PostTraining` | RL | PostTraining | .NET, Python | aucun | 12 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 3 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | peft |
| `MyIA.AI.Notebooks/Search` | Search | - | .NET, Python, Rust, autre | MyIA.AI.Notebooks/Search/requirements.txt | 0 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations` | Search | Part1-Foundations | .NET, Python, Rust, autre | MyIA.AI.Notebooks/Search/Part1-Foundations/requirements-automata.txt | 60 | oui | 1 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 2 carnet(s) de la serie | - |
| `MyIA.AI.Notebooks/Search/Part2-CSP` | Search | Part2-CSP | .NET, Python, Rust | aucun | 22 | non | 1 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques` | Search | Part3-Cas-pratiques | .NET, Python | aucun | 54 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Search/Part4-Metaheuristics` | Search | Part4-Metaheuristics | .NET, Python | MyIA.AI.Notebooks/Search/Part4-Metaheuristics/requirements-mgs-tsp.txt | 26 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-vs-mealpy` | Search | Part4-Metaheuristics | .NET | aucun | 10 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/Search/Part5-Frontieres` | Search | Part5-Frontieres | Python, .NET | aucun | 15 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Search/_archive` | Search | _archive | Python | aucun | 2 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/Sudoku` | Sudoku | - | .NET, Python, Rust, autre | MyIA.AI.Notebooks/Sudoku/requirements.txt | 46 | oui | 1 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (JAX, PyTorch (roues CUDA)) | python-dotenv |
| `MyIA.AI.Notebooks/SymbolicAI` | SymbolicAI | - | .NET | aucun | 1 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis` | SymbolicAI | ArgumentAnalysis | Python | MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/requirements.txt | 39 | non | 3 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 11 | scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/_archive` | SymbolicAI | ArgumentAnalysis | Python | aucun | 4 | non | 1 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/groupe-I2-contre-arguments-aspic` | SymbolicAI | ArgumentAnalysis | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean` | SymbolicAI | Lean | Python, autre | MyIA.AI.Notebooks/SymbolicAI/Lean/requirements.txt | 48 | oui | 4 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie | torch |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE` | SymbolicAI | Lean | Python, .NET, Rust, autre | aucun | 25 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GALOIS` | SymbolicAI | Lean | Python | aucun | 1 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GOL` | SymbolicAI | Lean | Python, autre | aucun | 12 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 4 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH` | SymbolicAI | Lean | autre, Python | aucun | 6 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry` | SymbolicAI | Lean | Python | aucun | 8 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS` | SymbolicAI | Lean | Python, .NET | aucun | 7 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands` | SymbolicAI | Lean | Python, autre | aucun | 7 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/MIMO` | SymbolicAI | Lean | Python, autre | aucun | 4 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200` | SymbolicAI | Lean | Python | aucun | 13 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100` | SymbolicAI | Lean | Python, autre | aucun | 34 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF` | SymbolicAI | Lean | autre, Python | aucun | 7 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests` | SymbolicAI | Lean | - | MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/requirements.txt | 0 | non | - | - | **inclus** | non | declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners` | SymbolicAI | Planners | Python, .NET, autre | MyIA.AI.Notebooks/SymbolicAI/Planners/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/00-Environment` | SymbolicAI | Planners | Python | aucun | 1 | non | - | planners-fast-downward | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : service conteneurise requis (patron Planners) : planners-fast-downward ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation` | SymbolicAI | Planners | .NET, Python | aucun | 6 | non | - | planners-fast-downward | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : service conteneurise requis (patron Planners) : planners-fast-downward | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical` | SymbolicAI | Planners | .NET, Python, autre | aucun | 8 | non | - | planners-fast-downward | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : service conteneurise requis (patron Planners) : planners-fast-downward ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 4 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/03-Advanced` | SymbolicAI | Planners | .NET, Python | aucun | 7 | non | - | planners-fast-downward | **exclu** | oui | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; declaration : service conteneurise requis (patron Planners) : planners-fast-downward ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 3 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/04-NeuroSymbolic` | SymbolicAI | Planners | Python | aucun | 4 | oui | 4 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | python-dotenv |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/_archive` | SymbolicAI | Planners | .NET | aucun | 1 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) ; mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API` | SymbolicAI | SMT | .NET, Python | MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/requirements.txt | 41 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway` | SymbolicAI | SMT | - | MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/requirements.txt | 0 | non | - | - | **inclus** | non | declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3` | SymbolicAI | SMT | .NET | aucun | 20 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python ; mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb` | SymbolicAI | SemanticWeb | .NET, Python | MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/requirements.txt | 28 | non | 2 | - | **inclus** | non | - | python-dotenv, scikit-learn |
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/RDF.Net-Legacy` | SymbolicAI | SemanticWeb | .NET | aucun | 1 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts` | SymbolicAI | SmartContracts | Python, autre | MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements-optional.txt, MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements.txt | 0 | non | - | - | **service optionnel** | oui | declaration : fichier de dependances optionnel : MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements-optional.txt | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations` | SymbolicAI | SmartContracts | Python | aucun | 4 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/01-Solidity-Foundation` | SymbolicAI | SmartContracts | Python | aucun | 4 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced` | SymbolicAI | SmartContracts | Python, autre | aucun | 8 | non | 1 | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing` | SymbolicAI | SmartContracts | Python | aucun | 3 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/04-Privacy-Cryptography` | SymbolicAI | SmartContracts | Python | aucun | 3 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/05-Alternative-Chains` | SymbolicAI | SmartContracts | Python, autre | aucun | 5 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/06-Real-World` | SymbolicAI | SmartContracts | Python | aucun | 5 | non | 1 | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning` | SymbolicAI | SymbolicLearning | .NET, Python, autre | MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/requirements.txt | 30 | oui | 1 | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 4 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | tensorflow, torchvision |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/_archive/2026-07-04-Neurosymbolic-EML-precurseur-SL12` | SymbolicAI | SymbolicLearning | Python | aucun | 2 | oui | - | - | **exclu** | non | mesure : GPU requis : marqueur mesure dans 1 carnet(s) de la serie ; declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA)) | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/difflogic/experiments` | SymbolicAI | SymbolicLearning | - | MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/difflogic/experiments/requirements.txt | 0 | non | - | - | **exclu** | non | declaration : taille : distribution(s) lourde(s) hors image CPU legere (PyTorch (roues CUDA), torchvision) ; declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety` | SymbolicAI | Tweety | Python, .NET, autre | MyIA.AI.Notebooks/SymbolicAI/Tweety/requirements.txt | 38 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/_probes` | SymbolicAI | Tweety | .NET | aucun | 1 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |
| `MyIA.AI.Notebooks/SymbolicAI/_archive` | SymbolicAI | _archive | Python | aucun | 1 | non | - | - | **inclus** | non | mesure : appel(s) de service dont l'URL n'est pas lisible sur la ligne de l'appel : 3 | - |
| `MyIA.AI.Notebooks/cross-series/AgentSystems` | cross-series | AgentSystems | Python | aucun | 2 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/cross-series/NotionsInteractives` | cross-series | NotionsInteractives | Python | aucun | 1 | non | - | - | **inclus** | non | - | - |
| `MyIA.AI.Notebooks/cross-series/matching-cv` | cross-series | matching-cv | - | MyIA.AI.Notebooks/cross-series/matching-cv/requirements.txt | 0 | non | - | - | **inclus** | non | declaration : aucun carnet dans ce groupe ni dans ses sous-repertoires : famille de noyau non mesurable ; l'absence de mesure n'exclut pas le groupe | - |
| `MyIA.AI.Notebooks/cross-series/socle-metadata-driven` | cross-series | socle-metadata-driven | .NET | aucun | 2 | non | - | - | **exclu** | non | mesure : noyau non-Python (.NET) : hors image CPU Python | - |

## 2. Conflits de versions

| Paquet | Classe | Specifications en presence | Sources | Resolution proposee |
|---|---|---|---|---|
| `accelerate` | specifier_divergent | >=0.25.0, >=0.30.0, >=1.0.0 | >=0.25.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.30.0 (MyIA.AI.Notebooks/GenAI/requirements-video.txt); >=1.0.0 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.0.0 |
| `anthropic` | specifier_divergent | >=0.18.0, >=0.20.0, >=0.21.0, >=0.25.0 | >=0.18.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=0.20.0 (MyIA.AI.Notebooks/SymbolicAI/Lean/requirements.txt); >=0.21.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.25.0 (MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.25.0 |
| `audiocraft` | specifier_divergent | >=1.0.0, >=1.3.0 | >=1.0.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=1.3.0 (MyIA.AI.Notebooks/GenAI/requirements-audio.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.3.0 |
| `automata-lib` | specifier_divergent | >=7.1.0, >=9.2.0 | >=7.1.0 (MyIA.AI.Notebooks/Search/Part1-Foundations/requirements-automata.txt); >=9.2.0 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=9.2.0 |
| `bitsandbytes` | specifier_divergent | >=0.41.0, >=0.43.0, >=0.44.0 | >=0.41.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.43.0 (MyIA.AI.Notebooks/GenAI/requirements-video.txt); >=0.44.0 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.44.0 |
| `black` | specifier_divergent | >=23.0.0, >=24.0.0 | >=23.0.0 (MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/01-decouverte/demo-2-references-contexte/ressources/projet-exemple/requirements.txt); >=24.0.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=24.0.0 |
| `cvxpy` | specifier_divergent | >=1.4.0, >=1.5 | >=1.4.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=1.5 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.5 |
| `datasets` | specifier_divergent | >=2.14.0, >=3.0.0, >=5.0 | >=2.14.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=3.0.0 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt); >=5.0 (MyIA.AI.Notebooks/RL/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=5.0 |
| `demucs` | specifier_divergent | >=4.0.0, >=4.0.1 | >=4.0.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=4.0.1 (MyIA.AI.Notebooks/GenAI/requirements-audio.txt) | retenir l'intersection des bornes (la plus stricte) -> >=4.0.1 |
| `diffusers` | specifier_divergent | >=0.24.0, >=0.30.0 | >=0.24.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.30.0 (MyIA.AI.Notebooks/GenAI/requirements-video.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.30.0 |
| `faster-whisper` | specifier_divergent | >=0.10.0, >=1.0.0 | >=0.10.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=1.0.0 (MyIA.AI.Notebooks/GenAI/requirements-audio.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.0.0 |
| `flake8` | specifier_divergent | >=6.0.0, >=7.0.0 | >=6.0.0 (MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/01-decouverte/demo-2-references-contexte/ressources/projet-exemple/requirements.txt); >=7.0.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=7.0.0 |
| `httpx` | specifier_divergent | >=0.27,<1, >=0.27.0 | >=0.27,<1 (MyIA.AI.Notebooks/GenAI/Texte/requirements-structured-outputs.txt); >=0.27.0 (MyIA.AI.Notebooks/GenAI/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.27,<1 |
| `ipykernel` | specifier_divergent | >=6.0.0, >=6.29.0 | >=6.0.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/requirements.txt); >=6.29.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=6.29.0 |
| `ipywidgets` | specifier_divergent | >=8.0.0, >=8.1 | >=8.0.0 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=8.1 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=8.1 |
| `jupyter-kernel-gateway` | specifier_divergent | >=3.0, >=3.0,<4 | >=3.0 (MyIA.AI.Notebooks/GameTheory/gateway/requirements.txt); >=3.0,<4 (MyIA.AI.Notebooks/Probas/Infer/gateway/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=3.0,<4 |
| `langchain` | specifier_divergent | >=0.1.0, >=0.3.0 | >=0.1.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=0.3.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.3.0 |
| `langchain-openai` | specifier_divergent | >=0.0.5, >=0.2.0 | >=0.0.5 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=0.2.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.2.0 |
| `matplotlib` | specifier_divergent | >=3.5, >=3.7, >=3.7,<3.11 | >=3.5 (MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements.txt); >=3.7 (MyIA.AI.Notebooks/CaseStudies/requirements.txt); >=3.7,<3.11 (MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=3.7,<3.11 |
| `moviepy` | specifier_divergent | >=1.0, >=2.0,<3 | >=1.0 (MyIA.AI.Notebooks/RL/requirements.txt); >=2.0,<3 (MyIA.AI.Notebooks/GenAI/requirements-video.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.0,<3 |
| `nest-asyncio` | specifier_divergent | >=1.5, >=1.6.0 | >=1.5 (MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/requirements.txt); >=1.6.0 (MyIA.AI.Notebooks/SymbolicAI/Lean/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.6.0 |
| `networkx` | specifier_divergent | >=3.0, >=3.1 | >=3.0 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=3.1 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=3.1 |
| `numpy` | specifier_divergent | >=1.21,<2.0, >=1.24, >=1.24,<2.5 | >=1.21,<2.0 (MyIA.AI.Notebooks/IIT/requirements.txt); >=1.24 (MyIA.AI.Notebooks/CaseStudies/requirements.txt); >=1.24,<2.5 (MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.24,<2.0 |
| `open-spiel` | specifier_divergent | >=1.4, >=2.0 | >=1.4 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=2.0 (MyIA.AI.Notebooks/GameTheory/gateway/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.0 |
| `openai` | specifier_divergent | ==2.24.0, >=1.0, >=1.12.0, >=1.55,<3, >=2.0.0 | ==2.24.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/requirements.txt); >=1.0 (MyIA.AI.Notebooks/Sudoku/requirements.txt); >=1.12.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=1.55,<3 (MyIA.AI.Notebooks/GenAI/Texte/requirements-structured-outputs.txt); >=2.0.0 (MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.0.0,<3 |
| `optuna` | specifier_divergent | >=3.0, >=3.5.0 | >=3.0 (MyIA.AI.Notebooks/Search/requirements.txt); >=3.5.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=3.5.0 |
| `ortools` | specifier_divergent | >=9.11, >=9.8 | >=9.11 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=9.8 (MyIA.AI.Notebooks/CaseStudies/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=9.11 |
| `pyarrow` | specifier_divergent | >=14.0.0, >=26.0.0 | >=14.0.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=26.0.0 (MyIA.AI.Notebooks/GameTheory/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=26.0.0 |
| `pydantic` | specifier_divergent | ==2.12.5, >=2.6.0, >=2.7,<3 | ==2.12.5 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/requirements.txt); >=2.6.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=2.7,<3 (MyIA.AI.Notebooks/GenAI/Texte/requirements-structured-outputs.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.7,<3 |
| `pydantic-settings` | specifier_divergent | >=2.0.0, >=2.1.0 | >=2.0.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/requirements.txt); >=2.1.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.1.0 |
| `pydub` | specifier_divergent | >=0.25.0, >=0.25.1 | >=0.25.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.25.1 (MyIA.AI.Notebooks/GenAI/requirements-audio.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.25.1 |
| `pytest` | specifier_divergent | >=7.0.0, >=8.0.0 | >=7.0.0 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=8.0.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=8.0.0 |
| `python-sat` | specifier_divergent | >=0.1, >=0.1.8, >=1.8.dev13 | >=0.1 (MyIA.AI.Notebooks/SymbolicAI/Tweety/requirements.txt); >=0.1.8 (MyIA.AI.Notebooks/GameTheory/requirements.txt); >=1.8.dev13 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.8.dev13 |
| `qwen-vl-utils` | specifier_divergent | >=0.0.1, >=0.0.8 | >=0.0.1 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=0.0.8 (MyIA.AI.Notebooks/GenAI/requirements-video.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.0.8 |
| `rdflib` | specifier_divergent | >=7.0, >=7.0.0,<8.0.0 | >=7.0 (MyIA.AI.Notebooks/CaseStudies/requirements.txt); >=7.0.0,<8.0.0 (MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=7.0,<8.0.0 |
| `requests` | specifier_divergent | >=2.28, >=2.31 | >=2.28 (MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements.txt); >=2.31 (MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.31 |
| `scikit-learn` | specifier_divergent | ==1.5.2, >=1.2, >=1.3 | ==1.5.2 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/requirements.txt); >=1.2 (MyIA.AI.Notebooks/Probas/requirements.txt); >=1.3 (MyIA.AI.Notebooks/Search/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.3 |
| `scipy` | specifier_divergent | ==1.14.1, >=0.13.3, >=1.10, >=1.11,<1.19, >=1.11.0 | ==1.14.1 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/requirements.txt); >=0.13.3 (MyIA.AI.Notebooks/IIT/requirements.txt); >=1.10 (MyIA.AI.Notebooks/Probas/requirements.txt); >=1.11,<1.19 (MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/requirements.txt); >=1.11.0 (MyIA.AI.Notebooks/GenAI/requirements-audio.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.11,<1.19 |
| `semantic-kernel` | specifier_divergent | >=1.0, >=1.39.0 | >=1.0 (MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/requirements.txt); >=1.39.0 (MyIA.AI.Notebooks/SymbolicAI/Lean/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.39.0 |
| `stable-baselines3` | specifier_divergent | >=2.0, >=2.2.0 | >=2.0 (MyIA.AI.Notebooks/RL/requirements.txt); >=2.2.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=2.2.0 |
| `torch` | incompatible | ==2.14.0, >=2.0, >=2.0,<2.12, >=2.1.0, >=2.13 | ==2.14.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/requirements.txt); >=2.0 (MyIA.AI.Notebooks/CaseStudies/requirements.txt); >=2.0,<2.12 (MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/requirements.txt); >=2.1.0 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt); >=2.13 (MyIA.AI.Notebooks/RL/requirements.txt) | aucune version commune : le paquet est ecarte du manifeste consolide -> paquet ecarte |
| `torchvision` | specifier_divergent | ==0.29.0, >=0.15.0 | ==0.29.0 (MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/requirements.txt); >=0.15.0 (MyIA.AI.Notebooks/GenAI/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.15.0 |
| `tqdm` | specifier_divergent | >=4.65, >=4.66.0 | >=4.65 (MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/requirements.txt); >=4.66.0 (MyIA.AI.Notebooks/GenAI/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=4.66.0 |
| `transformers` | specifier_divergent | >=4.35.0, >=4.37.0, >=4.40.0, >=5.12, >=5.15.0 | >=4.35.0 (MyIA.AI.Notebooks/GenAI/requirements.txt); >=4.37.0 (MyIA.AI.Notebooks/QuantConnect/requirements.txt); >=4.40.0 (MyIA.AI.Notebooks/GenAI/requirements-video.txt); >=5.12 (MyIA.AI.Notebooks/RL/requirements.txt); >=5.15.0 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=5.15.0 |
| `trl` | specifier_divergent | >=1.10, >=1.9.2 | >=1.10 (MyIA.AI.Notebooks/RL/requirements.txt); >=1.9.2 (MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=1.10 |
| `yfinance` | specifier_divergent | >=0.2, >=0.2.36 | >=0.2 (MyIA.AI.Notebooks/Probas/requirements.txt); >=0.2.36 (MyIA.AI.Notebooks/QuantConnect/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=0.2.36 |
| `z3-solver` | specifier_divergent | >=4.12, >=4.13 | >=4.12 (MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/requirements.txt); >=4.13 (MyIA.AI.Notebooks/CaseStudies/requirements.txt) | retenir l'intersection des bornes (la plus stricte) -> >=4.13 |

## 3. Manifeste consolide (source unique des paquets de l'image)

| Paquet | Version retenue | Groupes | Conflit |
|---|---|---|---|
| `agent-framework-openai` | a resoudre | 1 | non |
| `anthropic` | a resoudre | 13 | oui |
| `antropy` | a resoudre | 5 | non |
| `automata-lib` | a resoudre | 6 | oui |
| `axelrod` | a resoudre | 6 | non |
| `chromadb` | a resoudre | 1 | non |
| `cvxpy` | a resoudre | 6 | oui |
| `deap` | a resoudre | 6 | non |
| `dowhy` | a resoudre | 6 | non |
| `duckduckgo-search` | a resoudre | 5 | non |
| `eth-tester` | a resoudre | 7 | non |
| `fastapi` | a resoudre | 1 | non |
| `flask` | a resoudre | 1 | non |
| `google-adk` | 2.8.0 | 5 | non |
| `google-cloud-aiplatform` | a resoudre | 5 | non |
| `google-cloud-bigquery` | a resoudre | 5 | non |
| `google-generativeai` | a resoudre | 5 | non |
| `graphviz` | a resoudre | 12 | non |
| `httpx` | a resoudre | 1 | oui |
| `ipykernel` | a resoudre | 13 | oui |
| `ipywidgets` | a resoudre | 12 | oui |
| `jpype1` | a resoudre | 4 | non |
| `jupyter` | a resoudre | 13 | non |
| `jupyter-kernel-gateway` | a resoudre | 2 | oui |
| `jupyterlab` | a resoudre | 5 | non |
| `kaggle` | a resoudre | 5 | non |
| `kglab` | a resoudre | 1 | non |
| `langchain` | a resoudre | 13 | oui |
| `langchain-community` | a resoudre | 8 | non |
| `langchain-core` | a resoudre | 8 | non |
| `langchain-experimental` | a resoudre | 13 | non |
| `langchain-openai` | a resoudre | 13 | oui |
| `langgraph` | a resoudre | 8 | non |
| `litellm` | 1.100.4 | 5 | non |
| `matching` | a resoudre | 1 | non |
| `matplotlib` | a resoudre | 53 | oui |
| `mealpy` | a resoudre | 6 | non |
| `mlflow` | a resoudre | 5 | non |
| `mpyc` | a resoudre | 7 | non |
| `nashpy` | a resoudre | 6 | non |
| `nest-asyncio` | a resoudre | 15 | oui |
| `networkx` | a resoudre | 14 | oui |
| `numpy` | a resoudre | 31 | oui |
| `open-spiel` | a resoudre | 6 | oui |
| `openai` | 2.24.0 | 28 | oui |
| `opentelemetry-sdk` | a resoudre | 1 | non |
| `optuna` | a resoudre | 11 | oui |
| `ortools` | a resoudre | 12 | oui |
| `owlready2` | a resoudre | 1 | non |
| `owlrl` | a resoudre | 1 | non |
| `pandas` | a resoudre | 27 | non |
| `papermill` | a resoudre | 6 | non |
| `phe` | a resoudre | 7 | non |
| `playwright` | a resoudre | 1 | non |
| `pulp` | a resoudre | 6 | non |
| `py-ecc` | a resoudre | 7 | non |
| `py-evm` | a resoudre | 7 | non |
| `py-solc-x` | a resoudre | 7 | non |
| `pyarrow` | a resoudre | 6 | oui |
| `pycryptodome` | a resoudre | 7 | non |
| `pydantic` | 2.12.5 | 5 | oui |
| `pydantic-settings` | a resoudre | 5 | oui |
| `pyemd` | 0.5.1 | 5 | non |
| `pygad` | a resoudre | 6 | non |
| `pymoo` | a resoudre | 6 | non |
| `pyphi` | 1.2.0 | 5 | non |
| `pyshacl` | a resoudre | 1 | non |
| `pytest` | a resoudre | 9 | oui |
| `pytest-asyncio` | a resoudre | 1 | non |
| `pytest-html` | a resoudre | 1 | non |
| `pytest-playwright` | a resoudre | 1 | non |
| `python-bitcoinlib` | a resoudre | 7 | non |
| `python-constraint` | a resoudre | 6 | non |
| `python-dotenv` | a resoudre | 34 | non |
| `python-sat` | a resoudre | 16 | oui |
| `pyvis` | a resoudre | 1 | non |
| `rdflib` | a resoudre | 1 | oui |
| `reasonable` | a resoudre | 1 | non |
| `requests` | a resoudre | 12 | oui |
| `rustuna` | a resoudre | 6 | non |
| `scikit-learn` | a resoudre | 20 | oui |
| `scipy` | a resoudre | 17 | oui |
| `seaborn` | a resoudre | 19 | non |
| `semantic-kernel` | a resoudre | 16 | oui |
| `sparqlwrapper` | a resoudre | 1 | non |
| `sympy` | a resoudre | 6 | non |
| `tabulate` | a resoudre | 7 | non |
| `tavily-python` | a resoudre | 5 | non |
| `tenseal` | a resoudre | 7 | non |
| `torchlens` | 3.0.3 | 4 | non |
| `tqdm` | a resoudre | 8 | oui |
| `uvicorn` | a resoudre | 1 | non |
| `vyper` | a resoudre | 7 | non |
| `web3` | a resoudre | 7 | non |
| `werkzeug` | a resoudre | 1 | non |
| `xrpl-py` | a resoudre | 7 | non |
| `z3-solver` | a resoudre | 15 | oui |

## 4. Lacunes de declaration

Paquets **importes** par les carnets d'un groupe mais **absents** de ses fichiers de dependances : l'image ne les installera pas, le carnet echouera a l'execution. La correspondance import -> paquet est une declaration (voir la politique) ; l'absence dans les fichiers de dependances est une mesure.

| Groupe | Paquets importes non declares |
|---|---|
| `MyIA.AI.Notebooks/GameTheory` | scikit-learn, torch |
| `MyIA.AI.Notebooks/GameTheory/Metajeux` | torch |
| `MyIA.AI.Notebooks/GenAI/00-GenAI-Environment` | pyyaml |
| `MyIA.AI.Notebooks/GenAI/FineTuning` | peft |
| `MyIA.AI.Notebooks/GenAI/Texte` | peft, trl |
| `MyIA.AI.Notebooks/IIT/ICT-Series` | datasets, peft, scikit-learn, torch, transformers, trl |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine` | torch |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes` | torch |
| `MyIA.AI.Notebooks/InformationCalcul/Compression` | torch |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours` | transformers |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning` | diffusers, scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/_archive` | torch, torchvision |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision` | python-dotenv |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/05-Wavelet-Scattering` | scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/ML/ML.Net` | scikit-learn |
| `MyIA.AI.Notebooks/NLP` | scikit-learn |
| `MyIA.AI.Notebooks/Physique/Jauge` | torch |
| `MyIA.AI.Notebooks/QuantConnect/Python` | torch |
| `MyIA.AI.Notebooks/QuantConnect/Python/research` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/Crypto-LSTM-Prediction` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/DL-LSTM` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/Ensemble-DLinear-TFT` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/GraphSAGE-MultiAsset-Ranking` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/Mamba-Crypto-Ranking` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/RL-Options-Hedging` | torch |
| `MyIA.AI.Notebooks/QuantConnect/projects/TFT-Crypto-Ranking` | torch |
| `MyIA.AI.Notebooks/QuantConnect/research` | torch |
| `MyIA.AI.Notebooks/RL/PostTraining` | peft |
| `MyIA.AI.Notebooks/Sudoku` | python-dotenv |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis` | scikit-learn, torch, torchvision |
| `MyIA.AI.Notebooks/SymbolicAI/Lean` | torch |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/04-NeuroSymbolic` | python-dotenv |
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb` | python-dotenv, scikit-learn |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning` | tensorflow, torchvision |

## 5. Divergences canonique/observe (organe #23073)

| Bibliotheque | Canonique | Versions observees |
|---|---|---|
| `CsvHelper` | 33.0.1 | 27.1.1 (1 carnets), 33.0.1 (1 carnets) |
| `IKVM` | 8.15.0 | 8.14.0 (1 carnets), 8.15.0 (25 carnets) |
| `Microsoft.ML` | 5.0.0 | 4.0.2 (1 carnets), 5.0.0 (12 carnets) |
| `dotNetRDF` | 3.5.2 | 3.4.1 (13 carnets), 3.5.2 (2 carnets) |
| `pythonnet` | 3.1.0 | 3.0.5 (26 carnets), 3.1.0 (28 carnets), 3.2.1 (1 carnets) |

## 6. Fichiers de dependances hors cursus

Ces fichiers servent l'outillage et les services, pas les series : ils n'entrent pas dans le manifeste de l'image.

- `docker-configurations/notebook-runner/requirements-learning.lock.txt`
- `docker-configurations/notebook-runner/requirements-learning.txt`
- `docker-configurations/services/comfyui-qwen/workspace/requirements.txt`
- `docker-configurations/services/orchestrator/requirements.txt`
- `scripts/genai-stack/requirements.txt`
- `scripts/notebook_tools/requirements.txt`
- `scripts/sudoku/requirements.txt`
