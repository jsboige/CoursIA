# Vibe-Coding — Carte des workspaces GenAI

Cartographie structurelle des workspaces logiques du périmètre GenAI, vérifiée first-hand depuis le disque le 2026-09-11 (commit `58f5940d57`). Cette carte accompagne l'audit issue #14526 : « Auditer et réorganiser les séries comme espaces de workspace ». Aucun déplacement n'a été effectué ; ce document est une **photographie** de l'existant et un **plan de migration proposé**, à valider avant toute exécution.

## Vue d'ensemble

Le périmètre Vibe-Coding + séries GenAI voisines couvre **9 workspaces logiques** (cf. scope #14526). Leur localisation dans le dépôt est hétérogène : **5 vivent sous `Vibe-Coding/`** (Claude Code, Roo Code, Claw Systems, Claudish + la sous-série Roslyn `analyzers/`), **5 vivent dans leurs séries natives** (Open WebUI, AI-Engine, SemanticKernel, Texte pour OWUI live, docker-configurations pour vLLM). La convention est : **workspace hub** sous `Vibe-Coding/` pour les front-ends d'usage codage/agentique ; **séries natives** partout ailleurs.

## Cartographie workspace → dossier

| Workspace logique | Dossier réel | Fichiers | Type | Justification |
|---|---:|---|---|---|
| **Claude Code** | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/` | 61 | workspace | 5 modules (découverte → automatisation avancée) + Scripts + workspaces + docs + notebooks |
| **Roo Code** | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Roo-Code/` | 279 | workspace | 5 modules + Corrections + Demo-Roo-Capabilities + Scripts + workspaces |
| **Claw Systems** (NanoClaw, Hermes, OpenClaw) | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claw-Systems/` | 16 | workspace | Agents autonomes conteneurisés (Telegram + cluster) ; 11 docs |
| **Claudish** | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/` | 8 | workspace | Proxy multi-provider (Anthropic ↔ GLM ↔ Qwen ↔ DeepSeek) |
| **MyIA.AgentSafetyAnalyzer** (sous-série Roslyn) | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/analyzers/` | 7 | sous-série technique | Production-ready des analyseurs prototypés dans `Vibe-Coding/docs/Roslyn-Code-Guardrails.ipynb` ; Epic #10473, sub-grain #10500b. **Non listé dans `Vibe-Coding/README.md` l.13-19** (oubli structurel) |
| **vLLM** | `docker-configurations/services/vllm-zimage/` | 3 | service Docker | Compose + env + README ; vit avec les autres services GenAI (ComfyUI, Forge, Whisper) |
| **Open WebUI** | `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/` + 2 notebooks dans `Texte/19-20_OWUI_*.ipynb` | 53 | plateforme | Tour de la plateforme + QA Playwright (6 modules) ; la plateforme **vit dans sa série native** |
| **AI-Engine (WordPress)** | `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/` | 52 | plateforme | Extension WordPress GenAI ; **LivresAgités** = parcours cas d'usage 04 |
| **SemanticKernel** (≈ sk-agent côté MCP) | `MyIA.AI.Notebooks/GenAI/SemanticKernel/` | 143 | SDK | 10+ notebooks Python + .NET Interactive ; multi-modalité, MCP, agents |
| **LivresAgités** | `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/04-Cas-Usage-livresagites/` | 1 parcours | cas d'usage | Terrain d'observation pour AI-Engine |
| **sk-agent (MCP)** | `docs/reference/slide-analyzer-sk-agent.md` + `slides/analysis/sk-agent-vision-compare-20260419.md` | 2 | MCP / doc transverse | Vision + multi-agent ; aussi listé dans `Vibe-Coding/docs/CLUSTER-ORCHESTRATION.md` l.50 |
| **Zoo** | (aucun) | — | n'existe pas | Tell c.988 ★ sustained. Confusion probable entre `RooVeterinaryInc.roo-cline` (extension officielle) et `ZooCodeOrganization.zoo-code` (fork) |

## Carte par catégories

Le scope #14526 demande de distinguer **workspace, sous-thème, consommateur et document transverse**.

### Workspaces (front-ends d'usage)

- **Assistants de codage** : Claude-Code, Roo-Code
- **Agents autonomes** : Claw-Systems (NanoClaw, Hermes, OpenClaw)
- **Plateformes GenAI** : Open-WebUI, AI-Engine-WordPress
- **Proxy multi-provider** : Claudish

### Sous-thèmes (spécialisations dans un workspace)

- **Claw-Systems** : NanoClaw (léger Telegram), Hermes (gateway + coordinateur cluster), OpenClaw (l'inspirateur historique, podcast Steinberger)
- **Open-WebUI** : Tour de la plateforme (`00-Tour-Plateforme/`), QA Playwright (`Playwright-OWUI/`, 6 modules)
- **AI-Engine-WordPress** : Architecture, Comparatif, Functional (chatbots/forms/RAG/MCP/multi-provider), Cas d'usage LivresAgités, Playwright, Sécurité & méthode

### Consommateurs (middleware en aval)

- **Claudish** consommé par Claude-Code, Roo-Code, Claw-Systems (route les requêtes Anthropic vers le provider choisi)
- **SemanticKernel** consommé par les MCP agents
- **docker-configurations/vllm-zimage** consommé par Open-WebUI (LLM backend)
- **vLLM** cité dans `Texte/19_OWUI_Orchestration.ipynb` (déploiement local)

### Documents transverses

- `Vibe-Coding/docs/CLUSTER-ORCHESTRATION.md` — orchestration cluster MyIA (coordinateur + workers) ; couvre RooSync + MCPs maison
- `Vibe-Coding/docs/COMPARAISON-CLAUDE-ROO.md` — guide comparatif détaillé Claude Code vs Roo Code
- `Vibe-Coding/docs/INTRO-GENAI.md` — introduction GenAI
- `docs/reference/slide-analyzer-sk-agent.md` + `slides/analysis/sk-agent-vision-compare-20260419.md` — usage de sk-agent vision
- `docs/genai/open-webui-orchestration.md` — orchestration Open WebUI

### Sous-série technique

- `Vibe-Coding/analyzers/` — `MyIA.AgentSafetyAnalyzer` (NuGet-ready, `netstandard2.0`) ; prototypes Roslyn du notebook `docs/Roslyn-Code-Guardrails.ipynb`. AGSEC001-005 (Process.Start non-constant, SQL concat, File.Read non-constant, HttpClient URL non-constante, credentials hardcodées).

## Convention observée

Le body de l'issue #14526 est explicite : **« Les séries existantes sont déjà les espaces de connaissances des workspaces : il ne faut pas créer une racine générique concurrente. »** Cette convention est déjà respectée pour Open WebUI (série native `Plateformes-Conversationnelles/`), AI-Engine (idem), SemanticKernel (série `SemanticKernel/`), vLLM (service Docker partagé), sk-agent (MCP listé dans la doc cluster), LivresAgités (cas d'usage dans sa plateforme).

Les 4 workspaces assistants/bots/proxy (Claude-Code, Roo-Code, Claw-Systems, Claudish) vivent sous `Vibe-Coding/` parce qu'ils partagent la **même fonction pédagogique** (ateliers de codage agentique + bots autonomes) et qu'il est légitime qu'ils partagent la même racine.

## Plan de migration proposé (à valider)

**Constat : aucun déplacement de workspace n'est nécessaire.** Voici pourquoi, workspace par workspace :

| Workspace | `git mv` proposé ? | Justification |
|---|---|---|
| Claude Code | non | déjà dans Vibe-Coding |
| Roo Code | non | déjà dans Vibe-Coding |
| Claw Systems | non | déjà dans Vibe-Coding |
| Claudish | non | déjà dans Vibe-Coding |
| vLLM | non | service Docker, vit avec ses pairs (ComfyUI, Forge, Whisper) |
| Open WebUI | non | plateforme GenAI, sa série native est `Plateformes-Conversationnelles/` |
| sk-agent | non | MCP server, vit avec les autres docs MCP |
| LivresAgités | non | cas d'usage dans AI-Engine (parcours 04) |
| Zoo | n/a | n'existe pas dans le dépôt |

**Lots `git mv` retenus pour validation coordinateur** (à exécuter dans une PR de suivi, **post-validation** de cette carte) :

1. **Lot 1 — `Vibe-Coding/README.md`** : extension de l'arborescence affichée (l.13-19) pour inclure `analyzers/`, ajout d'une section `## Workspaces documentés hors Vibe-Coding` listant Open-WebUI, AI-Engine-WordPress, SemanticKernel, Texte (OWUI), docker-configurations/vllm-zimage avec lien vers leur README racine. **0 déplacement**, 1 fichier modifié, ~30 lignes nettes.

2. **Lot 2 (optionnel)** — si la convention « page collective unique » est jugée préférable à l'extension de README : créer `Vibe-Coding/docs/WORKSPACES.md` comme page de navigation avec liens vers chaque README racine. **0 déplacement**, 1 fichier créé, ~50 lignes.

## Risques identifiés

| Risque | Éval first-hand | Validation recommandée |
|---|---|---|
| Liens README → séries déplacés | Aucun déplacement prévu. Les 5 liens transverses de `GenAI/README.md` (`Claude Code + Roo Code + Claw-Systems + Claudish` l.51, `OWUI & AI-Engine` l.53) pointent déjà vers les bons dossiers. | relecture `grep -rn 'Vibe-Coding/' docs/ MyIA.AI.Notebooks/GenAI/` post-validation |
| Catalogue `COURSE_CATALOG.generated.*` | Régénéré chaque nuit par `catalog-cron.yml` à 03:37 UTC sur `main`. Aucun déplacement ne touche la structure déclarée : `Vibe-Coding` reste 1 série, `Plateformes-Conversationnelles` reste 1 série, etc. | re-run `catalog-cron` après merge Lot 1 |
| Traductions FR/EN siblings | Lean uniquement (cf. `code-style.md` règle i18n). Aucun `.lean` n'est touché par cette PR. | n/a |
| Notebooks `.ipynb` | Aucun déplacement de notebook. 5 notebooks vivent dans `Vibe-Coding/docs/` (Roslyn + CSharpRepl) ; ils restent où ils sont. | n/a |
| Submodules | Aucun submodule touché. Les 5 submodules du dépôt (MetaGeneticSharp, Z3.Linq, Automata, Argumentum, semantic-fleet) sont indépendants. | n/a |

## Mesures first-hand

Toutes les mesures sont faites depuis le worktree `CoursIA-c1062-14526-vibe-coding-audit` sur `origin/main @ 58f5940d57` le 2026-09-11, via `find <dossier> -type f | wc -l` et `find <dossier> -name "*.ipynb" | wc -l`.

```bash
find MyIA.AI.Notebooks/GenAI/Vibe-Coding -type f | wc -l
# → 382 (Claude-Code 61 + Roo-Code 279 + Claw-Systems 16 + Claudish 8 + docs 11 + analyzers 7)

find MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles -type f | wc -l
# → 110 (Open-WebUI 53 + AI-Engine-WordPress 52 + racine 5)

find MyIA.AI.Notebooks/GenAI/SemanticKernel -type f | wc -l
# → 143

find MyIA.AI.Notebooks/GenAI/Texte -name "*.ipynb" | wc -l
# → 30 (dont 19_OWUI_Orchestration.ipynb + 20_OWUI_Native_API.ipynb)

find docker-configurations/services/vllm-zimage -type f | wc -l
# → 3
```

## Liens

- Issue #14526 : https://github.com/jsboige/CoursIA/issues/14526
- Issue parente #14525 : https://github.com/jsboige/CoursIA/issues/14525
- `Vibe-Coding/README.md` l.13-19 : structure actuelle annoncée (4 sous-dossiers, `analyzers/` absent)
- `GenAI/README.md` l.51, l.53 : liens transverses vers les séries natives
- Tell c.14947 ★★★ : 0 byte production touchée (audit read-only)
- Tell c.1502 strict : lane ne merge pas, lane ne réorganise pas à elle seule
