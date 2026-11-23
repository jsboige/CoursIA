# Prévol Colab — matrice des trois parcours

> À jour au 2026-11-11. Livrable du critère 4 de l'issue #23276, porté dans le dépôt
> (le Google Doc privé de la promotion est mis à jour séparément par le coordinateur).

## D'où vient cette matrice

Demande directe du mainteneur pendant le cours du 29 octobre 2026 : préparer la
prochaine séance — **vibe-coding / Claude Code CLI**, **Semantic Kernel** ou
**fine-tuning / post-training** — en vérifiant comment nos outils s'utilisent depuis
Google Colab. Un groupe avait présenté un TP Claude-cli sans parvenir à le faire
fonctionner sous Colab.

Le fil de #23276 a déjà établi, **mesuré dans un runtime réel** : la trace Colab
datée, l'obsolescence du proxy OpenRouter (la bascule passe par deux variables
d'environnement, PR #23282) et les corrections du guide `OPENROUTER_SETUP.md`. Ce
qu'il restait ouvert, et que ce document clôture, est le **prévol minimal** des
trois parcours, adossé aux **carnets existants** de chaque série : on ne crée pas
trois nouveaux TPs, on qualifie ce qui existe.

## Comment lire la matrice

- **CPU / API** — le parcours appelle une API distante (Anthropic, OpenAI, OpenRouter,
  Hugging Face) ; aucun modèle local n'est chargé, un runtime Colab **sans GPU** suffit.
- **GPU** — le parcours charge ou entraîne un modèle local ; il a besoin du GPU que
  Colab attribue au runtime (T4 16 Go en gratuit, A100 en payant). **On ne promet
  jamais un GPU gratuit** et on ne lance jamais un entraînement coûteux sans budget :
  le prévol de ce parcours se borne à vérifier qu'un essai **réduit** tient sur le
  matériel attribué.

| Parcours | Carnet existant (prévol) | Matériel | Installation | Clés / env | Quota | Persistance | Prévol minimal |
|---|---|---|---|---|---|---|---|
| **vibe-coding / Claude-CLI** | `Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb` | CPU / API — aucun modèle local (CLI `claude` en subprocess) | `curl -fsSL https://claude.ai/install.sh \| bash` (ou `npm i -g @anthropic-ai/claude-code`, Node ≥ 18) | `ANTHROPIC_BASE_URL` + `ANTHROPIC_AUTH_TOKEN` (`.env`) ; ou `claude auth login` | appels API payants (1× haiku → 15× opus) ; `SIMULATION_MODE` = sans quota | aucune | import helpers → `verify_installation()` → `check_claude_status()` → 1er `run_claude("Bonjour")` |
| **Semantic Kernel** | `SemanticKernel/01-SemanticKernel-Intro.ipynb` | CPU / API — kernel local orchestrateur, modèle OpenAI distant | `pip install semantic-kernel` (v. 1.43.0) | `OPENAI_API_KEY` (+ `OPENAI_BASE_URL`, `OPENAI_CHAT_MODEL_ID`) via `load_dotenv()` + `os.getenv` | appels API ; « coût croissant » (historique réenvoyé à chaque tour) | aucune dans le code (seulement lecture du plugin) | `__version__` → `load_dotenv()` + clés → test `AsyncOpenAI` → `Kernel()` → `add_service(OpenAIChatCompletion)` |
| **fine-tuning / post-training** | `FineTuning/FT-01-Introduction-FineTuning-Python.ipynb` | **GPU** — plancher ~4 Go VRAM (GPT-2 124 M) ; run committé sur 17.2 Go ; repli CPU = 5-10 min | aucune cellule d'install dans le carnet (imports directs `torch` / `transformers` / `peft` / `datasets`) | `HF_TOKEN` (téléchargement du Hub ; sans jeton = débit limité) | rate-limit de téléchargement HF Hub (pas de quota API) | `save_pretrained()` → adaptateur LoRA 1.18 Mo ; checkpoints d'entraînement désactivés (`save_strategy="no"`) | check `torch.cuda` → chargement `openai-community/gpt2` → 1er entraînement LoRA (10 époques, 4.2 s) |

## Mesuré vs évalué — ce que cette lane a et n'a pas établi

- **Mesuré** (preuve dans le fil de #23276 et dans les PRs mergées) : le parcours
  **Claude-CLI**. La bascule OpenRouter sans proxy, la trace Colab réelle datée, et
  les corrections du guide. La ligne Claude-CI de la matrice reproduit ce qui a été
  vérifié dans un runtime réel.
- **Évalué** (lu dans les cellules des carnets existants, **non re-testé** dans un
  runtime Colab par cette lane) : les lignes **Semantic Kernel** et **fine-tuning**.
  Cette lane n'a ni navigateur ni compte Google : elle extrait les faits
  d'installation, de matériel, de clés et de persistance **des carnets eux-mêmes**
  (chaque valeur est issue d'une cellule lue), elle ne les présente pas comme testés
  sous Colab. Le run fine-tuning cité (4.2 s, carte 17.2 Go) est la sortie **committée**
  du carnet, pas une mesure Colab. Un essai borné dans un runtime Colab réel reste à
  faire par une lane outillée navigateur.

## Recommandation pédagogique

- **Claude-CLI** — le plus prêt à lancer tel quel : 100 % API, tourne sur n'importe
  quel runtime Colab (CPU suffit). Prévol en séance ≈ 5 min : installer la CLI, poser
  les deux variables d'environnement, premier `claude -p` borné.
- **Semantic Kernel** — tout aussi CPU-suffisant (100 % API OpenAI). Prévol :
  `pip install semantic-kernel` + clé `OPENAI_API_KEY`, premier appel au kernel.
- **fine-tuning / post-training** — le seul parcours **GPU**. Réserver un runtime avec
  GPU (un T4 16 Go Colab suffit pour GPT-2 / LoRA, plancher ~4 Go) ; borner l'essai à
  quelques époques (~5 s sur la carte du carnet) et ne pas dépasser sans budget.

## Sources

- Série Claude-CLI : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/`
- Série Semantic Kernel : `MyIA.AI.Notebooks/GenAI/SemanticKernel/`
- Série FineTuning : `MyIA.AI.Notebooks/GenAI/FineTuning/`
- Guide canonique : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/docs/OPENROUTER_SETUP.md`
- Issue : #23276 (trace Colab réelle ; collision #23281 / #23282 arbitrée, proxy obsolète)
