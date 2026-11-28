# Prévol Colab — matrice des trois parcours

> À jour au 2026-11-28. Livrable du critère 4 de l'issue #23276, porté dans le dépôt
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
| **vibe-coding / Claude-CLI** | `Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb` | CPU / API — aucun modèle local (CLI `claude` en subprocess) | `curl -fsSL https://claude.ai/install.sh \| bash` (ou `npm i -g @anthropic-ai/claude-code`, Node ≥ 18). Sous Colab, la voie npm est mesurée (2026-11-25) : code retour 0 en 11,5 s, binaire dans `/tools/node/bin`, déjà dans le `PATH` du runtime | `ANTHROPIC_BASE_URL` + `ANTHROPIC_AUTH_TOKEN` (`.env`) ; ou `claude auth login` | appels API payants (1× haiku → 15× opus) ; `SIMULATION_MODE` = sans quota | aucune | import helpers → `verify_installation()` → `check_claude_status()` → 1er `run_claude("Bonjour")` — **mesuré le 2026-11-28** : cycle agentique complet (2 tours d'outils, fichier réellement écrit). Sous Colab (`root`), **`--dangerously-skip-permissions` est refusé** : employer `--allowedTools Write Bash Read` |
| **Semantic Kernel** | `SemanticKernel/01-SemanticKernel-Intro.ipynb` | CPU / API — kernel local orchestrateur, modèle OpenAI distant | `pip install semantic-kernel` — **mesuré le 2026-11-28** : code retour 0 en **52,6 s**, version installée **1.47.0** | `OPENAI_API_KEY` (+ `OPENAI_BASE_URL`, `OPENAI_CHAT_MODEL_ID`) via `load_dotenv()` + `os.getenv` ; sous Colab, `userdata.get("OPENAI_API_KEY")` — **mesuré** : sans clé, `add_service(OpenAIChatCompletion(...))` échoue sur `ServiceInitializationError: The OpenAI API key is required.` | appels API ; « coût croissant » (historique réenvoyé à chaque tour) | aucune dans le code (seulement lecture du plugin) | `__version__` → `load_dotenv()` + clés → test `AsyncOpenAI` → `Kernel()` → `add_service(OpenAIChatCompletion)` — `__version__`, `Kernel()` et le chemin « clé absente » sont **mesurés** (2026-11-28) ; le plugin `FunPlugin` est **bloqué** sous Colab (voir « Bloqueurs » ci-dessous) |
| **fine-tuning / post-training** | `FineTuning/FT-01-Introduction-FineTuning-Python.ipynb` | **GPU** — plancher ~4 Go VRAM (GPT-2 124 M) ; run committé sur 17.2 Go ; repli CPU = 5-10 min ; **le runtime Colab gratuit mesuré le 2026-11-28 n'a pas de GPU** (`torch 2.14.1+cpu`, `cuda: false`) | aucune cellule d'install dans le carnet (imports directs `torch` / `transformers` / `peft` / `datasets`) ; **mesuré le 2026-11-28** : `pip install transformers peft datasets accelerate` code retour 0 en 2,0 s | `HF_TOKEN` (téléchargement du Hub ; sans jeton = débit limité) | rate-limit de téléchargement HF Hub (pas de quota API) | `save_pretrained()` → adaptateur LoRA 1.18 Mo ; checkpoints d'entraînement désactivés (`save_strategy="no"`) ; **mesuré le 2026-11-28** : l'adaptateur LoRA **n'a pas été produit** (voir « Bloqueurs ») | check `torch.cuda` → chargement `openai-community/gpt2` (**mesuré : 10,2 s**) → 1er entraînement LoRA — la dernière étape est **bloquée** sous Colab gratuit (voir « Bloqueurs ») |

## Mesuré vs évalué — ce que cette lane a et n'a pas établi

- **Mesuré** (preuve dans le fil de #23276, dans les PRs mergées et dans les passes
  Colab datées) : **les trois parcours** ont désormais un facts measured dans un
  runtime Colab réel.
  - **Claude-CLI** — trois fois : le 2026-11-07, puis le 2026-11-25 depuis un poste
    de la flotte, dans un runtime Colab réel (installation `npm`, emplacement du
    binaire, survie au redémarrage de session, héritage d'environnement entre
    cellules, *Secrets*, et les trois états de la CLI sans clé), puis le
    **2026-11-28**, où un **cycle agentique complet** a été mesuré : 3 appels
    `POST /v1/messages`, 2 tours d'outils, fichier **réellement écrit** sur disque,
    `num_turns: 3`, `is_error: false`, `terminal_reason: "completed"`. Les deux
    passes du 2026-11-25 sont **sans clé** : l'appel facturé n'y est pas mesuré.
    Sur la passe du 2026-11-28, le modèle distant était un **serveur local** (SSE) :
    la plomberie est mesurée, la **réponse du modèle distant ne l'est pas**.
  - **Semantic Kernel** — le 2026-11-28 : installation (52,6 s), version (1.47.0),
    création du `Kernel()` et chemin « clé absente » mesurés dans un runtime Colab
    réel. Le plugin du carnet n'y est **pas** atteignable (voir « Bloqueurs »).
  - **fine-tuning / post-training** — le 2026-11-28 : `torch` / CUDA, paquets
    `transformers` / `peft` / `datasets` et chargement de GPT-2 mesurés dans un
    runtime Colab réel. Le **pas LoRA** est resté bloqué et **aucun adaptateur n'a
    été produit** (voir « Bloqueurs »).
- **Ce qui reste hors mesure** : la **réponse du modèle distant** (Anthropic,
  OpenAI, OpenRouter). Aucun appel facturé n'a été émis depuis Colab : ce maillon
  est couvert par la **clé de module** du TP, pas par cette lane — c'est
  volontairement le seul geste que la procédure laisse à l'étudiant.
- **Ce qui n'est pas rejoué tel quel** : le run fine-tuning cité dans le carnet
  (4,2 s, carte 17,2 Go) reste la **sortie committée** du carnet, pas une mesure
  Colab — le 2026-11-28 n'a pas mesuré de GPU.

## Bloqueurs honnêtes — ce qui a arrêté chaque parcours

Mesurés le 2026-11-28 dans un runtime Colab réel (Linux 6.6.159, Python 3.13.18,
Node v22.23.4, `cwd=/content`).

| Parcours | Ce qui a marché | Bloqueur | Correctif |
|---|---|---|---|
| **Claude-CLI** | install `npm`, `claude --version`, les trois états sans clé, cycle agentique complet (2 tours d'outils, fichier écrit) | deux : (a) Colab tourne en **root** → `--dangerously-skip-permissions` refusé (`cannot be used with root/sudo privileges for security reasons`) ; (b) l'appel **facturé** exige la clé de module | (a) `--allowedTools Write Bash Read` (mesuré fonctionnel) ; (b) déposer la clé de module en *Secret* Colab, lue par `userdata.get()` |
| **Semantic Kernel** | install (52,6 s), version 1.47.0, `Kernel()`, message d'erreur « clé absente » | le dossier `./prompt_template_samples` **n'existe pas** sous Colab : `ModuleNotFoundError: No module named 'prompt_template_samples'` | cloner le dépôt dans le runtime (ou monter le dossier) avant d'importer le plugin |
| **fine-tuning** | `torch`, paquets, chargement de GPT-2 (10,2 s) | (a) **pas de GPU** : `torch 2.14.1+cpu`, `cuda: false` ; (b) `ImportError: Found an incompatible version of torchao. Found version 0.10.0, but only versions above 0.16.0 are supported` — le dispatcher LoRA de `peft` refuse le `torchao` présent | (a) demander un runtime **GPU** (un T4 16 Go suffit pour GPT-2 / LoRA) ; (b) `pip install -U torchao` (ou `pip uninstall -y torchao`) **avant** `get_peft_model` |

**Conséquence honnête sur le fine-tuning** : le 2026-11-28, `get_peft_model` a levé
**avant** de construire le wrapper LoRA ; la sauvegarde qui a suivi a donc écrit les
fichiers **du modèle de base** (`config.json`, `generation_config.json`,
`model.safetensors` — **pas** de `adapter_config.json`). Aucun adaptateur LoRA n'a
été produit : la ligne « `save_pretrained()` → adaptateur LoRA 1.18 Mo » de la
matrice décrit le **carnet**, pas cette mesure.

**Ce que la procédure laisse au student** : la clé de module. Tout le reste
(installations, câblage, lecture du secret, exécution) est dans le carnet et dans
cette matrice ; l'élève n'a besoin d'aucun accès à l'outillage interne.

## Recommandation pédagogique

- **Claude-CLI** — le plus prêt à lancer tel quel : 100 % API, tourne sur n'importe
  quel runtime Colab (CPU suffit). Prévol en séance ≈ 5 min : installer la CLI, poser
  les deux variables d'environnement, premier `claude -p` borné.
  **Attention au drapeau** : Colab tourne en `root`, donc
  `--dangerously-skip-permissions` est refusé — employer
  `--allowedTools Write Bash Read`, qui est la variante **mesurée**.
- **Semantic Kernel** — tout aussi CPU-suffisant (100 % API OpenAI). Prévol :
  `pip install semantic-kernel` + clé `OPENAI_API_KEY`, premier appel au kernel.
  **Attention en séance** : le plugin du carnet (`./prompt_template_samples`) n'est
  pas dans le runtime Colab — le préparer (dossier monté) ou traiter l'exercice
  du plugin sur une machine locale.
- **fine-tuning / post-training** — le seul parcours **GPU**. Réserver un runtime avec
  GPU (un T4 16 Go Colab suffit pour GPT-2 / LoRA, plancher ~4 Go) ; borner l'essai à
  quelques époques (~5 s sur la carte du carnet) et ne pas dépasser sans budget.
  **Deux prérequis de plus que le carnet** : un runtime **avec GPU**, et
  `pip install -U torchao` (ou la désinstallation de `torchao`) avant le premier
  `get_peft_model` — sans quoi le pas LoRA échoue et rien n'est sauvegardé.

## Sources

- Série Claude-CLI : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/`
- Série Semantic Kernel : `MyIA.AI.Notebooks/GenAI/SemanticKernel/`
- Série FineTuning : `MyIA.AI.Notebooks/GenAI/FineTuning/`
- Guide canonique : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/docs/OPENROUTER_SETUP.md`
  — sa section « La trace Colab sans clé (2026-11-25) » porte le tableau des faits mesurés
- Organe de prévol exécutable : `MyIA.AI.Notebooks/GenAI/shared/helpers/colab_preflight.py`
  (les trois parcours vérifiés en un `preflight()`, tests dans
  `MyIA.AI.Notebooks/GenAI/shared/helpers/tests/test_colab_preflight.py`)
- Issue : #23276 (trace Colab réelle ; collision #23281 / #23282 arbitrée, proxy obsolète)
