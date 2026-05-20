# Cluster CoursIA - agents, GPUs, specialisations

Reference perenne sur la structure du cluster : machines, GPUs, workspaces RooSync, specialisations infrastructure. Pour les **regles de coordination** : cf [docs/architecture_mcp_roo.md](architecture_mcp_roo.md) (RooSync) + [CLAUDE.md](../CLAUDE.md) section A. Pour le **calendrier enseignement / scope par ecole** : cf [docs/teaching-context.md](teaching-context.md).

## Machines du cluster

| Machine | Role principal | GPUs | VRAM totale |
|---------|----------------|------|-------------|
| `myia-ai-01` | **Coordinateur** + tests universels + vLLM hosting + training BG GPU 2 + prover BG forensic | 3x RTX 4090 | 72 GB (3x 24) |
| `myia-po-2023` | Hote services GenAI Image/Audio/Video (8 Docker services) | RTX 3080 + eGPU RTX 3090 | 40 GB (16 + 24) |
| `myia-po-2024` | QC backtest + ML training (modeles <= 10M params) | RTX 3070 | 8 GB |
| `myia-po-2025` | Tracks intensives ML/audits + workspace EPITA (3 agents) | RTX 3080 Ti laptop | 16 GB |
| `myia-po-2026` | Lean prover + QC MCP + service embedding + reverse proxy `xx.myia.io` | RTX 3080 | 16 GB |

**Note po-2024/po-2025 swap previsionnel** : user prevoit de mettre la 3080 16GB en utilisation perenne (po-2025 mobile recoit la 3070 8GB, po-2024 fixe garde la 3080 16GB).

## Workspaces RooSync (cluster CoursIA)

Cluster simplifie depuis 2026-05-15 : **un workspace `CoursIA` par machine**, sauf po-2025 qui a 3 agents distincts pour 3 workspaces dedies (CoursIA + 2 EPITA).

| RooSync ID | Role | Capacite dispatch depuis ai-01 |
|-----------|------|--------------------------------|
| `myia-ai-01:CoursIA` | Coord + reviewer PR + merger + tests universels | (self) |
| `myia-po-2023:CoursIA` | GenAI Image/Audio/Video + audit notebooks (Search/CSP/Sudoku) | OUI |
| `myia-po-2024:CoursIA` | QC backtest + ML training (sweep + Sudoku-NN) | OUI |
| `myia-po-2025:CoursIA` | Tracks intensives CoursIA + thermal backoff | OUI (avec contrainte thermal) |
| `myia-po-2025:2026-Epita-Programmation-par-Contraintes` | Review/merge PRs etudiants PrCon | Exception "grand manitou" |
| `myia-po-2025:2026-Epita-Intelligence-Symbolique` | Veille thematique + enrichissement sujets EPITA-IS | Exception "grand manitou" |
| `myia-po-2026:CoursIA` | Lean prover + QC MCP + embeddings | OUI |

**Boundary EPITA workspaces** : par defaut "stay in your workspace" (CLAUDE.md global). Exception explicite user 2026-05-16 : ai-01 est coordinateur transverse "grand manitou de tous les cours IA", donc peut dispatcher `[INFO]` / `[ASK]` / `[DIRECTIVE]` vers les workspaces EPITA via `roosync_messages(action: "send")`. Limite executive : ai-01 ne merge PAS leurs PRs, ne commit PAS dans leurs branches, ne fait pas dashboard append direct sur leur dashboard.

**Workspace `myia-po-2023:GenAI_Series` est DEPRECATED** depuis 2026-05-15. Tout dispatch GenAI va sur `myia-po-2023:CoursIA` uniquement.

## ai-01 - topologie GPU (RTX 4090 x3)

Regle stricte : GPU 2 **doit etre occupee 24/7** par un training BG longue duree.

| GPU | Role | Etat normal |
|-----|------|-------------|
| GPU 0 RTX 4090 | vLLM `medium` (Qwen3.5-35B-A3B-GPTQ-Int4, TP=2 avec GPU 1) | ~23-24 GB VRAM occupee 24/7 |
| GPU 1 RTX 4090 | vLLM `medium` (TP=2 avec GPU 0) | ~23-24 GB VRAM occupee 24/7 |
| GPU 2 RTX 4090 | **vLLM `mini` + Training BG ai-01 dedie** | DOIT toujours etre occupee par training BG |

**Alias vLLM** :
- `mini` : OmniCoder-9B-AWQ-4bit, GPU 2, port 5001
- `medium` : Qwen3.5-35B-A3B-GPTQ-Int4, GPU 0+1 TP=2, port 5002

**Anti-patterns interdits sur ai-01** :
- Diagnostiquer GPU 0/1 VRAM ~24GB comme "zombie processes" ou "memory leak" - c'est vLLM, occupation normale
- Tenter de killer/reset les processes sur GPU 0/1 - casse vLLM = prover SearchAgent local KO
- Laisser GPU 2 idle "en attendant decision strategique" - toujours avoir une queue de trainings prets

A chaque reveil de session ai-01 :
1. `nvidia-smi --query-gpu=memory.used,utilization.gpu --format=csv -i 2`
2. Si GPU 2 memory.used < 500 MiB -> lancer immediatement un training BG (queue ci-dessous)
3. Si training BG tourne deja -> laisser, NE PAS killer pour relancer
4. Cible : trainings >= 8h (sweep multi-seed, walk-forward M8 re-run, GARCH Phase 1, HMM/PyMC)

## po-2025 - contrainte thermique RTX 3080 Ti (incident 2026-04-28)

3 crashs systeme en 1 journee sur training LSTM prolonge :
- TDR 141 + BSOD 0x9F (DRIVER_POWER_STATE_FAILURE)
- Idem repete dans la meme journee
- Hard hang firmware / shutdown thermique critique a 100C ACPI

Hardware : MSI GE76 12UHS, RTX 3080 Ti laptop. Pas de persistence mode (non supporte laptop). Throttle deja a 50W sous charge a 89C, malgre power limit 150W. Lid ouvert ameliore mais ne suffit pas.

**Regle ai-01** : trainings GPU non-supervises > 15 min sur po-2025 INTERDITS, sauf si :
- Pattern reuse `scripts/training/train_with_checkpoints.py` (outer supervisor checkpoint + thermal backoff `max_temp=80`, `cool_sleep=60`, `heartbeat=30`)
- Watchdog `nvidia-smi` polling avec auto-stop a 87C
- Batch size reduit + mixed precision FP16

Si user dit "OK GPU heavy po-2025" : verifier qu'il connait l'incident avant d'agir (override possible).

## po-2025 - 3 agents distincts

| Workspace | Role | Etat |
|-----------|------|------|
| `myia-po-2025:CoursIA` | Tracks intensives ML/audits avec backoff thermal | ACTIF |
| `myia-po-2025:2026-Epita-Programmation-par-Contraintes` | Review/merge PRs etudiants PrCon | EN ATTENTE PRs etudiants |
| `myia-po-2025:2026-Epita-Intelligence-Symbolique` | Veille sujets + enrichissement | ACTIF veille |

**Skills cross-workspace tappables** : po-2025 developpe des skills specifiques par workspace, mais ai-01 peut tapper l'agent qui a deja la skill fraiche. Exemple : formulaire eval ESGF cree par `po-2025:2026-Epita-PrCon` plutot que `po-2025:CoursIA`, parce que PrCon avait fait des formulaires GWorkspace+Playwright le meme jour.

## Specialisations infrastructure

### GenAI Image/Audio/Video -> po-2023

Hardware : RTX 3080 Ti 16GB + eGPU 3090 24GB. **8 services Docker GenAI** :
- Image : Qwen Image Edit, Z-Image/Lumina, SD Forge Turbo/Main, SD.Next
- Audio : Whisper STT, Kokoro TTS, MusicGen, Demucs
- Video : ComfyUI Video

**Regle user** : s'il y a du GenAI Image/Audio/Video, ca va a po-2023. Lui seul peut tester notebooks contre ses propres services locaux.

### GenAI Texte (vLLM) -> ai-01

Les 2 containers Texte tournent sur le **vLLM workspace de ai-01**, pas po-2023. Cf section GPU topology ci-dessus pour `mini`/`medium`.

### GenAI Embedding -> po-2026

Container embedding dedie sur po-2026. Tout agent peut consommer l'endpoint.

### Reverse proxy `xx.myia.io` -> po-2026

Sous-domaines publics qui pointent vers les services GenAI de po-2023. Permet validation **bout-en-bout** des notebooks GenAI (auth bearer + timeouts + latences reelles client-side) en plus du test localhost de po-2023.

**Sequence GenAI a 2 etapes** : po-2023 dev + test local, puis po-2026 (optionnel) re-validation via sous-domaine public. po-2026 intervient APRES po-2023, jamais a la place.

### QuantConnect MCP -> po-2024 + po-2026

Tokens API QC configures dans `.mcp.json` sur les 2 machines (Docker MCP server `quantconnect/mcp-server`). Ils peuvent `create_compile` + `create_backtest` sur QC Cloud.

**Polyvalence** : avoir le token QC ne signifie PAS perimetre exclusif. Ces agents peuvent etre dispatch sur n'importe quelle mission (audit, Lean, notebooks). Le token QC = capacite **supplementaire**.

**Contrainte rate limit** : MAX 10 appels API QC / minute entre **tous les agents**. Avant backtest, annonce obligatoire sur dashboard workspace CoursIA pour eviter contention.

### Lean / Mathlib -> po-2026

Specialisation `*.lean`, port social_choice, Lake build, reecriture preuves structurelles. ai-01 = secours (env Lean a installer si manquant). Cf [docs/lean-prover-state.md](lean-prover-state.md).

### Whisper API host -> po-2023

Rotation cle API geree par po-2023 lui-meme. **NON consomme** dans workspace CoursIA (verifie 2026-05-16, 0 .env actif avec WHISPER_API_KEY cote CoursIA).

## Table rapide dispatch

| Mission | Agent principal | Alternative / validation |
|---------|-----------------|--------------------------|
| GenAI Image/Audio/Video (containers + notebooks) | `po-2023:CoursIA` | po-2026 pour validation reverse proxy `xx.myia.io` |
| GenAI Texte / vLLM (containers) | `ai-01:CoursIA` | tout agent pour consommer l'endpoint |
| GenAI Embedding (container) | `po-2026:CoursIA` | tout agent pour consommer l'endpoint |
| QC backtest / strategie | `po-2024:CoursIA` | `po-2026:CoursIA` (tokens MCP) |
| QC ESGF org cleanup | `po-2024:CoursIA` | `po-2026:CoursIA` |
| Lean / Mathlib (port + preuves) | `po-2026:CoursIA` | ai-01 secours (env a installer) |
| Lean prover BG forensic | **`ai-01:CoursIA` systematique** | apres chaque PR / message po-2026 mentionnant sorry |
| Audit notebooks pedagogique | tout agent polyvalent | cross-check pour eviter double couverture |
| Execution Papermill notebooks | tout agent polyvalent | ai-01 = machine de test universelle prioritaire |
| Review PR + merge | `ai-01:CoursIA` (seul merger) | - |
| Test global bout-en-bout (tous kernels) | `ai-01:CoursIA` (priorite) | - |
| Training CNN moyen (~7M, batch 128) | po-2024 / po-2025 / po-2026 (3080 16GB) | mixed precision FP16, attention batch |
| Training CNN gros (>10M, batch >256) | ai-01 GPU 2 | po-2023 eGPU 3090 si dispo |
| Coordination cross-workspace EPITA | `ai-01:CoursIA` via `roosync_messages send` | exception "grand manitou" |

**Regle implicite** : tous les agents sont polyvalents sur la **pedagogie**. Les **specialisations sont infra/tokens/hardware**. ai-01 doit pouvoir tester partout (priorite pour installer envs manquants).

## Dispatch via Epic GitHub (sprints multi-stages)

Pour tout sprint / curriculum >= 3 etapes, creer **Epic GitHub** + sub-issues numerotees AVANT de dispatcher. Les agents lisent l'issue, voient leur prochain step, livrent la PR liee, prennent le step suivant **sans re-demander la coord**.

| Element | Format |
|---------|--------|
| Epic title | `[Epic] <Nom-curriculum> - <duration estimee>` |
| Epic body | objectif + tableau stages (S1..SN) + dependencies graph + methodologie |
| Epic labels | `epic`, `<domain>` (ex `ml-trading`, `lean-prover`) |
| Sub-issue title | `S<N> - <objectif> (<agent cible>)` |
| Sub-issue body | prerequis (cite stage precedent), deliverables, gate GO/NO-GO verifiable, criteres methodologie (multi-seed, walk-forward, OOS), branch name attendu `feature/sN-<topic>` |
| Sub-issue labels | `stage-sN`, `<domain>` |
| Sub-issue linker | `Depends on #<previous>`, `Part of #<epic>` |
| Dispatch RooSync | 5 lignes max, pointeur vers issue, "Suivant = #<N+1> auto-dechaine apres ta PR mergee" |

**Anti-pattern interdit** : dispatch `roosync_messages send` decrivant une seule mission sans lien GitHub vers Epic ou sub-issue, sur sprint multi-stages.

**Exception** : missions one-shot < 30 min ou hotfix urgent restent en RooSync direct.

## Pointeurs cross-doc

- Architecture RooSync (34 outils MCP roo-state-manager) : [docs/architecture_mcp_roo.md](architecture_mcp_roo.md)
- Regles de coordination Git + dashboard : [CLAUDE.md](../CLAUDE.md) section A
- Calendrier enseignement + scope ecoles : [docs/teaching-context.md](teaching-context.md)
- Wrapper training BG avec checkpoints : `scripts/training/train_with_checkpoints.py`
- QC backtest + MCP Docker : [docs/quantconnect.md](quantconnect.md)
- Lean prover BG forensic protocol : [docs/lean-prover-state.md](lean-prover-state.md)
