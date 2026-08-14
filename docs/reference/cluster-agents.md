# Cluster CoursIA - agents, GPUs, specialisations

Reference perenne sur la structure du cluster : machines, GPUs, workspaces RooSync, specialisations infrastructure. Pour les **règles de coordination** : cf [docs/architecture_mcp_roo.md](architecture_mcp_roo.md) (RooSync) + [CLAUDE.md](../../CLAUDE.md) section A. Pour le **calendrier enseignement / scope par ecole** : cf [docs/teaching-context.md](teaching-context.md).

## Machines du cluster

| Machine | Role principal | LAN plage / IP | GPUs | VRAM totale |
|---------|----------------|----------------|------|-------------|
| `myia-ai-01` | **Coordinateur** + tests universels + vLLM hosting + training BG GPU 2 + prover BG forensic | `192.168.0.x` (LAN prive, profile Private, interface `vEthernet (MyIA-AI-Gigabit)`). vLLM sur `192.168.0.47:5002` (`0.0.0.0:5002` via Docker Desktop, `remote=Any` sur profil Private + Public, controle d'acces = `VLLM_API_KEY`). WSL/Hyper-V internes : `172.28.0.1`, `172.28.16.1` (mesure ai-01, [#9976](https://github.com/jsboige/CoursIA/issues/9976) §3.1) | 3x RTX 4090 | 72 GB (3x 24) |
| `myia-po-2023` | Hote services GenAI Image/Audio/Video (8 Docker services) | LAN a mesurer sur place (plage non inventoriee sur ce doc — confirmer sur la machine elle-meme via `Get-NetIPAddress -AddressFamily IPv4`). GenAI containers sur `localhost:<port>` (ex musicgen 8192) ; voir [docs/genai/genai-services.md](../genai/genai-services.md) pour le registre | RTX 3080 + eGPU RTX 3090 | 40 GB (16 + 24) |
| `myia-po-2024` | QC backtest + ML training (modèles <= 10M params) | LAN a mesurer sur place (plage non inventoriee). QC MCP Docker `quantconnect/mcp-server` → QC Cloud | RTX 3070 | 8 GB |
| `myia-po-2025` | Tracks intensives ML/audits + workspace EPITA (3 agents) | **LAN `172.24.44.x` (Ethernet 2, DHCP), hote `172.24.44.185` — mesure firsthand [#9976](https://github.com/jsboige/CoursIA/issues/9976) §3 (2026-08-10)**. LAN **physiquement disjoint** du `192.168.0.x` d'ai-01 (deux plages privées RFC 1918 distinctes). WSL/Hyper-V internes : `172.28.176.1` (WSL), `172.17.16.1` (Default Switch). Le `172.24.44.172` cité dans #9976 est la vue WSL ; l'hote lui-meme est `172.24.44.185`. **vLLM `192.168.0.47:5002` NON joignable** (`HTTP 000` + 100% ping loss depuis l'hote Windows) — ce n'est PAS un artefact WSL, c'est une route absente entre deux LAN distincts. Voir §"Regle de routage" | RTX 3080 Ti laptop | 16 GB |
| `myia-po-2026` | Lean prover + QC MCP + service embedding + reverse proxy `xx.myia.io` | LAN a mesurer sur place. Service embedding : port non inventorié dans ce doc. Reverse proxy `xx.myia.io` : sous-domaines publics, joignable depuis n'importe quel hote internet | RTX 3080 | 16 GB |

**Note po-2024/po-2025 swap previsionnel** : user prevoit de mettre la 3080 16GB en utilisation perenne (po-2025 mobile recoit la 3070 8GB, po-2024 fixe garde la 3080 16GB).

**Note LAN (cf [#9976](https://github.com/jsboige/CoursIA/issues/9976))** : la topologie complete des plages LAN par machine n'est **pas mesuree sur place** pour po-2023 / po-2024 / po-2026 dans cette revision. La cellule "LAN a mesurer sur place" reflete cet etat — ne PAS substituer une adresse devinette. Toute nouvelle mesure doit etre sourcee firsthand via `Get-NetIPAddress` sur la machine concernee, et ajoutee a ce tableau a ce moment-la.

## Topologie LAN et reachabilite endpoint

Section de reference pour le routage inter-machines des endpoints partages. La precedente absence de cette table est ce qui a rendu l'incident [#9976](https://github.com/jsboige/CoursIA/issues/9976) possible : "endpoint vivant" etait vrai *depuis ai-01*, lu comme un etat du cluster, et `master.env` etait confondu avec "cle de cluster" alors qu'il est per-machine.

### Endpoints partages (port → hote → joignable depuis)

| Endpoint | Port | Hote qui heberge | LAN address | Joignable depuis |
|----------|------|------------------|-------------|------------------|
| vLLM `medium` (Qwen3.5-35B-A3B-GPTQ-Int4, TP=2 GPU 0+1) | `5002` | `myia-ai-01` | `192.168.0.47:5002` (`0.0.0.0:5002` via Docker Desktop, `remote=Any` Private + Public, cle = `VLLM_API_KEY`) | **ai-01** (mesure : `401` en 0.0026 s depuis `127.0.0.1` et `192.168.0.47`). **po-2023 / po-2024 / po-2026** : a mesurer sur place (LAN `192.168.0.x` partage probable). **po-2025** : **CONFIRME NON joignable** firsthand ([#9976](https://github.com/jsboige/CoursIA/issues/9976) §3, 2026-08-10) — `HTTP 000` (timeout 5 s) + `100%` ping loss depuis l'hote Windows `172.24.44.185`. LAN physiquement disjoint, pas un artefact WSL. Option (a) adoptee : po-2025 utilise un fournisseur externe (OpenRouter, [#6949](https://github.com/jsboige/CoursIA/issues/6949)). Voir §Regle de routage |
| vLLM `mini` (OmniCoder-9B-AWQ-4bit) | `5001` | `myia-ai-01` | `192.168.0.47:5001` (deprecated, meme interface que `5002`) | idem `5002` ; port a verifier avant tout test (deprecated, peut etre ferme) |
| GenAI `musicgen` (service local) | `8192` | `myia-po-2023` | `localhost:8192` (conteneur Docker, wake-on-demand via [genai-service.py](../../MyIA.AI.Notebooks/GenAI/shared/helpers/genai_service.py)) | **po-2023** uniquement (validation reverse-proxy publique via `xx.myia.io` par po-2026, cf [docs/genai/genai-services.md](../genai/genai-services.md)) |
| GenAI autres services Image/Audio/Video (8 conteneurs) | `8188`-`8196` (cf [genai-services.md](../genai/genai-services.md)) | `myia-po-2023` | `localhost:<port>` + reverse-proxy `xx.myia.io` | **po-2023** localhost ; tout agent via `xx.myia.io` (auth bearer) |
| QC MCP (`quantconnect/mcp-server`) | n/a (HTTPS sortant vers `quantconnect.com`) | `myia-po-2024` + `myia-po-2026` | n/a (API Cloud) | **po-2024** et **po-2026** (tokens MCP configures sur les 2 machines). Contrainte : MAX 10 appels API QC / minute entre **tous** les agents (cf §"QuantConnect MCP" plus bas) |
| Lean 4 / Lake build | local (`elan toolchain`) | `myia-po-2026` (specialisation principale) | local uniquement (build sur place) | **po-2026** specialise ; **ai-01** = secours (env Lean a installer si manquant) |
| Service embedding | non inventorié dans ce doc | `myia-po-2026` | a mesurer sur place | a mesurer ; endpoint supposé joignable cross-LAN si meme plage que po-2026 |
| Reverse proxy `xx.myia.io` (sous-domaines GenAI publics) | `443` (HTTPS) | `myia-po-2026` (hebergement) | sous-domaines DNS publics | **tout agent** du cluster (auth bearer par sous-domaine) + internet |
| RooSync GDrive (dashboard + messages) | n/a (HTTPS sortant) | `myia-*` (toutes les machines) | n/a | cross-machine par design |

### Repere de diagnostic endpoint — ne JAMAIS agreger

| Symptome depuis l'hote X | Signification | Action |
|--------------------------|---------------|--------|
| `HTTP 401` en < 50 ms | **Vivant** + cle requise (ou token manquant/expiré). Le service repond, il refuse l'authentification. | Verifier la cle (`master.env` de la machine X, pas une autre), PAS l'adresse |
| `HTTP 200` (avec cle valide) | **Vivant** + authentifie. Service operationnel. | OK |
| `connection refused` | **Mort** localement : port ferme, service eteint, ou pas de listener. Le paquet arrive au TCP layer, aucun daemon ne repond. | Demarrer le service / verifier que le port est bien bound |
| `HTTP 000` / `timeout` / `100% packet loss` (ping) | **Non joignable depuis cet hote** : route absente, pare-feu inter-LAN, ou LAN disjoint. Le paquet ne sort pas / n'arrive pas. | **NE PAS classer comme "service mort"**. Tester depuis l'hote qui heberge l'endpoint (pas l'hote X). Si LAN disjoint, c'est une propriete de routage, pas un incident service |

**Regle de routage** (decision [#9976](https://github.com/jsboige/CoursIA/issues/9976) option (a), adoptee 2026-08-08) : **aucun grain necessitant l'inference locale (`192.168.0.47:5002`) n'est dispatche vers une lane hors-LAN**. Ces lanes (`po-2025` notoirement, et toute autre confirmee non-joignable) recoivent soit des grains sans inference, soit des grains a fournisseur externe (OpenRouter, greenlight sur [#6949](https://github.com/jsboige/CoursIA/issues/6949)). Une lane qui recoit un grain d'inference locale et mesure `HTTP 000` doit le signaler comme **erreur de dispatch du coordinateur**, pas le contourner.

**Securite de l'exposition `0.0.0.0:5002`** (mesure ai-01, [#9976](https://github.com/jsboige/CoursIA/issues/9976) §"La portee de securite") : la regle Docker Desktop est `remote=Any` sur les profils **Private ET Public**. Si `myia-ai-01` se retrouve un jour sur un reseau classe `Public` (partage de connexion, reseau invite, hot-spot), le port **5002 y serait joignable aussi**, protege par la seule `VLLM_API_KEY`. Pas un incident aujourd'hui (interface active `Private`, LAN de confiance), mais propriete a connaitre : **la marge d'exposition est deja consommee par defaut**, ce qui est un argument de plus contre toute re-exposition (l'option (b) est **vide cote ai-01** — rien a exposer qui ne le soit deja, mesure du [#9976](https://github.com/jsboige/CoursIA/issues/9976) §3.1).

### Comment mesurer la reachabilite (template reutilisable)

Depuis l'hote **X** (pas depuis l'hote qui heberge l'endpoint) :

```bash
# 1. Identifier la plage LAN de X (hote Windows)
Get-NetIPAddress -AddressFamily IPv4 | Where-Object {$_.IPAddress -notlike '127.*'} | Select-Object IPAddress,InterfaceAlias

# 2. Tester l'endpoint avec timeout court (eviter les hangs)
curl.exe -s -o NUL -w "%{http_code}`n" --max-time 6 http://<LAN-IP>:<port>/v1/models
```

**Lecture du résultat** :
- `200` : service vivant + cle valide (ou pas de cle requise).
- `401` en < 50 ms : service vivant + cle requise. Verifier `master.env` sur la machine X.
- `000` ou `timeout` : non joignable depuis X (route / pare-feu / LAN disjoint). **Re-tester depuis l'hote qui heberge l'endpoint** pour confirmer que le service est vivant — si `401` depuis l'hote hebergeur, le service marche et le probleme est strictement sur X.

Documenter toute nouvelle mesure dans une sous-section "Mesures recentes" plus bas, avec horodatage, machine source, et resultat verbatim.

### Mesures recentes (audit)

| Date | Source | Cible | Mesure | Conclusion |
|------|--------|-------|--------|------------|
| 2026-08-08 | `myia-ai-01` | `192.168.0.47:5002` (vLLM self) | `HTTP 401` en 0.0026 s sur `127.0.0.1:5002` ; `HTTP 401` en 0.0027 s sur `192.168.0.47:5002` (issue [#9976](https://github.com/jsboige/CoursIA/issues/9976), mesure jsboige) | Endpoint vivant sur les 2 interfaces, `0.0.0.0:5002`, `remote=Any` Private + Public, cle requise |
| 2026-08-08 | `myia-po-2025` | `192.168.0.47:5002` (vLLM) | `HTTP 000`, ping 100 % perte (issue [#9976](https://github.com/jsboige/CoursIA/issues/9976), constat firsthand po-2025) | **LAN disjoint** entre `192.168.0.x` et `172.24.44.172` (a confirmer si WSL interne ou LAN physique distinct — mesure depuis hote Windows requise, cf issue body §"Ce qui reste, et qui n'est pas un blocage") |
| (a completer) | `myia-po-2023` | `192.168.0.47:5002` (vLLM) | a mesurer | |
| (a completer) | `myia-po-2024` | `192.168.0.47:5002` (vLLM) | a mesurer | |
| (a completer) | `myia-po-2026` | `192.168.0.47:5002` (vLLM) | a mesurer | |

## Workspaces RooSync (cluster CoursIA)

Cluster simplifie depuis 2026-05-15 : **un workspace `CoursIA` par machine**, sauf po-2025 qui a 3 agents distincts pour 3 workspaces dedies (CoursIA + 2 EPITA).

| RooSync ID | Role | Capacité dispatch depuis ai-01 |
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

## Second workspace par machine — lanes `CoursIA-2` (depuis ~2026-06)

Depuis ~juin 2026, chaque machine worker porte **deux lanes** (un `lane` = machine x workspace) : sa lane `CoursIA` historique **et** une lane `CoursIA-2` sur un second workspace, coordonnee via un **second dashboard** `workspace-CoursIA-2` co-egal. **Aucun des deux dashboards n'est « celui du coordinateur »** : ai-01 **lit ET poste un contenu lane-specific sur CHACUN** chaque cycle, jamais de broadcast miroir (cf [CLAUDE.md](../../CLAUDE.md) section A + [.claude/rules/coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) règle 3).

| Machine | Lane `CoursIA` (dashboard `workspace-CoursIA`) | Lane `CoursIA-2` (dashboard `workspace-CoursIA-2`) |
|---------|-----------------------------------------------|---------------------------------------------------|
| `myia-po-2024` | QC backtest + ML (RTX 3070) | MetaGeneticSharp / metaheuristiques .NET (#1203) |
| `myia-po-2025` | Python / ML (off-LAN — OpenRouter pour LLM, vLLM local non-joignable, cf [#9976](https://github.com/jsboige/CoursIA/issues/9976)) | .NET / Argumentum (#2137) |
| `myia-po-2026` | Lean Conway/Knot + embeddings GenAI | Grothendieck (#2159) |

`po-2023` (hote GenAI) et `ai-01` (coord) n'ont qu'une lane `CoursIA`. po-2025 ajoute par ailleurs ses 2 workspaces EPITA (cf section "po-2025 - 3 agents distincts").

**Anti-collision (HARD)** : un seul editeur par serie/notebook ; une **session `CoursIA` != session `CoursIA-2`** sur la meme machine (collision-avoidance cross-session — un worker qui refuse un pivot cross-session a raison, le tort est au coordinateur). **Une lane ne se ferme jamais** : si la deep-queue Epic d'une lane est epuisee, le worker tombe sur le **fallback perenne never-empty** de SA famille (#2651 prose READMEs, #3973 README ascendant, #2161 rollout 3-exos, #3966 mise-en-forme notebooks), jamais "idle". Detail : [.claude/rules/coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) règle 4.

## ai-01 - topologie GPU (RTX 4090 x3)

Règle stricte : GPU 2 **doit etre occupee 24/7** par un training BG longue duree.

| GPU | Role | Etat normal |
|-----|------|-------------|
| GPU 0 RTX 4090 | vLLM `medium` (Qwen3.6-35B-A3B-GPTQ-Int4, TP=2 avec GPU 1) | ~23-24 GB VRAM occupee 24/7 |
| GPU 1 RTX 4090 | vLLM `medium` (TP=2 avec GPU 0) | ~23-24 GB VRAM occupee 24/7 |
| GPU 2 RTX 4090 | **vLLM `mini` + Training BG ai-01 dedie** | DOIT toujours etre occupee par training BG |

**Alias vLLM** :
- `mini` : OmniCoder-9B-AWQ-4bit, GPU 2, port 5001, deprecated
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

**Règle ai-01** : trainings GPU non-supervises > 15 min sur po-2025 INTERDITS, sauf si :
- Pattern reuse `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (classe `TrainingCheckpoint` + `thermal_check` import direct ; outer supervisor subprocess documenté dans `scripts/training/train_with_checkpoints.py` n'existe pas — librairie canonique = `gpu_training.py`, defauts `max_temp=80`, `cool_sleep=15`)
- Watchdog `nvidia-smi` polling avec auto-stop a 87C
- Batch size réduit + mixed precision FP16

Si user dit "OK GPU heavy po-2025" : vérifier qu'il connait l'incident avant d'agir (override possible).

## po-2025 - 3 agents distincts

| Workspace | Role | Etat |
|-----------|------|------|
| `myia-po-2025:CoursIA` | Tracks intensives ML/audits avec backoff thermal | ACTIF |
| `myia-po-2025:2026-Epita-Programmation-par-Contraintes` | Review/merge PRs etudiants PrCon | EN ATTENTE PRs etudiants |
| `myia-po-2025:2026-Epita-Intelligence-Symbolique` | Veille sujets + enrichissement | ACTIF veille |

**Skills cross-workspace tappables** : po-2025 developpe des skills spécifiques par workspace, mais ai-01 peut tapper l'agent qui a deja la skill fraiche. Exemple : formulaire eval partenaire cree par `po-2025:2026-Epita-PrCon` plutôt que `po-2025:CoursIA`, parce que PrCon avait fait des formulaires GWorkspace+Playwright le meme jour.

## Specialisations infrastructure

### GenAI Image/Audio/Video -> po-2023

Hardware : RTX 3080 Ti 16GB + eGPU 3090 24GB. **8 services Docker GenAI** :
- Image : Qwen Image Edit, Z-Image/Lumina, SD Forge Turbo/Main, SD.Next
- Audio : Whisper STT, Kokoro TTS, MusicGen, Demucs
- Video : ComfyUI Video

**Règle user** : s'il y a du GenAI Image/Audio/Video, ca va a po-2023. Lui seul peut tester notebooks contre ses propres services locaux.

### GenAI Texte (vLLM) -> ai-01

Les 2 containers Texte tournent sur le **vLLM workspace de ai-01**, pas po-2023. Cf section GPU topology ci-dessus pour `mini`/`medium`.

### GenAI Embedding -> po-2026

Container embedding dedie sur po-2026. Tout agent peut consommer l'endpoint.

### Reverse proxy `xx.myia.io` -> po-2023

Sous-domaines publics qui pointent vers les services GenAI de po-2023. Permet validation **bout-en-bout** des notebooks GenAI (auth bearer + timeouts + latences réelles client-side) en plus du test localhost de po-2023.

**Sequence GenAI a 2 étapes** : po-2023 dev + test local, puis po-2026 (optionnel) re-validation via sous-domaine public. po-2026 intervient APRES po-2023, jamais a la place.

### QuantConnect MCP -> po-2024 + po-2026

Tokens API QC configures dans `.mcp.json` sur les 2 machines (Docker MCP server `quantconnect/mcp-server`). Ils peuvent `create_compile` + `create_backtest` sur QC Cloud.

**Polyvalence** : avoir le token QC ne signifie PAS perimetre exclusif. Ces agents peuvent etre dispatch sur n'importe quelle mission (audit, Lean, notebooks). Le token QC = capacité **supplémentaire**.

**Contrainte rate limit** : MAX 10 appels API QC / minute entre **tous les agents**. Avant backtest, annonce obligatoire sur dashboard workspace CoursIA pour eviter contention.

### Lean / Mathlib -> po-2026

Specialisation `*.lean`, port social_choice, Lake build, reecriture preuves structurelles. ai-01 = secours (env Lean a installer si manquant). Cf [docs/lean/prover_iteration_history.md](../lean/prover_iteration_history.md).

### Whisper API host -> po-2023

Rotation cle API geree par po-2023 lui-meme. **NON consommé** dans workspace CoursIA (verifie 2026-05-16, 0 .env actif avec WHISPER_API_KEY cote CoursIA).

## Table rapide dispatch

| Mission | Agent principal | Alternative / validation |
|---------|-----------------|--------------------------|
| GenAI Image/Audio/Video (containers + notebooks) | `po-2023:CoursIA` | po-2026 pour validation reverse proxy `xx.myia.io` |
| GenAI Texte / vLLM (containers) | `ai-01:CoursIA` | tout agent pour consommer l'endpoint |
| GenAI Embedding (container) | `po-2026:CoursIA` | tout agent pour consommer l'endpoint |
| QC backtest / strategie | `po-2024:CoursIA` | `po-2026:CoursIA` (tokens MCP) |
| QC partner org cleanup | `po-2024:CoursIA` | `po-2026:CoursIA` |
| Lean / Mathlib (port + preuves) | `po-2026:CoursIA` | ai-01 secours (env a installer) |
| Lean prover BG forensic | **`ai-01:CoursIA` systematique** | apres chaque PR / message po-2026 mentionnant sorry |
| Audit notebooks pedagogique | tout agent polyvalent | cross-check pour eviter double couverture |
| Execution Papermill notebooks | tout agent polyvalent | ai-01 = machine de test universelle prioritaire |
| Review PR + merge | `ai-01:CoursIA` (seul merger) | - |
| Test global bout-en-bout (tous kernels) | `ai-01:CoursIA` (priorite) | - |
| Training CNN moyen (~7M, batch 128) | po-2024 / po-2025 / po-2026 (3080 16GB) | mixed precision FP16, attention batch |
| Training CNN gros (>10M, batch >256) | ai-01 GPU 2 | po-2023 eGPU 3090 si dispo |
| Coordination cross-workspace EPITA | `ai-01:CoursIA` via `roosync_messages send` | exception "grand manitou" |

**Règle implicite** : tous les agents sont polyvalents sur la **pédagogie**. Les **specialisations sont infra/tokens/hardware**. ai-01 doit pouvoir tester partout (priorite pour installer envs manquants).

## Dispatch via Epic GitHub (sprints multi-stages)

Pour tout sprint / curriculum >= 3 étapes, creer **Epic GitHub** + sub-issues numerotees AVANT de dispatcher. Les agents lisent l'issue, voient leur prochain step, livrent la PR liee, prennent le step suivant **sans re-demander la coord**.

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

## Délégation — mapping `model` → moteur, par machine

Le mapping du `model` explicite (`sonnet` / `haiku`) vers le moteur sous-jacent dépend de la machine d'exécution. Raisonner en **tiers** (intermédiaire / léger), pas en nom de modèle : le principe de [`model-delegation.md`](../../.claude/rules/model-delegation.md) — déléguer le read-heavy borné, garder la décision, modèle explicite obligatoire — est invariant.

| Machine | `sonnet` (tier intermédiaire) | `haiku` (tier léger) |
|---|---|---|
| ai-01 | GLM-5.1 | Qwen 3.6 local |
| po-2023 | ZAI GLM-5.1 | MiniMax M3 |
| autres workers po-* | voir `roosync_inventory` | voir `roosync_inventory` |

MiniMax M3 (déployé sur `po-2023` depuis 2026-07-02, mandat user) remplace Qwen 3.6 sur le tier `haiku` pour cette lane : les sous-agents `model: "haiku"` invoqués depuis po-2023 sont exécutés par MiniMax M3. Seul le moteur change, pas la règle de qualité.

## Capacité vision — router le QA visuel vers MiniMax (lanes CoursIA-2) ou ai-01, jamais GLM

Mandat user 2026-07-11. **MiniMax M3** (main-loop de toutes les lanes CoursIA-2 depuis le mandat du 02/07) et **ai-01** (Opus) ont des capacités de **vision** que **ZAI GLM-5.1** (lanes CoursIA) n'a pas. Objectif : que nos README et notebooks **rendent bien visuellement**.

**Routage capability-driven, PAS token-driven.** Distinct de [[feedback-token-economy-anthropic-only]] : on route vers MiniMax **pour sa vision** — une capacité que GLM n'a pas — pas pour économiser. C'est le cas légitime « meilleur outil pour la tâche », pas un fallback dégradé.

- **Règle.** Toute tâche dont la valeur dépend du **rendu visuel** (galeries de figures README, plots générés par notebook, sorties d'images GenAI, layout de slides, diagrammes) voit son **QA visuel** routé vers une lane **CoursIA-2 (MiniMax)** ou vers **ai-01**. **Jamais** vérifié text-only sur une lane GLM : elle ne voit pas.
- **Mécanisme concret.** Un `Read` sur un fichier image (`.png`/`.webp`/`.jpg`), ou sur un screenshot (Playwright render → screenshot → `Read`, ou `mcp__sk-agent__analyze_image`), insère des blocs image que MiniMax/Opus interprètent. Un `test -f` confirme l'**existence**, PAS le **rendu** — seul le regard distingue une vraie figure d'un placeholder plat, blanc ou cassé.
- **Couplage ai-01 ↔ MiniMax (la « double vision » du mandat).** MiniMax fait le **balayage en volume** (audit read-only de N figures → liste de défauts : cassées / blanches / placeholder / alt-text incohérent / overflow slide) ; ai-01 **valide la liste et tranche au merge-gate** (regarde effectivement les figures d'une PR avant merge). Déléguer le sweep borné, garder le jugement — le sweep visuel est read-only, donc **sans collision** avec la lane qui possède la substance : le fix repart au owner.
- **Classe de défaut à attraper** (cf [`sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) Prong A) : une figure réduite à des blocs de couleur plats / image blanche / placeholder / render cassé **alors que le vrai outil était invocable** (stack GenAI, matplotlib, solveur) → verdict RECOVERABLE-MACHINE ou -LOCAL, **régénérer**, jamais consacrer.

**Incident fondateur** : `GenAI/Image/assets/readme/workflow-orchestration.png` — 3 blocs plats olive/violet/vert labellisés « sd35 photorealistic / watercolor / anime », c'est-à-dire une sortie dégénérée et non des images générées. Le fichier a passé le gate « existe sur disque » sans encombre ; il a été attrapé au **premier regard** (ai-01, 2026-07-11).

## Pointeurs cross-doc

- Cycle de vie / diagnostic des serveurs MCP : [architecture_mcp_roo.md](architecture_mcp_roo.md) — inventaire des 15 outils roo-state-manager : [HARNESS-OVERVIEW.md §2](https://github.com/jsboige/roo-extensions/blob/main/docs/harness/HARNESS-OVERVIEW.md)
- Règles de coordination Git + dashboard : [CLAUDE.md](../../CLAUDE.md) section A
- Calendrier enseignement + scope ecoles : [docs/teaching-context.md](teaching-context.md)
- Training BG avec checkpoints : `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (classe `TrainingCheckpoint` ; 18 tests PR #7454, fixes GPU-thermal #7335/#7454/#7456 ; le wrapper outer-supervisor subprocess `scripts/training/train_with_checkpoints.py` documenté n'a jamais été créé — utiliser `gpu_training.py` directement)
- QC backtest + MCP Docker : [docs/qc/quantconnect.md](../qc/quantconnect.md)
- Lean prover BG forensic protocol : [docs/lean/prover_iteration_history.md](../lean/prover_iteration_history.md)
