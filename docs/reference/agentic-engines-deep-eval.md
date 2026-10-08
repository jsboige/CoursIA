# Évaluation approfondie des moteurs agentiques — ADK vs Semantic Kernel vs MS Agent Framework

> Livrable de l'issue [#14499](https://github.com/jsboige/CoursIA/issues/14499) (mandat user 2026-09-23 : « Il faut analyser les 3 en profondeur »).
> Protocole commun : 6 points (état de l'art, modes d'orchestration **exécutés**, déterminisme, couverture C#/Python, coût pour le dépôt, verdict par critère).
> Ce document porte les mesures et les tableaux — pas de rapport de cycle. Chaque affirmation est `VERIFIÉ` (mesure firsthand, commit/chemin cité) ou `RAPPORTE` (source primaire citée).

## État du document

| Tranche | Point du protocole | État |
|---|---|---|
| T1 (cette PR) | pt 2 — SK, mode événementiel (Process Framework) exécuté | livré |
| T2 (cette PR) | pt 2 — SK, couche agents : handoff exécuté (service LLM réel, temp 0) | livré |
| T3 (cette PR) | pt 2 — ADK : handoff natif C5 + désignation C4 exécutés via l'organe Track2 (service LLM réel, temp 0) | livré |
| T4 | pt 2 — SK, modes restants (séquentiel, concurrent, group chat, Magentic) exécutés (service LLM réel, temp 0) | livré |
| T5 | pt 3 — MAF, graphe typé (`WorkflowBuilder`) exécuté (service LLM réel, temp 0), borne de boucle falsifiée | livré |
| T6 | pt 4 — couverture C# mesurée par les assemblages (SK 1.81.0, MAF 1.24.0, ADK absent), contrôles positif et négatif | livré |
| — | pt 2 — MS Agent Framework (agents, graphe) | à venir |
| — | pt 1 état de l'art | livré hors repo : note datée du 2026-10-05 sur [#19380](https://github.com/jsboige/CoursIA/issues/19380) ; mémo inventaire local du 2026-10-07 (po-2024:CoursIA-2) sur [#14499](https://github.com/jsboige/CoursIA/issues/14499) |
| — | pts 3-6 (déterminisme, couverture langages, coût, verdict) | à venir |

## 2. Modes d'orchestration — exemples exécutés

### 2.1 Semantic Kernel — couverture réelle du dépôt (mesuré)

`VERIFIÉ` (lecture intégrale du carnet [`06-SemanticKernel-ProcessFramework.ipynb`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb), kernel python3, twin exécuté de bout en bout) :

- la série démontre des pipelines **séquentiels manuels** (`run_content_pipeline`, `run_iterative_pipeline` : boucle de révision explicite en Python) ;
- l'API **événementielle** du Process Framework (`ProcessBuilder` + `on_event`/`send_event_to`) n'apparaît **que en prose** (sections descriptives et schéma d'architecture) — **aucune cellule ne l'exécute** ;
- le point user « orchestration événementielle sous-exploitée » ([#14499](https://github.com/jsboige/CoursIA/issues/14499), contre-point 2) est donc **confirmé par la mesure** : le mode est documenté mais jamais exécuté dans le corpus.

Conséquence pour l'évaluation : le pilote événementiel ci-dessous est le **premier** exemple exécuté de ce mode dans le dépôt — il ne reduplique rien.

### 2.2 Pilote SK Process Framework (événementiel, déterministe)

`VERIFIÉ` — pilote [`eval-pilots/sk_process_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/sk_process_pilot.py), exécuté sous `py -3.11` / semantic_kernel **1.41.3** (le kernel de la série), **sans LLM** : chaque étape est une transformation déterministe (intake → enrich → review → publish|reject, règle de seuil ≥ 3 mots). Reproduction firsthand depuis l'emplacement livré : exit 0.

Trace d'exécution (deux entrées, deux embranchements événementiels) :

```text
[step] intake -> {'text': 'le framework orchestre des etapes evenementielles'}
[step] enrich -> {'text': 'le framework orchestre des etapes evenementielles', 'words': 6, 'label': 'long'}
[step] review -> {'text': ..., 'words': 6, 'label': 'long', 'verdict': 'approved'}
[step] publish -> {'text': ..., 'verdict': 'approved'}
[step] intake -> {'text': 'ok'}
[step] enrich -> {'text': 'ok', 'words': 1, 'label': 'court'}
[step] review -> {'text': 'ok', 'words': 1, 'label': 'court', 'verdict': 'rejected'}
[step] reject -> {'text': 'ok', 'verdict': 'rejected'}
DETERMINISM: OK
PILOT OK sk=1.41.3 steps=8
```

**Déterminisme (pt 3, premier datapoint)** : double exécution dans le même process → trace et états finaux identiques (`DETERMINISM: OK`), sans graine ni température — l'orchestration événementielle elle-même est pure.

Faits d'API mesurés sur 1.41.3 (contrairement aux exemples publics plus anciens, utiles à toute réutilisation dans la série) :

| Fait | Détail |
| --- | --- |
| Point d'entrée d'exécution | `from semantic_kernel.processes.local_runtime.local_kernel_process import start` puis `await start(process, kernel, "Start", data=...)` — le `__init__` de `local_runtime` n'exporte **rien**, les chemins de sous-modules complets sont requis. |
| Ciblage de fonction | `send_event_to(step, function_name="fn")` (forme kwargs) — **pas** de `where_function` dans cette version. |
| État typé d'étape | la souscription générique `KernelProcessStep[State]` **ne fonctionne pas** (métaclass pydantic) ; l'idiome qui marche : annotation `state: MyState = Field(default_factory=MyState)` + `activate()` faisant `self.state = state.state`. |
| Événements externes | `context.send_event()` ne fait que **mettre en file** (no-op silencieux une fois le process drainé) ; `context.start_with_event(...)` draine réellement la boucle. |
| Retour d'étape | une fonction `@kernel_function` qui retourne `None` fait émettre `OnError` par le runtime — toujours retourner une valeur. |

### 2.3 Pilote SK couche agents — HandoffOrchestration (service LLM réel)

`VERIFIÉ` — pilote [`eval-pilots/sk_agents_handoff_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/sk_agents_handoff_pilot.py), exécuté sous `py -3.11` / semantic_kernel **1.41.3**, service **réel** (`gpt-4o-mini`, température 0, `max_completion_tokens` 200, budget **dur de 10 appels** comptés par un connecteur instrumenté). Scénario : `triage` → handoff vers `specialiste_technique` | `specialiste_formation`, 2 entrées non ambiguës × 2 exécutions. Reproduction firsthand depuis l'emplacement livré : exit 0.

```text
[technique #1/#2] decision: specialiste_technique (stable)
[formation  #1/#2] decision: specialiste_formation (stable)
ROUTING DETERMINISM: OK
LLM CALLS: 9/10
PILOT OK sk=1.41.3 orchestration=Handoff
```

**Déterminisme (pt 3, deuxième datapoint — la distinction qui compte)** : à température 0, la **décision de routage** est stable entre exécutions d'un même process ET entre processus, mais la **prose** des spécialistes n'est **pas** byte-identique entre processus (mesuré : deux runs de la même entrée « formation » produisent deux formulations différentes, routage identique). Conclusion d'évaluation : le déterminisme à temp 0 s'asserte sur les **décisions structurantes** (routage, embranchements), jamais sur le texte — les pilotes ADK/MAF seront mesurés sur la même base pour rester comparables.

Faits d'API mesurés sur 1.41.3 (couche agents) :

| Fait | Détail |
| --- | --- |
| Détournement `OPENAI_BASE_URL` | le SDK OpenAI honore silencieusement les variables d'environnement du poste (proxy local ici) → clé `sk-proj` envoyée au proxy → 401. Parade : `OpenAIChatCompletion(async_client=AsyncOpenAI(api_key=..., base_url=...))` explicite — toujours épingler le `base_url` dans un pilote reproductible. |
| `InProcessRuntime.start()` | **synchrone** en 1.41.3 (l'`await` lève `TypeError`) ; `stop_when_idle()` est asynchrone. Import depuis `semantic_kernel.agents.runtime` (top level). |
| `orchestration/__init__` vide | importer `HandoffOrchestration`/`OrchestrationHandoffs` depuis `semantic_kernel.agents` (top level), pas du sous-module. |
| `gpt-5-mini` refuse `temperature=0.0` | 400 `unsupported_value` (« Only the default (1) value is supported ») — contrainte famille *reasoning* : un pilote déterministe ne peut pas la prendre. **Conséquence de méthode** : le modèle de comparaison est **épinglé en constante** (`MODEL = "gpt-4o-mini"`), et non choisi par une sonde qui bascule. Un repli automatique ferait dépendre le modèle **effectif** d'un comportement d'API, et la comparaison entre pilotes se casserait sans signal le jour où la sonde passerait. La sonde reste (elle atteste que le service répond sur ce modèle) mais elle **échoue fort** (exit 2) au lieu de basculer. `max_completion_tokens` (pas `max_tokens`) fonctionne sur les deux. |
| Mécanique handoff | l'orchestration injecte `transfer_to_<agent>` + `complete_task` dans un **clone** du kernel de chaque agent ; filtre d'auto-invocation termine le tour juste après l'appel → exactement 1 appel LLM par tour d'agent (rend le budget tenable). `ChatCompletionAgent` active `function_choice_behavior=Auto()` par défaut. |
| Sonde de routage | `(await result.get()).name` = l'agent qui a terminé — le signal déterministe le plus propre ; `agent_response_callback` (un simple `list.append` sync) capture la prose. Un spécialiste qui répond sans `complete_task` est auto-complété sans blocage. |
| Réutilisation | `HandoffOrchestration` + `InProcessRuntime` **frais** par invocation ; les instances d'agents sont réutilisables (le clonage isole les plugins injectés). |

### 2.4 Pilote Google ADK — handoff natif C5 + désignation C4 (organe Track2 invoqué)

`VERIFIÉ` — pilote [`Track2-GoogleADK/eval-pilots/adk_handoff_pilot.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/eval-pilots/adk_handoff_pilot.py), exécuté sous `py -3.11` / google-adk **2.8.0** via l'**organe du track** ([`utils/adk_runtime.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/utils/adk_runtime.py) : `build_agent` + `run_agent_turn` ; [`utils/adk_orchestrator.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/utils/adk_orchestrator.py) : `AdkOrchestrator`) — aucune réimplémentation. Service **réel** `gpt-4o-mini`, température 0 (même modèle, même réglage, même scénario de triage que le pilote T2 — les deux moteurs deviennent directement comparables **par construction** : le modèle est épinglé en constante dans les deux pilotes, aucune sonde ne peut le substituer), budget ex-post 12 appels mesuré par les snapshots d'usage du contrat C6. Reproduction firsthand depuis l'emplacement livré : exit 0.

Deux observables, alignés sur les deux mécaniques distinctes du contrat du track :

1. **Handoff natif C5** (`sub_agents` → `transfer_to_agent` injecté par ADK) : le triage transfère vers le spécialiste, même couple d'entrées non ambiguës que T2 ;
2. **Désignation C4** (`AdkOrchestrator`, plan déclaré AVANT le premier appel LLM) : une chaîne de 2 spécialistes doit s'exécuter dans l'ordre du plan (observable : `agent_hands`).

```text
[technique #1/#2] final_agent: specialiste_technique | events: 3
[formation  #1/#2] final_agent: specialiste_formation | events: 3
[chaine C4] mains: analyseur -> synthetiseur | events: 2
ROUTING DETERMINISM: OK
PLAN ORDER (C4): OK
LLM CALLS: 10/12 (ex-post, snapshots d'usage C6)
PILOT OK adk=2.8.0 orchestration=transfer_to_agent+AdkOrchestrator
```

**Déterminisme (pt 3, troisième datapoint)** : la décision de routage C5 est stable sur 2 exécutions par entrée (même base d'assertion que T2 — décisions structurantes, jamais la prose) ; l'ordre C4 est déterministe **par construction** : le plan est une donnée posée avant tout appel LLM, la mesure le confirme mécaniquement (`agent_hands` suit le plan exactement).

Faits d'API mesurés sur ADK 2.8.0 :

| Fait | Détail |
| --- | --- |
| Température non exposée par l'organe | `build_agent`/`build_adk_model` n'acceptent pas `temperature` ; le champ **public** `Agent.generate_content_config` (un `GenerateContentConfig`) se pose après construction et sa fusion dans les paramètres de génération se fait **après** les kwargs du constructeur `LiteLlm` — il gagne sur tout défaut, sans toucher l'organe. |
| Boucle de transfert vers le parent | sans `disallow_transfer_to_parent = True` et `disallow_transfer_to_peers = True` sur les sous-agents, le modèle transfère **vers le haut** → boucle triage↔spécialiste jusqu'au timeout 120 s (mesuré avec gpt-4o-mini ; déjà mesuré le 2026-10-05 sur cet organe avec un petit modèle local). Ce sont des champs publics d'`Agent`. |
| Budget natif non exposé | `RunConfig.max_llm_calls` existe (budget ex-ante natif) mais `run_agent_turn`/`run_chain` ne prennent pas de `run_config` — le pilote compte ex-post via les snapshots C6 (`len(result.usage_turns)`, un par appel LLM quand le provider remonte son usage). |
| `ProviderConfig` explicite | le pilote construit sa config OpenAI en clair (`provider`, `model`, `api_key` de `master.env`, `base_url` épinglé) : aucune écriture dans le `.env` du track, et les kwargs explicites `api_base`/`api_key` passés par `build_adk_model` priment sur le détournement `OPENAI_BASE_URL` du poste (même parade que T2). `drop_params=True` (posé par l'organe) absorbe les paramètres non supportés par le provider. |
| Agent unique-parent | chaque exécution reconstruit ses agents (le pilote n'a qu'un orchestrateur, mais l'organe impose un parent unique par `Agent` — mesuré 2026-10-05 : `ValidationError: Agent X already has a parent`). |
| Log bénin en chaîne partagée | à l'étape 2 de la chaîne C4, ADK journalise `Event from an unknown agent: analyseur` : l'événement de session partagée vient du Runner de l'étape 1 — informationnel, la chaîne complète et les mains sont correctes. |

### 2.5 Pilote SK — les quatre autres modes d'orchestration (séquentiel, concurrent, group chat, Magentic)

`VÉRIFIÉ` — pilote [`eval-pilots/sk_orchestration_modes_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/sk_orchestration_modes_pilot.py), exécuté sous `py -3.11` / semantic_kernel **1.41.3**, service **réel** (`gpt-4o-mini`, température 0, `max_completion_tokens` 160 pour les agents, budget **dur** compté par un connecteur instrumenté qui jette au-delà). Complète T2 (handoff, §2.3) : les cinq modes d'orchestration de la couche agents sont désormais couverts par un exemple exécuté.

Les trois mêmes rôles (`redacteur`, `critique`, `arbitre`) portent les quatre modes : la **charge est constante**, seule l'orchestration change, ce qui isole la propriété mesurée. Chaque mode tourne **deux fois** (2 × 4 = 8 exécutions).

**Ce qui est asserté, et ce qui ne l'est pas.** À température 0, la **signature structurelle** d'un run — la suite des agents qui ont répondu — est stable ; la **prose** ne l'est pas (§2.3, §2.4). Les pilotes assertent donc la structure. Trois propriétés, une par famille de mode :

- **séquentiel** : ordre **et** nombre fixes (la chaîne est déclarée : `redacteur → critique → arbitre`) ;
- **group chat** : ordre **et** nombre fixes (tour de table borné par `RoundRobinGroupChatManager(max_rounds=N)`) ;
- **concurrent** : **ensemble** fixe, ordre **libre** — les agents tournent en parallèle, exiger une séquence serait un faux négatif (mesuré : l'ordre a varié entre les deux runs, l'ensemble non) ;
- **magentic** : **ensemble** fixe, ordre **libre** — c'est le manager qui choisit qui parle ; l'ordre est sa décision, pas une propriété du mode.

Trace d'exécution (transcription abrégée — les lignes `apercu` de prose sont omises, cf. le déterminisme ci-dessous) :

```text
probe gpt-4o-mini: OK -> OK

MODE sequentiel  run1/run2: tours=3 agents=['redacteur','critique','arbitre']    STABLE: OK | TOURS [3,3]: OK
MODE concurrent  run1: tours=3 ['arbitre','critique','redacteur']
                 run2: tours=3 ['redacteur','critique','arbitre']               STABLE: OK | TOURS [3,3]: OK
MODE group_chat  run1/run2: tours=3 agents=['redacteur','critique','redacteur'] STABLE: OK | TOURS [3,3]: OK
MODE magentic    run1/run2: tours=2 agents=['redacteur','critique']             STABLE: OK | TOURS [2,6]: OK
Max round count reached.

SYNTHESE
  sequentiel   tours=3 (attendu [3,3]) stable=True couverture=True
  concurrent   tours=3 (attendu [3,3]) stable=True couverture=True
  group_chat   tours=3 (attendu [3,3]) stable=True couverture=True
  magentic     tours=2 (attendu [2,6]) stable=True couverture=True
MULTI-AGENTS PAR MODE: OK
ROUTING DETERMINISM: OK
LLM CALLS: 31/110
PILOT OK sk=1.41.3 modes=4
```

Les deux runs de **concurrent** montrent le point exact : même **ensemble** (`{arbitre, critique, redacteur}`), ordre **différent** — l'assertion porte sur l'ensemble trié, une comparaison de séquence aurait produit un faux négatif sur une implémentation correcte.

Quatre propriétés de la couche agents se déduisent de ces huit exécutions, et aucune n'est documentée de façon actionnable en amont :

| Fait | Détail |
| --- | --- |
| `agent_response_callback` se passe **au constructeur** | l'affecter après coup (`orchestration.agent_response_callback = messages.append`) est **silencieusement ignoré** en 1.41.3 : la liste de messages reste vide et le run paraît ne compter aucun tour. Les quatre constructeurs (`SequentialOrchestration`, `ConcurrentOrchestration`, `GroupChatOrchestration`, `MagenticOrchestration`) l'acceptent en kwarg. |
| `description` **obligatoire** dès qu'un manager choisit l'orateur | `GroupChatOrchestration` lève `ValueError: All members must have a description.` — sans manager (séquentiel, concurrent) le champ est inutile, avec manager (group chat, magentic) il est requis. Un agent décrit pour un mode l'est donc pour les quatre. |
| Le manager Magentic a besoin de son **propre budget de tokens** | il demande au service un `response_format=ProgressLedger` (JSON structuré) puis le valide par `ProgressLedger.model_validate_json(response.content)`. Avec les 160 tokens des agents, le JSON est **tronqué** et lève `ValidationError: Invalid JSON: EOF while parsing a value` — l'échec ne vient ni du modèle ni du mode, mais de la taille allouée à la réponse du manager. `StandardMagenticManager(prompt_execution_settings=...)` avec 1500 tokens corrige. Ce chemin appelle `get_chat_message_content(history, settings_clone)` **sans kernel** : l'erreur `The kernel is required for function calls` en est un symptôme trompeur, la cause réelle est la troncature. |
| Magentic **délègue selon la tâche**, pas selon le nombre de membres | sur une tâche triviale (« définir X en une phrase »), le manager délègue **une seule fois** (`redacteur`) puis répond — de façon **stable** sur deux exécutions. Un tour unique n'est donc pas un défaut du mode : c'est le comportement attendu d'un plan court. Pour démontrer la **planification**, la tâche doit exiger plusieurs rôles (le pilote passe une tâche dédiée qui nomme explicitement le passage par le critique). |
| Le manager Magentic **ne se termine pas seul** sur une tâche courte — il faut le borner | `max_round_count` vaut **`None` par défaut** (les deux autres garde-fous, `max_stall_count=3` et `max_reset_count`, sont posés). Mesure : non borné, le manager a produit **8 tours** (`critique` répété 5 fois) et épuisé le budget LLM avant la fin du second run. Borné à **2** comme à **3** rounds, il **bute sur le plafond** — la ligne `Max round count reached.` apparaît dans les deux cas, et la terminaison vient de la borne, jamais d'une satisfaction déclarée par le ledger. Un pilote Magentic doit donc poser `max_round_count` explicitement, et l'assertion de tours se lit comme « borné », pas comme « terminé naturellement ». |

**Ce que le relevé apprend pour l'évaluation comparative** : sur les quatre modes, la sonde structurelle exploitable est la **suite des `name` reçus par `agent_response_callback`**, avec une comparabilité qui dépend du mode — ordre inclus quand le mode le détermine, ensemble seul quand il ne le détermine pas. Appliquer la même assertion aux quatre modes produirait deux faux négatifs (concurrent, magentic) sur une implémentation correcte ; c'est la propriété du mode, pas la tolérance du test, qui fixe la forme de l'assertion. Le pilote ADK (§2.4) s'était déjà heurté au même point par l'autre bout (ordre C4 déterministe *par construction*), ce qui donne à la comparaison SK↔ADK une base commune : **le déterminisme se déclare par mode, jamais globalement**.

### 2.6 Pilote MAF — le graphe typé (WorkflowBuilder)

`VÉRIFIÉ` — pilote [`eval-pilots/maf_workflow_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/maf_workflow_pilot.py), exécuté sous `py -3.11` / `agent-framework-core` **1.9.0**, service **réel** (`gpt-4o-mini`, température 0, budget **dur** compté par un client instrumenté qui jette au-delà).

**MAF n'est pas un framework « objets d'orchestration ».** Aucune classe `SequentialOrchestration` / `HandoffOrchestration` n'existe : l'unité est le **graphe typé** — `WorkflowBuilder(start_executor=…)`, des `Executor` portant un `@handler`, des arêtes posées par `add_edge` et `add_switch_case_edge_group(Case(condition=…, target=…), …, Default(target=…))`. C'est la différence de nature avec SK, et elle décide de tout le reste : **qui parle ensuite n'est pas une décision d'agent**, c'est une arête du graphe.

**L'organe natif existe déjà dans le dépôt**, et c'est lui qui fixe l'idiome du pilote : le harnais du prover Lean construit exactement ce graphe (`SymbolicAI/Lean/agent_tests/prover/workflow.py`, `ProofWorkflowBuilder`, sept exécuteurs — `SearchAgent → TacticAgent → VerifyExecutor → CriticAgent → … → yield_output`). Le pilote reprend la même grammaire (`@handler`, `ctx.send_message`, `ctx.yield_output`, `add_switch_case_edge_group`) plutôt que d'en inventer une.

Les trois mêmes rôles que §2.5 (`redacteur`, `critique`, `arbitre`) et la même tâche : la charge est constante, seule l'orchestration change, ce qui rend les deux couches comparables. Le graphe posé est `redacteur → critique → (boucle de révision | arbitre)`, la branche étant une **lambda Python sur le message**.

Trace d'exécution :

```text
MAF 1.9.0 (agent-framework-core)
MAF run1: tours=5 agents=['redacteur', 'critique', 'redacteur', 'critique', 'arbitre']
MAF run2: tours=5 agents=['redacteur', 'critique', 'redacteur', 'critique', 'arbitre']
FORME STABLE: OK
MULTI-AGENTS: OK
ORDRE FIXE: OK
BOUCLE BORNEE: OK
LLM CALLS: 10/40
PILOT OK maf workflow roles=3
```

**La borne est falsifiée, elle n'est pas supposée.** Un run vert sur le seul chemin nominal ne prouve pas que le plafond de boucle mord. Avec `MAX_REVISIONS = 0`, le même pilote rend **3 tours** (`redacteur, critique, arbitre`) au lieu de 5 — la branche de retour est donc réellement gouvernée par la lambda, et les assertions distinguent les deux formes au lieu d'être tautologiques.

| Fait | Détail |
| --- | --- |
| Le routage est **déterministe par construction** | en SK/Magentic, un LLM choisit l'orateur et émet un `ProgressLedger` ; ici la condition est une lambda sur le message. Corollaire pour l'assertion : l'**ordre ET le nombre de nœuds** sont fixés par le graphe — même doctrine que séquentiel/group chat en §2.5, pas celle de concurrent/Magentic (ensemble fixe, ordre libre). |
| Ce que « stable » peut vouloir dire, et ne peut pas | le **chemin** est fixé par les arêtes, mais le **nombre de tours de boucle** dépend du drapeau `REVISION` rendu par le LLM. Asserter l'égalité exacte des deux séquences ferait échouer le pilote le jour où le critique répond `non` au premier tour. Le pilote asserte donc la **forme du chemin** (nœuds, ordre, alternance, terminaison sur `arbitre`) et borne séparément le nombre de tours. |
| Le repli des répétitions se fait **par identité de nœud**, pas par voisinage | la boucle alterne `redacteur, critique` : ses répétitions ne sont **pas** consécutives. Une première version repliait les seuls voisins identiques et rendait la séquence intacte — elle faisait **échouer le pilote sur un graphe correct** (mesure : `ORDRE FIXE: FAIL`). Un défaut de l'assertion, pas du graphe. |
| `agent_framework.__version__` **ne décrit pas** ce qui s'exécute | il rend la version du **métapaquet** (1.2.2 sur cet env), simple agrégateur de dépendances, alors que le cœur chargé est `agent-framework-core` (1.9.0). C'est le second numéro qui vaut ; un relevé qui cite le premier se trompe de deux ordres de version. |
| MAF était déjà dans le dépôt, à une version **sous son propre pin** | le harnais du prover déclare `agent-framework-openai>=1.3.0,<2.0.0` (`agent_tests/requirements.txt`), mais l'env ne portait que 1.2.2 du paquet agrégateur — les deux numéros divergent et le pin porte sur le **connecteur**, pas sur l'agrégateur. Installation alignée avant mesure (règle F : réparer, jamais contourner) ; `agent-framework-openai` 1.8.2, cœur 1.9.0. |

**Ce que le relevé apprend pour l'évaluation comparative.** SK et MAF ne répondent pas à la même question. SK offre une **bibliothèque de topologies prêtes** (séquentiel, concurrent, group chat, Magentic, handoff) où le choix de l'orateur est délégué à un manager — donc à un LLM dès que la topologie est dynamique. MAF offre un **graphe** où la topologie est écrite, donc inspectable et testable hors LLM, au prix de l'écrire soi-même. Le déterminisme n'est pas une propriété du framework mais de **ce qu'on met dans le graphe** : le prover Lean s'en sert précisément pour rendre son routage vérifiable (`SwitchCaseEdgeGroup` sur `msg.next_agent`), là où un manager Magentic l'aurait rendu probabiliste. Les deux couches sont donc complémentaires plutôt que concurrentes sur ce point, et le critère de choix est la **nature de la décision de routage** : écrite → MAF, déléguée → SK.

### 2.7 Couverture C# — mesurée par les assemblages, pas par la documentation

`VÉRIFIÉ` — sonde [`eval-pilots/csharp_coverage_probe.cs`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/csharp_coverage_probe.cs), exécutée sous .NET **10.0.204** (`dotnet run csharp_coverage_probe.cs`), exit 0.

Le point 4 de l'issue demande « ce que chaque moteur offre réellement en C# ». La méthode n'interroge pas la documentation mais **énumère les types publics des assemblages réellement déployés** par le restaurateur de paquets : un type absent de cette énumération n'est pas utilisable, quelle que soit la doc.

**Ce que la mesure renverse.** L'intuition naturelle — SK est le moteur historique du dépôt, donc le plus mature en C# — est fausse sur la couche agents. Les cinq objets d'orchestration mesurés en Python 1.41.3 (§2.3 à §2.5) **n'existent pas** dans SK C# 1.81.0, qui n'expose que le modèle historique `AgentGroupChat`. Ils existent tous les cinq dans **MAF C# 1.24.0**, avec le checkpoint et l'OTel que l'issue demande au point 3. Autrement dit, la couche la plus récente de SK est **Python d'abord**, tandis que MAF est **C# d'abord**.

| Moteur | Version mesurée | Types publics | Orchestration multi-agents en C# |
| --- | --- | --- | --- |
| Semantic Kernel | famille `Microsoft.SemanticKernel*` 1.81.0 — **4 assemblages**, dont `…Agents.Core` qui porte **17** types | **210** (union) | **modèle historique seul** : `AgentGroupChat`, `AgentGroupChatSettings`, `SequentialSelectionStrategy`, `ChatCompletionAgent` |
| MS Agent Framework | famille `Microsoft.Agents.AI*` 1.24.0 — **3 assemblages**, dont `…Workflows` qui porte **132** types | **285** (union) | **les cinq topologies** : `SequentialWorkflowBuilder`, `ConcurrentWorkflowBuilder`, `GroupChatWorkflowBuilder`, `MagenticWorkflowBuilder`, `HandoffWorkflowBuilder`, plus `WorkflowBuilder` |
| Google ADK | — | — | **aucune distribution C#** |

**Ce que le chiffre est, et ce qu'il n'est pas** (précision apportée en réponse à une review). `210` et `285` sont l'**union dédoublonnée sur le nom court** des types publics de **toute la famille** d'assemblages préfixée, pas le compte d'un assemblage : le détail par assemblage est publié dans la trace ci-dessous (`Agents.Core` = 17, `Agents.Abstractions` = 27, `Abstractions` = 132, `Core` = 35 → union 210). Deux conséquences assumées : le total **dépend de ce que le projet hôte a restauré** (un connecteur de plus le gonfle), et deux types homonymes de namespaces différents y fusionnent — c'est donc un **plancher**, jamais un compte de types. Le propos de fond ne s'appuie pas sur ces totaux mais sur les **contrôles nommés** qui suivent.

Le contrôle négatif est lui aussi triangulé, parce qu'un contrôle par **nom exact** ne teste qu'une **convention de nommage** (celle de la couche agents Python) et pas la surface d'API C# : il est doublé d'un contrôle **par forme** (tout type SK C# en `*Orchestration`) et d'un contrôle **par assemblage** (`Microsoft.SemanticKernel.Agents.Orchestration.dll` déployé). Les trois rendent « absent » — c'est ce qui donne sa force à l'affirmation.

Capacités MAF C# mesurées, qui répondent directement au point 3 de l'issue :

| Capacité demandée | Type mesuré |
| --- | --- |
| reprise d'un long run (checkpoint) | `CheckpointManager`, `CheckpointInfo`, `FileSystemJsonCheckpointStore`, `WorkflowSessionCheckpointRecovery` |
| observabilité (traces OTel) | `OpenTelemetryWorkflowBuilderExtensions` |
| ledger du manager Magentic | `MagenticProgressLedger` (le pendant C# du `ProgressLedger` mesuré en Python, §2.5) |
| tour de table borné | `RoundRobinGroupChatManager` |

Trace d'exécution (abrégée — les lignes de contrôle individuelles sont ci-dessus) :

```text
SK (C#) -- 4 assemblage(s) balaye(s) :
   Microsoft.SemanticKernel.Abstractions.dll                    132
   Microsoft.SemanticKernel.Agents.Abstractions.dll              27
   Microsoft.SemanticKernel.Agents.Core.dll                      17
   Microsoft.SemanticKernel.Core.dll                             35
   union dedoublonnee (nom court)                               210   <- PLANCHER, pas un compte de types

MAF (C#) -- 3 assemblage(s) balaye(s) :
   Microsoft.Agents.AI.Abstractions.dll                          28
   Microsoft.Agents.AI.Workflows.dll                            132
   Microsoft.Agents.AI.dll                                      125
   union dedoublonnee (nom court)                               285   <- PLANCHER, pas un compte de types

CONTROLE NEGATIF -- l'orchestration de la couche agents SK Python doit etre ABSENTE du C#
   (a) par FORME -- types SK C# en `*Orchestration` : aucun  OK
   (b) par ASSEMBLAGE -- `Microsoft.SemanticKernel.Agents.Orchestration` deploye : non  OK
   (c) par NOM EXACT (convention Python) :
       absent  OK  SequentialOrchestration
       absent  OK  ConcurrentOrchestration
       absent  OK  GroupChatOrchestration
       absent  OK  MagenticOrchestration
       absent  OK  HandoffOrchestration

CONTROLE POSITIF -- les cinq topologies doivent etre PRESENTES dans MAF C#
   present OK  SequentialWorkflowBuilder
   present OK  ConcurrentWorkflowBuilder
   present OK  GroupChatWorkflowBuilder
   present OK  MagenticWorkflowBuilder
   present OK  HandoffWorkflowBuilder
   present OK  WorkflowBuilder

GOOGLE ADK (C#) -- balayage des assemblages deployes
   Google.Protobuf.dll

VERDICT controles : negatif=OK positif=OK
```

**Sur Google ADK (C#).** Le paquet officiel n'existe pas : `Google.Adk` est introuvable sur NuGet, et la recherche par mots-clés ne remonte que des homonymes tiers (`NTG.Adk` est un kit d'aviation, `Hazina.LLMs.GoogleADK` une enveloppe communautaire à quelques centaines de téléchargements). La sonde le mesure par **balayage du répertoire de sortie** : la seule assembly « Google » présente est `Google.Protobuf.dll`, dépendance transitive sans rapport avec un moteur agentique. Pour un dépôt qui enseigne en **.NET Interactive**, l'écart est décisif et se lit sans hypothèse.

**Ce que le relevé apprend pour l'évaluation comparative.** La question « quel moteur pour la distillation » reçoit ici une contrainte dure qui n'était pas visible dans la grille du 11/09 : nos séries sont **bilingues**, et un moteur qui n'existe qu'en Python oblige à maintenir deux piles pour un même enseignement. Sur ce critère, MAF couvre **les deux langages avec les mêmes topologies**, SK ne les couvre qu'en Python sur la couche agents, et ADK n'a pas de C# du tout. Cela ne tranche pas l'arbitrage — la maturité runtime et la dette de migration restent à mesurer — mais cela déplace un critère de « préférence » vers un **fait mesuré**.

**Forme du livrable, et pourquoi.** La sonde est une **app mono-fichier** (.NET 10, directives `#:package`) : aucun `.csproj` n'est ajouté au dépôt, donc aucun impact sur `MyIA.CoursIA.sln`, `MyIA.AI.Shared.sln` ni sur les workflows .NET (tous filtrés par chemin) — un projet orphelin aurait été happé par l'un ou l'autre. La reproduction demande le réseau pour la restauration des paquets, comme les pilotes Python demandent une clé d'API.

**Les traces d'exécution sont committées** ([`eval-pilots/traces/`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/)) : les `stdout` des six pilotes, tels quels — pour qu'une affirmation `VÉRIFIÉ` de ce document soit une **propriété du dépôt** et non du poste de l'auteur. Le `stderr` n'est pas committé : les avertissements Python y impriment des chemins absolus, et un fichier committé n'en porte pas. La séparation est faite **à la capture**, jamais par retrait de lignes après coup. Une trace committée n'est pas un contrôle — le contrôle est le pilote, rejouable par la commande du README ; la trace est le témoin daté.

**Le coût de ce choix est payé, et il est petit.** Un `.csproj` hors solution aurait aussi rendu T6 rejouable ; l'app mono-fichier ne le fait pas *par elle-même* — les versions de paquets doivent être lisibles quelque part en dehors des directives. C'est le rôle de [`eval-pilots/README.md`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/README.md) : il porte les trois versions épinglées, la commande de restauration, l'interpréteur des pilotes Python et le modèle épinglé. T6 est donc rejouable depuis le dépôt seul, sans `.csproj` ni impact sur les solutions.

**Deux pièges de méthode, tous deux payés par une erreur réelle.** `Assembly.Load("<nom>")` ne suffit pas : rien ne référence ces assemblages, donc rien ne les charge, et la sonde rend « aucune assembly » sur un projet pourtant correctement restauré — il faut charger **par chemin** depuis le répertoire de sortie. Et un détecteur se valide par ses **faux négatifs**, pas par ses hits : d'où le contrôle négatif ci-dessus. Sans lui, « 0 hit » serait indiscernable de « sonde cassée » — le mode de défaut qui a fait passer pour un « résidu » un lake portant 80 % de la dette formelle du dépôt (règle anti-régression).

### 2.8 À venir

Reste de #14499 : le pilote identique dans les trois moteurs sur une **vraie charge de distillation** (point 3), et le coût pour le dépôt (point 5). L'emplacement `eval-pilots/` accueille les pilotes Python et la sonde C# ; l'idiome de référence de MAF est l'organe du dépôt (`SymbolicAI/Lean/agent_tests/prover/workflow.py`).
