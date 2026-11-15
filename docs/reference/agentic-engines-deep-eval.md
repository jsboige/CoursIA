# Évaluation approfondie des moteurs agentiques — ADK vs Semantic Kernel vs MS Agent Framework

> REFERENCE — vivante — dernière révision 2026-11-11

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
| T7 | pt 2 — MAF, couche agents : `HandoffBuilder` exécuté (service LLM réel, temp 0), contrôle positif des cinq topologies Python | livré |
| T8 | pt 2 — MAF, couche agents : `GroupChatBuilder` (selection function) + `MagenticBuilder` (manageur + ledger) exécutés (service LLM réel, temp 0) | livré |
| P1 | pt 3 — pilote identique, réplique **SK** : charge de distillation figée + `GroupChatOrchestration` à manager custom, exécuté (service LLM réel, temp 0, 2 runs) | livré |
| P2 | pt 3 — réplique **MAF** sur la même fixture, même politique de tour (`GroupChatBuilder` + selection function + termination condition) | livré |
| P3 | pt 3 — réplique **ADK** sur la même fixture, même politique de tour (boucle Python de désignation explicite + `InMemorySessionService` partagée) | livré |
| — | coût pour le dépôt (pt 5) | livré (§4) |
| — | pt 1 état de l'art | livré hors repo : note datée du 2026-10-05 sur [#19380](https://github.com/jsboige/CoursIA/issues/19380) — **périmée au 2026-11-06 et remplacée par le §5** de ce document ; mémo inventaire local du 2026-10-07 (po-2024:CoursIA-2) sur [#14499](https://github.com/jsboige/CoursIA/issues/14499) |
| Q17 | pt 1 **rafraîchi** + axes API courantes / trajectoire / besoins réels | livré (§5) — versions et cadence remesurées au 2026-11-04, sondes d'API rejouées aux versions courantes |
| — | pts 3-5 (déterminisme, couverture langages, coût) | livrés (§2-§4) |
| — | pt 6 verdict par critère | réservé à ai-01 + user |

## 2. Modes d'orchestration — exemples exécutés

### 2.1 Semantic Kernel — couverture réelle du dépôt (mesuré)

`VERIFIÉ` (lecture intégrale du carnet [`06-SemanticKernel-ProcessFramework.ipynb`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb), kernel python3, twin exécuté de bout en bout) :

- la série démontre des pipelines **séquentiels manuels** (`run_content_pipeline`, `run_iterative_pipeline` : boucle de révision explicite en Python) ;
- l'API **événementielle** du Process Framework (`ProcessBuilder` + `on_event`/`send_event_to`) n'apparaît **que en prose** (sections descriptives et schéma d'architecture) — **aucune cellule ne l'exécute** ;
- le point user « orchestration événementielle sous-exploitée » ([#14499](https://github.com/jsboige/CoursIA/issues/14499), contre-point 2) est donc **confirmé par la mesure** : le mode est documenté mais jamais exécuté dans le corpus.

Mesure mécanique, pour que la claim ne repose pas sur une « lecture intégrale » déclarée — comptage des occurrences sur le JSON du carnet : `semantic_kernel.processes` **0**, `ProcessStep` **0**, `ProcessEvent` **0**, `LocalRuntime` **0**, `@step` **0** ; `ProcessBuilder` **2** et `KernelProcess` **1**, tous deux en **markdown**. Les deux cellules de code qui portent le mot `step` (`PipelineMetrics` cellule 16, `WorkflowBuilder` cellule 21) sont des **stubs d'exercice** (`TODO etudiant`, corps en `pass`/`return None`) — un échafaudage pédagogique local, pas l'API du framework. Aucune cellule n'importe le moteur.

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

`VERIFIÉ` — pilote [`07-Agent-Orchestration/eval-pilots/adk_handoff_pilot.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Agent-Orchestration/eval-pilots/adk_handoff_pilot.py), exécuté sous `py -3.11` / google-adk **2.8.0** via l'**organe du track** ([`utils/adk_runtime.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Agent-Orchestration/utils/adk_runtime.py) : `build_agent` + `run_agent_turn` ; [`utils/adk_orchestrator.py`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Agent-Orchestration/utils/adk_orchestrator.py) : `AdkOrchestrator`) — aucune réimplémentation. Service **réel** `gpt-4o-mini`, température 0 (même modèle, même réglage, même scénario de triage que le pilote T2 — les deux moteurs deviennent directement comparables **par construction** : le modèle est épinglé en constante dans les deux pilotes, aucune sonde ne peut le substituer), budget ex-post 12 appels mesuré par les snapshots d'usage du contrat C6. Reproduction firsthand depuis l'emplacement livré : exit 0.

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

**Ce que la mesure renverse.** L'intuition naturelle — SK est le moteur historique du dépôt, donc le plus mature en C# — est fausse sur la couche agents. Les cinq objets d'orchestration mesurés en Python 1.41.3 (§2.3 à §2.5) **n'existent pas dans la surface stable** de SK C# 1.81.0, qui n'expose que le modèle historique `AgentGroupChat`. Ils existent tous les cinq dans **MAF C# 1.24.0**, avec le checkpoint et l'OTel que l'issue demande au point 3. Autrement dit, la couche la plus récente de SK est **Python d'abord**, tandis que MAF est **C# d'abord**.

> **Précision Q17 (2026-11-04)** — la phrase ci-dessus est **trop forte**, et la mesure l'a renversée : l'orchestration C# de SK **existe et est publiée**, mais **uniquement en version `-preview`** (`Microsoft.SemanticKernel.Agents.Orchestration` et `…Agents.Magentic`, qui n'ont jamais eu de version stable). La formulation exacte, mesurée et sourcée, est au **§5.6**. Ce que T6 établit reste vrai : ces topologies **ne sont pas** dans la surface stable, et le checkpoint comme l'OTel SK C# sont absents des **deux** surfaces.

| Moteur | Version mesurée | Types publics | Orchestration multi-agents en C# |
| --- | --- | --- | --- |
| Semantic Kernel | famille `Microsoft.SemanticKernel*` 1.81.0 — **4 assemblages**, dont `…Agents.Core` qui porte **17** types | **210** (union) | **modèle historique seul** : `AgentGroupChat`, `AgentGroupChatSettings`, `SequentialSelectionStrategy`, `ChatCompletionAgent` |
| MS Agent Framework | famille `Microsoft.Agents.AI*` 1.27.0 — **3 assemblages**, dont `…Workflows` qui porte **132** types | **286** (union) | **les cinq topologies** : `SequentialWorkflowBuilder`, `ConcurrentWorkflowBuilder`, `GroupChatWorkflowBuilder`, `MagenticWorkflowBuilder`, `HandoffWorkflowBuilder`, plus `WorkflowBuilder` |
| Google ADK | — | — | **aucune distribution C#** |

**Re-mesure Q17 du 2026-11-04** ([`eval-pilots/traces/out-Q17-csharp-coverage-1.27.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-csharp-coverage-1.27.0.txt), sortie 0, contrôles négatif et positif au vert). La sonde T6 mesurait MAF C# **1.24.0** ; elle a été rejouée à la version courante **1.27.0**. Le delta est faible mais réel : l'union dédoublonnée passe de **285 à 286** types, les quatre assemblages SK restent **inchangés** (`Abstractions` 132, `Agents.Abstractions` 27, `Agents.Core` 17, `Core` 35 → union **210**, identique à T6, SK .NET n'ayant rien publié depuis le 2026-10-06), et MAF C# garde les trois mêmes assemblages (`Agents.AI.Abstractions` 28, `Agents.AI.Workflows` 132, `Agents.AI` 126). **Aucun type n'a disparu** : les cinq topologies, les capacités de checkpoint et d'OTel sont toutes encore là.

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

**Forme du livrable, et pourquoi.** La sonde est une **app mono-fichier** (.NET 10, directives `#:package`) : aucun `.csproj` n'est ajouté au dépôt, donc aucun impact sur `dotnet/MyIA.CoursIA.sln`, `dotnet/MyIA.AI.Shared/MyIA.AI.Shared.sln` ni sur les workflows .NET (tous filtrés par chemin) — un projet orphelin aurait été happé par l'un ou l'autre. La reproduction demande le réseau pour la restauration des paquets, comme les pilotes Python demandent une clé d'API.

**Les traces d'exécution sont committées** ([`eval-pilots/traces/`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/)) : les `stdout` des pilotes, tels quels — pour qu'une affirmation `VÉRIFIÉ` de ce document soit une **propriété du dépôt** et non du poste de l'auteur. Le `stderr` n'est pas committé : les avertissements Python y impriment des chemins absolus, et un fichier committé n'en porte pas. La séparation est faite **à la capture**, jamais par retrait de lignes après coup. Une trace committée n'est pas un contrôle — le contrôle est le pilote, rejouable par la commande du README ; la trace est le témoin daté.

**Le coût de ce choix est payé, et il est petit.** Un `.csproj` hors solution aurait aussi rendu T6 rejouable ; l'app mono-fichier ne le fait pas *par elle-même* — les versions de paquets doivent être lisibles quelque part en dehors des directives. C'est le rôle de [`eval-pilots/README.md`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/README.md) : il porte les trois versions épinglées, la commande de restauration, l'interpréteur des pilotes Python et le modèle épinglé. T6 est donc rejouable depuis le dépôt seul, sans `.csproj` ni impact sur les solutions.

**Deux pièges de méthode, tous deux payés par une erreur réelle.** `Assembly.Load("<nom>")` ne suffit pas : rien ne référence ces assemblages, donc rien ne les charge, et la sonde rend « aucune assembly » sur un projet pourtant correctement restauré — il faut charger **par chemin** depuis le répertoire de sortie. Et un détecteur se valide par ses **faux négatifs**, pas par ses hits : d'où le contrôle négatif ci-dessus. Sans lui, « 0 hit » serait indiscernable de « sonde cassée » — le mode de défaut qui a fait passer pour un « résidu » un lake portant 80 % de la dette formelle du dépôt (règle anti-régression).

### 2.8 Pilote MAF — la couche agents (HandoffBuilder)

`VERIFIÉ` — pilote [`eval-pilots/maf_agents_handoff_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/maf_agents_handoff_pilot.py), exécuté sous le **venv projet** (Python 3.13) / `agent-framework-core` **1.21.0** + `agent-framework-orchestrations` **1.3.1** (lignes alignées pour la mesure — l'env portait core 1.15.0 avec orchestrations 1.1.1, incompatible sur le protocole request-info ; règle F), service **réel** `gpt-4o-mini`, température 0, `max_tokens` 200, budget **dur** de 40 appels comptés par un client instrumenté. Même scénario de triage que T2 (§2.3) et T3 (§2.4), même modèle épinglé en constante — les **trois** moteurs sont comparables par construction. Reproduction firsthand depuis l'emplacement livré : exit 0, **deux fois** (le second processus sert de mesure inter-processus du déterminisme).

```text
MAF versions: agent-framework-core 1.21.0, agent-framework-orchestrations 1.3.1
sonde OK (1 appel(s))
TOPOLOGIES PYTHON: Sequential, Concurrent, GroupChat, Magentic, Handoff
[technique #1] agents=['triage', 'specialiste_technique'] decision: specialiste_technique
[technique #2] agents=['triage', 'specialiste_technique'] decision: specialiste_technique
[formation #1] agents=['triage', 'specialiste_formation'] decision: specialiste_formation
[formation #2] agents=['triage', 'specialiste_formation'] decision: specialiste_formation
ROUTING CORRECTNESS: OK
ROUTING DETERMINISM: OK
LLM CALLS: 9/40
PILOT OK maf handoff model=gpt-4o-mini
```

**Déterminisme (pt 3, troisième moteur, troisième datapoint identique)** : à température 0, la décision de routage (quel spécialiste termine) est stable intra-processus et inter-processus ; la prose n'est pas assertée — même doctrine que T2/T3. Profil de coût identique à T2 : **exactement 2 appels LLM par run** (1 triage + 1 spécialiste), la sonde mise à part.

**La couche agents de MAF existe, mais elle vit dans un paquet séparé.** T5 (§2.6) pouvait laisser croire que MAF Python se réduit au graphe typé : c'est un artefact de périmètre, pas de nature. Les cinq topologies mesurées en C# par T6 existent en Python dans `agent-framework-orchestrations` — contrôle positif par import, zéro appel LLM : `SequentialBuilder`, `ConcurrentBuilder`, `GroupChatBuilder`, `MagenticBuilder`, `HandoffBuilder`. La parité C#/Python est donc réelle sur la couche agents (là où SK est Python d'abord, §2.7), et les **deux natures de routage coexistent chez MAF** : graphe écrit dans le cœur (T5), topologies déléguées dans orchestrations (ce pilote) — la conclusion du §2.6 se précise sans être renversée.

Faits d'API mesurés sur core 1.21.0 / orchestrations 1.3.1 :

| Fait | Détail |
| --- | --- |
| Drapeau obligatoire | `HandoffBuilder.build()` jette `ValueError` si un participant n'a pas `require_per_service_call_history_persistence=True` (« local history stays consistent with the service across handoff tool-call short-circuits »). |
| Agent de départ explicite | `with_start_agent(agent)` obligatoire — `build()` jette sinon (« Must call with_start_agent(...) before building the workflow »). |
| Entrée et lancement | message explicite `Message(role="user", contents=[Content(type="text", …)])` + `workflow.run(msg)` direct. `WorkflowAgent(workflow).run(...)` bute sur le handshake request-info du handoff (`AgentInvalidResponseException: Unexpected content type while awaiting request info responses`) — mesuré sur deux lignes de versions alignées, ce n'est pas un artefact de dérive. |
| Observable du locuteur | l'identité d'agent ne vit **ni** dans `AgentResponse` ni dans `Message` : c'est l'event qui la porte. Seuls les events `type='output'` (`executor_id` + réponse) marquent un tour de parole réel ; `executor_invoked`/`executor_completed` partent **aussi** pour les rounds du protocole interne (`should_respond=False`, sans appel LLM) — les compter fait lire un mesh bouclant là où la conversation réelle est `triage → spécialiste → fin`. |
| Terminaison | le workflow est en **posture interactive** : après la réponse du spécialiste il émet une `request_info` (`HandoffAgentUserRequest`) et attend l'utilisateur. Réutiliser le même workflow pour une nouvelle entrée fait avancer l'état mais laisse la requête pendante (warning « fresh message while request_info events are still pending ») — même hygiène que T2 : **reconstruire le workflow par invocation** (agents réutilisables, eux). |
| Spécialistes puits | un participant sans `add_handoff` déclenche un warning (« your workflow may get stuck ») mais est un **puits légitime** : le run termine sur sa réponse. Le warning se lit « ce agent ne peut pas re-transférer », pas « erreur ». |
| Comptage de versions | `agent_framework.__version__` (metapaquet) et `agent-framework-core` divergent — leçon déjà inscrite en T5, toujours vraie en 1.21. |

### 2.9 Pilote MAF couche agents — GroupChat (selection function) et Magentic (manageur + ledger)


`VÉRIFIÉ` — pilote [`eval-pilots/maf_groupchat_magentic_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/maf_groupchat_magentic_pilot.py), exécuté sous `agent-framework-core` **1.21.0** / `agent-framework-orchestrations` **1.3.1** (env venv du dépôt — le cœur a avancé depuis T5/T7), service **réel** (`gpt-4o-mini`, température 0, `max_tokens` 200, budget **dur de 60 appels** compté par un client instrumenté qui jette au-delà). Même banc de triage que T2/T3/T7 : deux entrées non ambiguës × deux exécutions par topologie. Reproduction firsthand depuis l'emplacement livré : exit 0.

Les deux topologies mesurées ici complètent la couche agents MAF entamée par T7 (handoff) — et elles portent **la question topologique décisive** pour l'évaluation comparative :

- **GroupChat** — qui parle ensuite n'est **pas négocié par un protocole du moteur** : c'est une **selection function que nous écrivons**, appelée à chaque tour avec l'état de la conversation (`GroupChatState(current_round, participants, conversation)`). Le pilote mesure ce seam : le triage répond en nommant son spécialiste (`SPECIALISTE TECHNIQUE` / `SPECIALISTE FORMATION` en majuscules), la selection function lit la conversation et route ;
- **Magentic** — le pattern orchestrateur : un agent **manageur** découpe la demande en une tâche confiée au spécialiste, le **ledger** (plan + avancement, en JSON) piste l'exécution, sous borne `max_round_count=1`.

Trace d'exécution (les deux runs — même process et processus frais — sont byte-identiques) :

```text
MAF versions: agent-framework-core 1.21.0, agent-framework-orchestrations 1.3.1
[GC technique #1/#2] agents=['triage', 'specialiste_technique'] decision: specialiste_technique
[GC formation #1/#2] agents=['triage', 'specialiste_formation'] decision: specialiste_formation
[MG technique #1/#2] participation: specialiste_technique
[MG formation  #1/#2] participation: specialiste_formation
GC ROUTING CORRECTNESS: OK / DETERMINISM: OK
MG PARTICIPATION CORRECTNESS: OK / DETERMINISM: OK
LLM CALLS: total 25/60 (groupchat 8, magentic 16)
PILOT OK maf groupchat+magentic model=gpt-4o-mini
```

**Déterminisme (pt 3, datapoint MAF couche agents)** : même doctrine que T2/T3/T7 — à température 0 on asserte la **décision** (quel spécialiste a parlé / participé), jamais la prose. Mesuré stable en intra-processus (2 exécutions par entrée) **et** inter-processus (relance complète : traces byte-identiques, y compris la répartition des appels 8/16).

Faits d'API mesurés sur orchestrations 1.3.1 :

| Fait | Détail |
| --- | --- |
| L'observable T7 ne dit pas qui a parlé ici | les events `type='output'` d'un GroupChat/Magentic portent l'id de l'**orchestrateur** (`group_chat_orchestrator` / `magentic_orchestrator`), pas des participants. Le tour de parole réel vit dans les events `type='group_chat'` : leur `data` est soit un `GroupChatRequestSentEvent` (tâche envoyée — sans appel LLM) soit un `GroupChatResponseReceivedEvent` (vraie réponse, champ `participant_name`). Seul le second compte. |
| **Le même extracteur sert les deux topologies** | Magentic **embarque un group chat interne** : ses tours de spécialistes passent aussi par des events `group_chat` → la fonction `auteurs()` du pilote (filtre `ResponseReceived` → `participant_name`) fonctionne à l'identique pour GroupChat et Magentic. Le plan du manageur, lui, vit dans les events `magentic_orchestrator` — hors tours de parole. |
| `executor_invoked`/`completed` partent aussi pour les rounds de protocole | ils tirent pour des rounds `should_respond=False` **sans appel LLM** (mesuré sur le flux complet d'un run) — les compter comme des tours surévalue la participation. C'est le même piège que le T7, vu de la couche orchestration. |
| Le manageur Magentic exige son **propre plafond de tokens** | ses prompts de ledger demandent du **JSON** (plan, avancement). À `max_tokens=200` le JSON est tronqué → `Progress ledger JSON parse failed (attempt 3/3): Unbalanced JSON braces` → l'orchestrateur RESET puis `Max round count reached` **sans que le plan n'ait jamais été consommé**. À 600 tokens pour le seul manageur (les spécialistes restent à 200), le ledger parse proprement et le routage s'exécute. Même famille que le fait SK §2.5 (manager Magentic = JSON structuré = budget dédié) — la contrainte est dans le **pattern Magentic**, pas dans le moteur. |
| La selection function est le seam evaluable | `GroupChatState.participants` est un `OrderedDict` (identifiant → description) ; `current_round` part à 0 (premier appel = qui ouvre), et `conversation[-1]` est la réponse à router. `TerminationCondition` n'est **pas** importable du top-level `agent_framework` — la borne passe par `max_rounds` du builder. |
| Coût par topologie | GroupChat : **2 appels/run** (triage + spécialiste, `max_rounds=2`) ; Magentic : **4 appels/run** (plan + ledger du manageur + réponse du spécialiste + ledger final) — le pattern orchestrateur coûte le double du routage par selection function sur ce banc. |

**Ce que le relevé apprend pour l'évaluation comparative.** Le §2.6 concluait que MAF-graph donne un routage **écrit** là où SK-Magentic le délègue à un LLM. La couche agents MAF nuance la partition : `GroupChatBuilder` rend le routage **écrit sans écrire le graphe** — la selection function est notre code appelé par le moteur, exactement le compromis que le handoff T7 délègue au protocole et que le graphe T5 impose en arêtes. Les trois couches forment un spectre (délégué → callable nôtre → graphe nôtre), et GroupChat en est **le point médian** : déterminisme testable hors LLM (la fonction est pure Python sur l'état) sans le coût d'écriture du graphe. Magentic, lui, reste le pattern délégué — avec la même exigence de budget de tokens du manageur que SK, et un coût par run double sur ce banc.

### 2.10 À venir

Le suivi des tranches vit dans le tableau **État du document** en tête de ce document, pas ici : le seul point du protocole encore ouvert est le **verdict par critère** (point 6), que le protocole réserve à l'arbitrage ai-01 + user. L'emplacement `eval-pilots/` accueille les pilotes Python et la sonde C# ; l'idiome de référence du graphe MAF est l'organe du dépôt (`SymbolicAI/Lean/agent_tests/prover/workflow.py`).

## 3. Pilote identique sur une vraie charge de distillation (point 3)

### 3.1 La charge partagée — fixture figée

`VERIFIÉ` (fixture [`distill_charge_fixture.md`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/distill_charge_fixture.md)) : la charge est la **section réelle** d'ouverture de [`01-SemanticKernel-Intro.ipynb`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb) (cellules 0-8 : objectifs, prérequis, sommaire, première cellule de code), extraite puis **figée** à la tête `8e9eaaaa0`. Écart **déclaré** dans le header de la fixture : la cellule 8, l'unique cellule d'authentification de la section, est tronquée par le budget de fixture — la charge distillée ne couvre donc pas l'authentification, et c'est un choix de borne, pas une caractéristique du carnet. Les trois répliques (P1 SK, P2 MAF, P3 ADK) distillent **ce fichier**, pas le carnet vivant — la charge est byte-stable entre moteurs, entre exécutions et entre dates.

### 3.2 P1 — Semantic Kernel : `GroupChatOrchestration` à manager custom

`VERIFIÉ` (pilote [`sk_distillation_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/sk_distillation_pilot.py), LOC self-mesurées reportées dans la trace [`out-P1-sk-distillation.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P1-sk-distillation.txt), sk 1.41.3, gpt-4o-mini temp 0, budget dur 16) :

- **La politique de tour vit dans le moteur** : trois `ChatCompletionAgent` (producteur ≤ 120 mots, critique à verdict imposé `VERDICT: ACCEPTE|REVISION:`, arbitre à `DECISION:`) reliés par `GroupChatOrchestration`, dont le manager custom `DistillationGroupChatManager` encode producteur → critique → [révision → producteur → critique] → arbitre dans `select_next_agent`, et scelle dans `should_terminate`. C'est la pièce que P2/P3 ré-encoderont dans l'idiome de leur moteur (graphe typé / boucle) — **même politique, organe différent**.
- **Mesures** (2 exécutions complètes) : 3 appels LLM/run, latences 1,82/0,69/0,83 s puis 1,83/0,72/0,77 s, mur 3,46/3,42 s, total 8/16 appels (sondes comprises). **Déterminisme OK** : (tours, décision, tour d'arbitrage) = (1, ACCEPTE, 1) identique sur les deux runs.
- **Comportement en échec** : une sonde sur un modèle inexistant échoue fort (`ServiceResponseException`, type nommé, clé jamais affichée) — aucun repli, aucune tentative masquée.
- **Deux constats de moteur, pas des trous du pilote** : (1) l'orchestration GroupChat appelle les agents **en streaming** — le compteur d'appels doit surcharger `get_streaming_chat_message_contents`, pas seulement la voie non-streaming (première version du pilote : 6 appels invisibles au compteur) ; (2) les chunks streaming n'exposent **pas** l'usage de jetons (l'API ne le rend que sur `stream_options.include_usage`, que SK ne positionne pas) — la mesure « tokens par appel » exige la voie non-streaming ; sur ce banc, la latence et le compte d'appels sont mesurés, les jetons sont `n/d` pour les tours d'agents. C'est une **différence d'observabilité par mode d'invocation**, audible pour le point 6.
- **Réserve de couverture, levée par ré-exécution.** La mesure initiale (ci-dessus) datait d'**avant** la documentation de la troncature de la cellule 8 : le critique acceptait au tour 1, seule la voie ACCEPTE était exercée. Le pilote a été **ré-exécuté sur la fixture réparée** (4859 caractères, troncature déclarée) : le critique rejette alors au tour 1 (`VERDICT: REVISION:` — la distillation ne couvre pas l'authentification), le producteur révise, le critique rejette de nouveau, l'arbitre scelle en `DECISION: RESIDUEL tour 1`. Séquence : producteur → critique → producteur → critique → arbitre (2 tours), déterminisme structurel OK sur les deux runs, 12/16 appels. **La branche RÉVISION du manager SK est donc exercée**, et le résultat **converge avec P2 (MAF)** : même séquence d'auteurs, même type de décision, même tour d'arbitrage. La divergence de verdict P1(ACCEPTE)/P2(RESIDUEL) relevait bien de la **charge**, pas du moteur — désormais prouvé par ré-exécution à charge identique. C'est la comparaison strictement à charge identique que le point 3 appelait.

### 3.3 P2 — Microsoft Agent Framework : `GroupChatBuilder` à selection function

`VERIFIÉ` (pilote [`maf_distillation_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/maf_distillation_pilot.py), trace [`out-P2-maf-distillation.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P2-maf-distillation.txt)) : la même politique de tour que P1, encodée cette fois dans une **selection function** appelée par le moteur à chaque tour avec `GroupChatState(current_round, participants, conversation)` — l'idiome MAF (`GroupChatBuilder`, orchestrations 1.3.1). Mêmes instructions mot pour mot, même fixture figée, même modèle épinglé `gpt-4o-mini` à température 0.

Relevé (deux runs, même process) :

```text
MAF versions: agent-framework-core 1.21.0, agent-framework-orchestrations 1.3.1, agent-framework-openai 1.16.0
sonde echec (modele inexistant): ChatClientException
[run 1] sequence: producteur -> critique -> producteur -> critique -> arbitre   verdict_final=REVISION   wall=7.23s
[run 2] sequence: producteur -> critique -> producteur -> critique -> arbitre   verdict_final=REVISION   wall=6.24s
    decision: DECISION: RESIDUEL tour 1: la cellule d'authentification est tronquee...
DETERMINISME (tours, decision, tour d'arbitrage): OK (2, 'RESIDUEL', '1') vs (2, 'RESIDUEL', '1')
LLM CALLS: 12/16
```

Le pilote reporte aussi ses LOC self-mesurées dans la trace (ligne `LOC PILOT`).

- **La branche RÉVISION est exercée ici, contrairement à P1.** En documentant la troncature de la cellule 8 dans la fixture (correctif de la review P1), la charge est devenue **non distillable complètement** : le critique rejette au tour 1 (`VERDICT: REVISION:` — la distillation ne couvre pas l'authentification), le producteur révise, le critique rejette de nouveau, l'arbitre scelle en `DECISION: RESIDUEL`. La politique conditionnelle complète (producteur → critique → révision → producteur → critique → arbitre) est donc mise à l'épreuve en P2, là où P1 n'exerçait que la voie ACCEPTE. C'est une couverture **gagnée par la réparation de la fixture**, pas par une charge écrite pour l'occasion.
- **Déterminisme asserti sur la structure, jamais la prose** : le tuple comparé est (tours, type de décision, entier du tour d'arbitrage) = `(2, RESIDUEL, 1)`. La phrase motivant le RESIDUEL varie entre runs (le LLM la reformule) ; le déterminisme ne la lit pas — c'est la même discipline qu'en P1, resserrée par une expression régulière sur `tour\s+(\d+)` plutôt qu'un découpage de chaîne fragile.

- **Écart d'environnement déclaré à l'installation** : `agent-framework-openai` n'existe **pas** en 1.21.0 sur PyPI (dernière disponible : 1.17.0, `pip index versions` le 29/10) — le connecteur est donc résolu par pip contre les pins `core 1.21.0` + `orchestrations 1.3.1` de T8 ; la ligne de versions effective est imprimée dans la trace (connecteur 1.16.0). Le constructeur prend `model=`, pas `model_id=`.
- **Deux pièges d'extraction, mesurés et corrigés** : (1) `GroupChatResponseReceivedEvent` ne porte **pas** le texte — seulement `round_index` et `participant_name` ; le texte vit dans l'event `executor_invoked` dont `data` est un `AgentExecutorResponse` (`executor_id` = nom de l'agent, `agent_response.text`/`.messages`). La séquence d'auteurs se lit donc sur les events `group_chat`, les textes sur les `AgentExecutorResponse`. (2) La selection function n'a **pas d'état terminal** : sans `termination_condition`, elle ré-élit l'arbitre jusqu'à `max_rounds`. La boucle se scelle donc par une `termination_condition` (`_apres_arbitre` : stop dès que le dernier auteur est l'arbitre), posée sur le builder — c'est l'homologue du `should_terminate` du manager SK de P1.
- **Comparabilité avec P1** : même fixture figée, même politique, même réglage, organe différent — exactement ce que vise le point 3. Chez SK la boucle vit dans un `GroupChatManager` custom (deux méthodes `select_next_agent`/`should_terminate`), chez MAF dans une selection function + une termination condition posées sur le builder. **Convergence prouvée à charge identique** : P1 a été ré-exécuté sur la fixture réparée (cf §3.2) et produit la **même** séquence (producteur → critique → producteur → critique → arbitre), le **même** type de décision (`RESIDUEL`), le **même** tour d'arbitrage (1) que P2. Les deux répliques ne divergent que sur l'idiome d'orchestration, pas sur le résultat — c'est la mesure centrale du point 3.

### 3.4 P3 — Google ADK : boucle Python de désignation explicite sur session partagée

`VERIFIÉ` (pilote [`adk_distillation_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/adk_distillation_pilot.py), trace [`out-P3-adk-distillation.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P3-adk-distillation.txt)) : la même politique de tour que P1/P2, mais **sans manager de group-chat ni selection function** — ADK n'a pas cet idiome dans notre setup. La politique vit dans une **boucle Python de désignation explicite** (contrat C4 de l'organe `AdkOrchestrator` du Track2, réutilisé tel quel) : notre code décide qui parle ensuite, invoque l'agent désigné via un `Runner` ADK sur une `InMemorySessionService` **partagée**, lit sa réponse, re-désigne. C'est exactement la différence de nature que le point 3 veut mesurer : là où SK/MAF exposent un point d'extension *orchestrateur* (manager, selection function), ADK expose des primitives (`Runner`, `SessionService`) et laisse la politique à l'appelant.

Relevé (deux runs, même process) :

```text
ADK version: google-adk 2.8.0
sonde echec (modele inexistant): NotFoundError
charge: distill_charge_fixture.md (4859 caracteres, fixture figee)
[run 1] tours=1 verdict_critique=ACCEPTE wall=4.03s
    sequence: producteur -> critique -> arbitre
    decision: DECISION: RESIDUEL tour 1: La cellule d'authentification est tronquee...
[run 2] tours=1 verdict_critique=ACCEPTE wall=4.56s
    sequence: producteur -> critique -> arbitre
    decision: DECISION: RESIDUEL tour 1: La cellule d'authentification est tronquee...
DETERMINISME (tours, decision, tour d'arbitrage): OK (1, 'RESIDUEL', '1') vs (1, 'RESIDUEL', '1')
LLM CALLS: 7/16
```

Le pilote reporte ses LOC self-mesurées dans la trace (ligne `LOC PILOT`).

- **Désignation explicite obligatoire, mesurée.** Passer `prompt=None` après le premier rôle (c'est-à-dire laisser ADK router par handoff implicite) produit des warnings `Event from an unknown agent` et des séquences d'auteurs instables — le routeur implicite ne connaît pas nos trois rôles. Le pilote passe donc à chaque tour un **prompt de désignation explicite** (« À toi de jouer, critique : … ») : la session partagée porte l'historique complet, le prompt ne fait que désigner. C'est l'équivalent ADK du contrat C4 de l'organe Track2, et c'est la condition de reproductibilité de la séquence.
- **Deux verdicts distincts, non contradictoires.** Le critique porte sur la **qualité de la distillation** (exactitude, non-invention, concision — il accepte), l'arbitre sur la **recevabilité au regard de la charge** (la cellule d'authentification est tronquée, il scelle en RESIDUEL). Le résumé du pilote affiche donc `verdict_critique` et `decision` séparément : un `ACCEPTE` du critique suivi d'un `RESIDUEL` de l'arbitre est un comportement correct, pas un bug d'extraction.
- **Variabilité inter-processus observée, honnêtement reportée.** Sur une exécution antérieure du même pilote, les deux runs ont divergé (`(1, RESIDUEL, 1)` vs `(2, ACCEPTE, 1)`) — un outlier LLM : la première critique a parfois demandé une RÉVISION au lieu d'accepter, changeant la structure du tour. Température 0 ne garantit donc pas l'identité structurelle inter-processus chez ADK, contrairement à ce que P1/P2 ont montré sur leur setup. La trace committée est la mesure **reproductible sur deux runs consécutifs du même process** ; l'outlier est documenté ici plutôt que masqué par une relance sélective. C'est un constat de moteur utile pour le point 3 (et cohérent avec §3.1 : la prose des spécialistes n'est pas byte-identique entre processus).
- **Comparabilité avec P1/P2** : même fixture figée (4859 caractères), même politique, même modèle épinglé à température 0, même budget dur de 16 appels. Les trois répliques convergent sur la décision arbitrale (`RESIDUEL` lié à la troncature de la cellule 8) quand elles la mesurent sur la fixture réparée ; elles diffèrent sur l'**idiome d'orchestration** — manager custom (SK), selection function + termination condition (MAF), boucle de désignation de l'appelant (ADK). C'est précisément la mesure du point 3 : la même charge, trois organes, trois natures de contrôle du tour.

## 4. Coût pour le dépôt (point 5)

Le point 5 demande trois choses : ce qui existe déjà, la dette de migration, et la valeur pédagogique. Mesures firsthand sur l'arbre à la tête de cette PR.

### 4.1 Ce qui existe déjà (inventaire mesuré)

| Moteur | Présence dans le dépôt | Mesure |
|---|---|---|
| **Semantic Kernel** | série pédagogique **bi-langage**, C# concentrée | `GenAI/SemanticKernel/` — 23 carnets (18 Python, 5 `.net-csharp`) selon `COURSE_CATALOG.generated.json` au head (mesuré, §5.4). La partie C# (5 carnets) inclut les 2 du préfixe `Semantic-fleet-*` ; la couche agents (`01` à `11`) est **Python seule** |
| **Google ADK** | série pédagogique dédiée (Python) + organe d'orchestration réutilisable | `ML/DataScienceWithAgents/07-Agent-Orchestration/` (14 carnets), plus `utils/adk_runtime.py` (`build_agent`, `run_agent_turn`) et `utils/adk_orchestrator.py` (contrat C4) — réutilisés tels quels par le pilote P3 |
| **Microsoft Agent Framework** | **aucune série pédagogique** — présent uniquement dans les pilotes d'évaluation de ce chantier | `grep` sur `agent-framework`/`Microsoft.Agents.AI` dans les `.ipynb` ne retourne que les pilotes ; MAF n'apparaît que dans `eval-pilots/` |
| **semantic-fleet** | sous-module épinglé | `MyIntelligenceAgency/semantic-fleet`, branche `stable-from-v0343` (`.gitmodules`) — infrastructure de flotte SK, hors série pédagogique |
| **pilotes d'évaluation** | pilotes autonomes + traces committées | `eval-pilots/` : SK (T1/T2/T4/P1), MAF (T5/T7/T8/P2), ADK (P3) — chacun exécutable firsthand, traces dans `traces/` |

Le constat structurel : **le dépôt enseigne déjà deux des trois moteurs** (SK en C# et Python, ADK en Python via Track2), et le troisième (MAF) n'a **pas** de série — il n'existe chez nous que comme objet de mesure. C'est le déséquilibre que le point 5 doit nommer.

### 4.2 Dette de migration

`VERIFIÉ` contre l'inventaire : la dette n'est **pas** symétrique.

- **Pas de migration à proprement parler** : SK et ADK ont chacun leur série et leurs idiomes, stables. Rien à porter d'un moteur à l'autre — les séries coexistent sans se concurrencer.
- **La dette réelle est un manque, pas un portage** : MAF n'a pas de série pédagogique. Le combler signifierait **écrire** une série (au moins un carnet couche agents : `HandoffBuilder`, `GroupChatBuilder`, `MagenticBuilder` — les trois idiomes déjà exécutés en T7/T8), pas migrer du contenu existant. Le coût est donc celui d'une **création**, bornée par ce que T5/T7/T8/P2 ont déjà mesuré et documenté (les pièges d'extraction, la termination condition, la ligne de versions `core 1.21.0` + `orchestrations 1.3.1` + connecteur résolu).
- **Dette d'environnement déclarée, et elle a grandi** : les trois moteurs exigent des venv **distincts** (SK 1.41.3 ; MAF core 1.21.0 + orchestrations 1.3.1 ; ADK 2.8.0 + litellm + pydantic-settings). Ce n'est pas une dette de code mais une dette de **reproductibilité** : un étudiant qui veut rejouer les trois pilotes doit monter trois environnements. Le README `eval-pilots/` documente chacun. **L'écart s'est creusé depuis** : au 2026-11-04, les versions courantes sont SK 1.46.0, MAF core 1.24.0 + orchestrations 1.4.1, ADK 2.13.0 (§5.1) — mais **l'écart n'est pas uniforme** : le pin SK a **190 jours**, celui d'ADK **70 jours**, et celui de MAF **27 jours** seulement (§5.1). Le pilote SK est donc la dette principale ; le pilote MAF est à trois versions mineures de la version courante.

### 4.3 Valeur pédagogique — enseigner les trois est la bonne réponse pour un cours

**Corrections apportées par Q17 (2026-11-04).** Trois affirmations de cette section étaient fausses ou ambiguës ; elles sont rectifiées ci-dessous, et la section a été réécrite pour ne rien laisser subsister. Les traces committées des trois pilotes sont la preuve.

Le point 3 a mesuré la chose décisive : **à charge identique, les trois moteurs convergent sur la décision finale, pas sur la structure de l'orchestration.** Ce qui est commun, c'est le `DECISION` rendu à l'arbitre (`RESIDUEL tour 1`) ; ce qui diffère, c'est **le nombre d'étapes et l'idiome de contrôle du tour**.

| Réplique | Trace | Étapes | Verdict du critique | Décision finale |
| --- | --- | --- | --- | --- |
| P1 (SK) | [`out-P1-sk-distillation-reexec.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P1-sk-distillation-reexec.txt) | **5** (producteur → critique → producteur → critique → arbitre) | `REVISION` | `RESIDUEL tour 1` |
| P2 (MAF) | [`out-P2-maf-distillation.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P2-maf-distillation.txt) | **5** (même séquence) | `REVISION` | `RESIDUEL tour 1` |
| P3 (ADK) | [`out-P3-adk-distillation.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-P3-adk-distillation.txt) | **3** (producteur → critique → arbitre) | `ACCEPTE` | `RESIDUEL tour 1` |

La version initiale de cette section affirmait « les trois moteurs produisent **la même structure et le même verdict** ». C'est faux sur la structure : SK et MAF convergent entre eux à 5 étapes, ADK s'arrête à 3 parce que son critique **accepte** là où les deux autres demandent une révision. La convergence réelle — et c'est elle qui est instructive — porte sur la **décision de l'arbitre**, qui est la même pour les trois. Le §3.4 décrivait déjà exactement cela ; cette section en divergeait.

Ce qui subsiste, et qui fait la valeur d'un enseignement multi-moteurs :

- **Le concept transférable est la politique d'orchestration** (producteur → critique → [révision] → arbitre), et elle se ré-encode dans trois idiomes : un manager à deux méthodes (SK), une selection function + une termination condition (MAF), une boucle de désignation de l'appelant (ADK). Un étudiant qui a vu les trois sait que l'orchestration est un **choix de conception**, pas une propriété du moteur — et la mesure le prouve : à charge identique, la même politique ne produit pas la même conversation.
- **La différence de nature est elle-même le cours** : SK et MAF exposent un **point d'extension orchestrateur** (le moteur appelle votre code pour savoir qui parle ensuite), ADK expose des **primitives** (`Runner`, `SessionService`) et laisse la politique à l'appelant. C'est une distinction architecturale réelle, mesurée, qu'on ne peut pas enseigner avec un seul moteur.
- **L'expertise multi-moteurs de la flotte est un atout, mais un atout à deux moteurs.** SK et ADK ont chacun leur série **écrite et exécutée** ; MAF n'a **aucune série pédagogique** (§4.1) — il n'existe chez nous que comme objet de mesure, dans les pilotes. Le coût marginal d'enseigner MAF est donc celui d'une **création**, pas celui d'une exploitation ; celui d'enseigner SK et ADK est quasi nul.

**Réserve d'honnêteté — une seule « couverture C# », pas deux.** Le §2.7 mesure la **couverture d'API C#** (quels types un moteur expose-t-il réellement en C# ?). Cette section parle de **série pédagogique C#** (qu'y a-t-il à enseigner ?). Les deux mots se ressemblent, ne mesurent pas la même chose, et les confondre avait produit une affirmation fausse. La réserve se formule donc ainsi :

- **couverture d'API C#** : SK expose le modèle historique seul ; MAF expose les cinq topologies, le checkpoint et l'OTel ; ADK n'a **aucune distribution C#** (mesuré : aucun paquet NuGet — §2.7 et §5.5) ;
- **série pédagogique C#** : le dépôt n'en compte qu'une, celle de SK — 5 carnets `.net-csharp` sur les 23 de `GenAI/SemanticKernel/` (mesuré, §5.4). 07-Agent-Orchestration est intégralement Python, et MAF n'a rien.

Un cours bi-langage ne peut donc pas être symétrique sur les trois moteurs ; c'est une borne à déclarer, pas à masquer. Le verdict par critère (quel moteur pour quel usage) reste au point 6, réservé à ai-01 + user.

## 5. Arbitrage 2026-11 — API courantes, trajectoire et besoins réels (Q17)

Cette section répond au grain posé par ai-01 sur [#14499](https://github.com/jsboige/CoursIA/issues/14499) le 2026-11-04 : **les API réelles aux versions courantes**, **l'évolution récente et la trajectoire**, **nos besoins moteur par moteur**. Elle porte aussi les corrections apportées au §4.

Comme le reste du document, chaque affirmation est `VÉRIFIÉ` (mesure firsthand, trace ou chemin cité) ou `RAPPORTÉ` (source primaire datée citée).

### 5.1 Versions courantes — mesurées le 2026-11-04

Sources des dates : API PyPI (`https://pypi.org/pypi/<paquet>/json`, date de publication **la plus ancienne** d'une version — la première publication, pas la dernière, pour ne pas dater une version par un re-push) et API NuGet *flat container* (`https://api.nuget.org/v3-flatcontainer/<id>/index.json` pour les versions, puis date lue dans l'index central ZIP du `.nupkg`). L'API `registration` paginée n'est pas utilisée : elle rend `items: null` pour `microsoft.semantickernel`, ce qui la rend muette là où elle devrait parler.

| Moteur | Paquet | Version courante | Publiée le | Pin des pilotes | Âge du pin |
| --- | --- | --- | --- | --- | --- |
| SK (Python) | `semantic-kernel` | **1.46.0** | 2026-10-28 | 1.41.3 (2026-04-28) | **190 j** |
| SK (.NET, surface stable) | `Microsoft.SemanticKernel.Agents.Core` | **1.81.0** | 2026-10-06 | 1.81.0 | 29 j |
| SK (.NET, surface preview) | `…Agents.Orchestration` / `…Agents.Magentic` | **1.81.0-preview** | 2026-10-06 | (non épinglé) | 29 j |
| MAF (Python, cœur) | `agent-framework-core` | **1.24.0** | 2026-10-30 | 1.21.0 (2026-10-08) | 27 j |
| MAF (Python, topologies) | `agent-framework-orchestrations` | **1.4.1** | 2026-10-30 | 1.3.1 (2026-10-08) | 27 j |
| MAF (Python, connecteur) | `agent-framework-openai` | **1.18.0** | 2026-10-30 | 1.16.0 (2026-10-08) | 27 j |
| MAF (.NET) | `Microsoft.Agents.AI` / `.Workflows` | **1.27.0** | 2026-10-30 | 1.24.0 (2026-10-07) | 28 j |
| ADK (Python) | `google-adk` | **2.13.0** | 2026-10-23 | 2.8.0 (2026-08-26) | 70 j |

`VÉRIFIÉ` — également mesuré : le pin `google-adk==2.8.0` n'est pas propre aux pilotes, il est aussi celui du track pédagogique [`07-Agent-Orchestration/requirements.txt`](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Agent-Orchestration/requirements.txt). **L'écart du pin pilote n'est donc pas un artefact d'évaluation : c'est l'état du cours lui-même**, et il porte sur 14 carnets.

**La lecture qu'il faut faire de ce tableau, et celle qu'il ne faut pas faire.** Un seul pin est franchement vieux : **SK Python, 190 jours**. MAF est à **27 jours** de sa version courante — les pilotes MAF tournent sur une ligne récente, et l'écart avec la version courante est de **trois versions mineures**, pas d'une génération. ADK est à 70 jours (cinq versions mineures derrière). Une formulation du type « les pilotes tournent sur des versions de six mois, trois mois et deux mois et demi » serait donc **fausse pour MAF**, qui est le cas le plus favorable de la série.

### 5.2 Cadence de publication depuis le 2026-09-01

`VÉRIFIÉ` — comptage sur les dates de publication mesurées ci-dessus, fenêtre de 64 jours.

| Paquet | Sorties dans la fenêtre | Rythme observé |
| --- | --- | --- |
| `agent-framework-core` | **8** | ~une par semaine |
| `agent-framework-openai` | 7 | ~une par semaine |
| `agent-framework-orchestrations` | 6 | ~une par semaine |
| `Microsoft.Agents.AI` et `.Workflows` | 7 chacun | ~une par semaine |
| `google-adk` | 7 | ~une par semaine |
| `semantic-kernel` (Python) | **2** | ~une par mois |
| `Microsoft.SemanticKernel.Agents.Core` (.NET) | **2** | 1.80.1 le 2026-09-03, 1.81.0 le 2026-10-06, **rien depuis** |

**Ce que la cadence dit, et qu'elle ne dit pas.** L'écart de rythme entre MAF/ADK (une sortie par semaine) et SK (une par mois) est **mesuré**. Il **s'explique** par la succession annoncée (§5.3) — mais cette explication est `RAPPORTÉ`, pas mesurée : la cadence est un fait, sa cause est une intention de l'éditeur. Deux observations complètent la mesure sans la surinterpréter :

- **SK Python a connu un trou de deux mois** : 1.44.1 le 2026-08-06, puis 1.45.0 le 2026-10-06. Sur les neuf versions depuis avril, c'est le seul intervalle de plus de cinq semaines.
- **SK .NET est silencieux depuis le 2026-10-06** (29 jours à la date de mesure), et la version qui plafonne est **exactement celle qu'épingle la sonde C#** : la surface C# de SK n'a pas bougé depuis la mesure T6 (§2.7).

### 5.3 Statut et trajectoire — sources primaires datées

`RAPPORTÉ` — sauf mention contraire, faits relevés sur source primaire datée, consultée le 2026-11-04.

**Semantic Kernel → Microsoft Agent Framework : une succession annoncée, pas une dépréciation silencieuse.**

- `VÉRIFIÉ` (source primaire datée) — [devblogs.microsoft.com/agent-framework/semantic-kernel-and-microsoft-agent-framework/](https://devblogs.microsoft.com/agent-framework/semantic-kernel-and-microsoft-agent-framework/), **7 octobre 2025** : « We will continue to support Semantic Kernel v1.x for the foreseeable future. We will continue to address critical bugs, security issues […] for a least one year after Microsoft Agent Framework leaves Preview and is Generally Available. » Le même billet pose : « Think of Microsoft Agent Framework as Semantic Kernel v2.0 (it's built by the same team!). »
- `VÉRIFIÉ` — [github.com/microsoft/semantic-kernel](https://github.com/microsoft/semantic-kernel) (README, page non datée, consultée le 2026-11-04) : « Semantic Kernel is now Microsoft Agent Framework! […] Microsoft Agent Framework (MAF) is the enterprise‑ready successor to Semantic Kernel. » Le README renvoie à un guide de migration.
- `VÉRIFIÉ` — [devblogs.microsoft.com/agent-framework/category/announcements/](https://devblogs.microsoft.com/agent-framework/category/announcements/), **3 avril 2026** : « Microsoft Agent Framework has reached version 1.0 for both .NET and Python. […] This is the production-ready release: stable APIs, and a commitment to long-term support. »

**Ce que ces trois sources donnent, une fois composées.** MAF est GA depuis le **2026-04-03** ; la promesse de support de SK v1.x court donc **au moins un an après cette date**, soit **jusqu'au 2027-04-03 au plus tôt**. C'est une borne, pas une date : le billet dit « for the foreseeable future » et ne publie pas de date de fin. La conséquence pratique est nette — **SK n'est pas mort, mais il ne recevra plus de fonctionnalités** : ce sont les correctifs de sécurité et les bugs critiques qui continuent, et les nouveautés vont à MAF. Pour un choix d'adoption à trois ans, c'est l'argument qui pèse.

`VÉRIFIÉ` — [github.com/microsoft/agent-framework](https://github.com/microsoft/agent-framework) (README, non daté) : « Full framework support for both Python and C#/.NET implementations with consistent APIs » ; Go est maintenu dans un dépôt séparé. `VÉRIFIÉ` — [releases MAF](https://github.com/microsoft/agent-framework/releases), **2026-10-30** : `python-1.24.0` et `dotnet-1.27.0` ; le README fournit un « Guide to migrate from Semantic Kernel ».

**Google ADK : deux lignes vivantes, et une documentation qui advertise plus de langages que ce que nous mesurons.**

- `VÉRIFIÉ` — [adk.dev](https://adk.dev/) (non daté, consulté le 2026-11-04) : « Available in Python, TypeScript, Go, Java, and Kotlin. » / « New in ADK 2.0! » (graph workflows), « ADK TypeScript 2.0 GA ».
- `VÉRIFIÉ` — [releases adk-python](https://github.com/google/adk-python/releases) : la ligne 2.x publie `v2.13.0` le **2026-10-23** ; la ligne 1.x a encore publié `v1.39.1` le **2026-08-27**, c'est-à-dire **après** le démarrage de la ligne 2.x (`v2.7.1`, 2026-08-17). Les deux lignes coexistent donc — mais **la ligne 1.x est silencieuse depuis le 2026-08-27** (69 jours), quand la ligne 2.x a continued à publier au rythme hebdomadaire. Le fait mesuré est une **coexistence qui s'est figée**, pas un parallélisme actif.
- `VÉRIFIÉ` — mêmes notes de version : `v2.13.0` déprécie la télémétrie legacy (« deprecate call_llm span and OpenTelemetry 1.36 GenAI semconv ») ; `v2.10.0` fait émettre un `DeprecationWarning` **à l'import** des modules audio legacy.
- `NON TROUVÉ` — aucune déclaration explicite de politique de maintenance 1.x vs 2.x (page d'accueil, README, notes de version : rien). Pas de roadmap publiée pour ADK non plus.

**Ce que « ADK n'est pas Python-only » ne veut pas dire.** La documentation annonce cinq langages, mais **notre mesure porte sur la distribution .NET** : aucun paquet NuGet ADK n'existe (§2.7, §5.5), et la seule assembly « Google » déployée par la restauration est `Google.Protobuf.dll`, dépendance transitive. La formulation exacte est donc : **ADK n'a pas de distribution C#** — pas « ADK est Python-only », qui serait faux au sens de la documentation.

**Non trouvé, et c'est un résultat.** Aucune feuille de route publiée pour SK ; aucun document de roadmap dédié dans le dépôt MAF. Ces absences sont des faits de mesure, pas des oublis : elles sont listées ici pour que le lecteur sache que la trajectoire **n'est documentée que par les billets de succession et les notes de version**.

### 5.4 Nos besoins — tirés du dépôt, pas imaginés

`VÉRIFIÉ` — inventaire mesuré sur l'arbre (`git grep`), pas sur une liste d'exigences imaginée.

| Besoin | Où il est déjà dans le dépôt | Contrainte réelle qu'il impose |
| --- | --- | --- |
| **Distillation** producteur → critique → arbitre | les trois pilotes `P1`/`P2`/`P3` + leurs traces committées | le tour doit être **contrôlable** par l'appelant, pas délégué au moteur |
| **Long run avec reprise** | le prover Lean (`…/SymbolicAI/Lean/agent_tests/prover/`) tourne sur `agent_framework` | le moteur doit savoir **reprendre** un run interrompu |
| **Traces** | `…/agent_tests/prover/baselines/traces/*.spans.jsonl` — des milliers de spans déjà produites | il faut un **format de trace** stable et lisible par un tiers |
| **Comptage de tokens** | `07-Agent-Orchestration/Day5-DS-Star/Lab12d-Token-Usage.ipynb` ; note du carnet : « Jusqu'à la trace 1, ADK produisait bien `usage_metadata` sur ses events » | il faut un compte **fiable et détaillé**, pas approximatif |
| **Série pédagogique bilingue C#/Python** | SK : 23 carnets (18 Python, 5 `.net-csharp`) ; ADK : 14 carnets Python ; MAF : **0** | il faut une **offre existante** ou l'accepter comme un coût de création |
| **Endpoint local** (vLLM, claudish) | `07-Agent-Orchestration/utils/adk_runtime.py` (`LiteLlm`, `api_base`) ; pilotes SK/MAF (`AsyncOpenAI(base_url=…)`, `base_url=…`) | le branchement doit passer par une **API compatible OpenAI** |

Deux découverts en mesurant cet inventaire, et qu'aucun tableau précédent ne portait :

- **MAF est déjà en production chez nous.** `…/agent_tests/prover/agents.py` importe `from agent_framework import Agent, ChatOptions`, et `…/agent_tests/requirements.txt` épingle `agent-framework-openai>=1.3.0,<2.0.0` — un **plancher, pas un pin exact**. Le prover est donc exposé à tout ce que MAF publie dans la branche 1.x, c'est-à-dire aux **huit versions** sorties depuis le 2026-09-01 (§5.2). C'est le besoin de *stabilité* le plus concret du dépôt, et il est mesuré.
- **Le pin `google-adk==2.8.0` du track pédagogique est lui aussi en retard de cinq versions mineures** (§5.1). Le lab « Token-Usage » documente d'ailleurs un comportement déjà observé : « Jusqu'à la trace 1, ADK produisait bien `usage_metadata` sur ses events ».

### 5.5 Couverture des besoins par moteur — mesurée aux versions courantes

`VÉRIFIÉ` — sonde [`eval-pilots/current_api_probe.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/current_api_probe.py) (Python) et rejeu de [`eval-pilots/csharp_coverage_probe.cs`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/csharp_coverage_probe.cs) (C#, surface stable) + [`eval-pilots/csharp_preview_surface_probe.cs`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/csharp_preview_surface_probe.cs) (C#, surface preview), **sans aucun appel LLM ni clé API**. Traces : [`out-Q17-sk-api-1.46.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-sk-api-1.46.0.txt), [`out-Q17-maf-api-1.24.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-maf-api-1.24.0.txt), [`out-Q17-adk-api-2.13.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-adk-api-2.13.0.txt), [`out-Q17-csharp-coverage-1.27.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-csharp-coverage-1.27.0.txt), [`out-Q17-csharp-preview-1.81.0.txt`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/traces/out-Q17-csharp-preview-1.81.0.txt).

**La sonde a une méthode, et ses limites sont mesurées aussi.** Chaque capacité porte un **contrôle positif** (ce qui doit être là) et un **contrôle négatif** ; s'y ajoute un **contrôle négatif inter-moteurs** (les deux autres moteurs doivent être **non importables** dans l'environnement mesuré), qui prouve que les verdicts « ABSENT » ne viennent pas d'un environnement contaminé. Deux faux négatifs ont été observés puis corrigés pendant la mesure, et ils sont de deux natures différentes :

- **un chemin mal cheminé** : interroger `semantic_kernel.agents.orchestration.X` rend « absent » parce que le paquet **ne re-exporte pas** ses classes — il faut passer par le sous-module (`…orchestration.group_chat.GroupChatOrchestration`). Le contrôle négatif de convention qui en découle est désormais dans la sonde ;
- **un granulaire inadapté** : le comptage de tokens est un **champ** (pydantic `model_fields`, dataclass `dataclasses.fields`, `__annotations__`, `dir()` en repli), pas un symbole — une recherche par symbole seul rendrait « absent » à tort.

| Besoin | SK 1.46.0 | MAF 1.24.0 (+ orch 1.4.1) | ADK 2.13.0 |
| --- | --- | --- | --- |
| **Cinq topologies** | **présent** (5 sous-modules, ré-exportées depuis `semantic_kernel.agents`) | **présent** (`SequentialBuilder`, `ConcurrentBuilder`, `GroupChatBuilder`, `MagenticBuilder`, `HandoffBuilder`) | primitives (`SequentialAgent`, `LoopAgent`, `ParallelAgent`), pas de topologie équivalente |
| **Reprise d'un long run** | **ABSENT** — aucun symbole `checkpoint`/`resume`/`restore`/`snapshot` dans tout le paquet | **présent** — `WorkflowCheckpoint`, `CheckpointStorage`, `FileCheckpointStorage`, `InMemoryCheckpointStorage`, `CheckpointID`, `AgentExecutorCheckpointState` | **présent** — `ResumabilityConfig` (`google.adk.agents.invocation_context`), sessions `InMemory`/`VertexAi`/`PerAgentDatabase` |
| **Traces / observabilité** | `TracerProvider`, `get_tracer_provider` (`agents.runtime.core.telemetry.tracing`) | `ChatTelemetryLayer`, `AgentTelemetryLayer`, `get_tracer`, `workflow_tracer` | callbacks `Before/AfterModel`, `AfterTool`, `OnModelError` + télémétrie |
| **Comptage de tokens** | `CompletionUsage` existe et est **posé dans `metadata["usage"]`** par le service (`open_ai_chat_completion_base.py:222`) — donc **pas un champ du message** (`ChatMessageContent` : `CHAMPS ABSENT`) et **pas d'agrégateur** | `UsageDetails` (`TypedDict` : entrée, sortie, total, cache création/lecture, raisonnement) + `Content.from_usage(...)` + `agent_framework.add_usage_details(...)` — **agrégation de première classe** | `Event.usage_metadata` → `GenerateContentResponseUsageMetadata` : total, prompt, candidats, cache, **raisonnement**, tools — **le plus détaillé des trois** |
| **Endpoint local** | `base_url` **n'est pas un paramètre** de `OpenAIChatCompletion.__init__` : il faut passer `async_client=AsyncOpenAI(base_url=…)` (forme du pilote) — construction vérifiée | `base_url` **accepté directement** par `OpenAIChatCompletionClient` — construction vérifiée | par `LiteLlm(api_base=…)` — l'organe du dépôt (`utils/adk_runtime.py`) |
| **Avertissements de dépréciation à l'import** | **0** | 0 (`ExperimentalWarning` hors dépréciation : `[FIDES] ContentVariableStore`) | **0** |

**Trois lectures que la mesure autorise, et qu'elle n'autorise pas à élargir.**

1. **L'API publique de SK n'a pas bougé.** Les cinq topologies, `AgentGroupChat`, `ProcessBuilder` (déplacé en module de premier niveau, `semantic_kernel.processes`) sont tous là en 1.46.0, et **aucun `DeprecationWarning` n'est émis à l'import**. Un code écrit contre 1.41.3 n'a pas à être réécrit — mais il ne recevra plus de fonctionnalité (§5.3).
2. **Sur la reprise, SK n'offre rien** — ni en Python (aucun symbole), ni en C# (zéro type sur les six fragments cherchés : `Checkpoint`, `OpenTelemetry`, `Telemetry`, `Workflow`, `Resume`, `Persistence`), y compris dans sa surface preview (§5.6). MAF expose sept types de checkpoint et trois extensions OpenTelemetry côté C#, et la même chose en Python ; ADK expose `ResumabilityConfig`. **Si le prover Lean doit pouvoir reprendre un long run, SK est hors sujet.**
3. **Le branchement local n'a pas la même facilité partout.** MAF accepte `base_url` directement ; SK l'a **retiré** de la signature du service (le passage par `async_client` reste la forme correcte, vérifiée par construction) ; ADK passe par un adaptateur tiers (LiteLLM), ce qui ajoute une dépendance de plus au track.

### 5.6 La surface C# — stable, preview, et ce que la mesure overturnait

`VÉRIFIÉ` — la sonde C# de T6 mesure la **surface stable** (`Microsoft.SemanticKernel.Agents.Core` 1.81.0). Le §2.7 en conclut que « les cinq objets d'orchestration **n'existent pas** dans SK C# 1.81.0 ». **Cette formulation est trop forte, et la mesure Q17 l'a renversée.**

Contrôle de la source : l'archive `main` du dépôt SK contient bien `dotnet/src/Agents/Orchestration/` (avec `ConcurrentOrchestration.cs`, `GroupChatOrchestration.cs`, `HandoffOrchestration.cs`, `SequentialOrchestration.cs`) et `dotnet/src/Agents/Magentic/` (`MagenticManager.cs`, `MagenticAgentActor.cs`) — et ces deux répertoires sont **des projets .csproj distincts** (`Agents.Orchestration.csproj`, `Agents.Magentic.csproj`). Autrement dit, la couche d'orchestration C# de SK n'est pas dans le paquet `Agents.Core` : elle est **dans deux paquets à part**.

Contrôle de la distribution : sur NuGet, `microsoft.semantickernel.agents.orchestration` et `microsoft.semantickernel.agents.magentic` existent, et **aucune de leurs 32 versions n'est stable** — la liste complète est `1.51.0-preview` … `1.81.0-preview`. La dernière, `1.81.0-preview`, a été publiée le **2026-10-06**, le même jour que la 1.81.0 stable.

Mesure directe : la sonde [`csharp_preview_surface_probe.cs`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/csharp_preview_surface_probe.cs) restaure ces deux paquets `-preview` **en plus** du paquet stable, et mesure la surface deployée :

| Mesure | Résultat |
| --- | --- |
| Assemblages deployés (préfixe `Microsoft.SemanticKernel.Agents`) | `Abstractions` 27 · `Core` 17 · `Magentic` 11 · `Orchestration` 29 · `Runtime.Abstractions` 15 · `Runtime.Core` 10 |
| Les cinq topologies | **présentes** — `ConcurrentOrchestration`, `SequentialOrchestration`, `GroupChatOrchestration`, `HandoffOrchestration` dans `Agents.Orchestration.dll`, `MagenticOrchestration` dans `Agents.Magentic.dll` |
| Contrôle négatif de provenance | les cinq sont **absentes** de `Agents.Core.dll` (l'assemblage stable) — donc bien fournies par la couche preview |
| Reprise / telemetry / workflow (six fragments) | **AUCUN** type, dans la surface preview comme dans la stable |

**La correction, en une phrase.** L'orchestration C# de SK **existe et est publiée**, mais **uniquement en version `-preview`** — il n'y a jamais eu de version stable de `Microsoft.SemanticKernel.Agents.Orchestration`. L'absence constatée par T6 n'était donc pas une absence de capacité : c'était une absence de **version stable**. La formulation juste est : « SK C# n'expose pas l'orchestration **en version stable** ; il l'expose en preview, dans des paquets distincts de la couche agents stable. »

**Ce que cela ne change pas.** Les topologies SK C# restent, dans la surface stable, absentes ; le checkpoint et l'OTel SK C# restent absents **des deux surfaces** (preview comprise). Et MAF C# les expose **en version stable**. La conclusion du §2.7 — « SK est Python d'abord sur la couche agents, MAF est C# d'abord » — **tient**, avec une nuance qu'elle ne portait pas : l'écart SK/MAF côté C# n'est pas « une capacité de plus chez MAF », c'est « une capacité **stable** de plus chez MAF ».

### 5.7 Limites de la mesure

Ce que cette section **ne** mesure pas, et qu'il faut savoir avant de s'en servir :

- **Aucun appel LLM n'a été fait.** Les sondes mesurent la **surface d'API** et la **forme de l'appel** (construction réelle d'un client, sans requête). Elles ne disent rien du comportement à l'exécution — la preuve comportementale reste celle des traces P1/P2/P3, qui datent des versions de septembre.
- **Les pilotes n'ont pas été rejoués aux versions courantes.** Le poste n'a pas de clé de modèle (`gpt-4o-mini` est épinglé dans les pilotes) ; le rejeu exigerait de changer le modèle, ce qui romprait la comparabilité du protocole. **L'écart entre « l'API existe » et « le pilote rejoué » n'est donc pas mesuré** — il est signalé, pas comblé. C'est le point le plus faible de cette section, et il est assumé comme tel.
- **Une dépendance optionnelle peut faire tomber un import.** `semantic_kernel.agents.autogen` (nouveau en 1.46.0) exige le paquet `autogen` ; `semantic_kernel.agents.runtime` exige `google-genai` et `protobuf`. Un environnement minimal échoue à l'import sur une dépendance absente — ce qui a d'abord produit un **faux négatif** de sonde, corrigé depuis. C'est un fait d'installation, pas une absence d'API, et il est reproduit dans la trace.
- **Les chiffres de types publics sont des planchers**, pas des comptes : l'union dédoublonnée sur le nom court fusionne des homonymes de namespaces différents et dépend de ce que l'hôte a restauré (§2.7).
- **Le point 6 reste réservé** : le verdict par critère — quel moteur pour quel usage — appartient à ai-01 et à l'arbitrage user. Cette section **documente**, elle ne tranche pas.
