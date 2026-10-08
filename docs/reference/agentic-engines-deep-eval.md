# Évaluation approfondie des moteurs agentiques — ADK vs Semantic Kernel vs MS Agent Framework

> Livrable de l'issue [#14499](https://github.com/jsboige/CoursIA/issues/14499) (mandat user 2026-09-23 : « Il faut analyser les 3 en profondeur »).
> Protocole commun : 6 points (état de l'art, modes d'orchestration **exécutés**, déterminisme, couverture C#/Python, coût pour le dépôt, verdict par critère).
> Ce document porte les mesures et les tableaux — pas de rapport de cycle. Chaque affirmation est `VERIFIÉ` (mesure firsthand, commit/chemin cité) ou `RAPPORTE` (source primaire citée).

## État du document

| Tranche | Point du protocole | État |
|---|---|---|
| T1 (cette PR) | pt 2 — SK, mode événementiel (Process Framework) exécuté | livré |
| — | pt 2 — SK, autres modes (séquentiel, concurrent, handoff, group chat, Magentic) | à venir |
| — | pt 2 — ADK (agents, workflows, séquentiel) | à venir |
| — | pt 2 — MS Agent Framework (agents, graphe) | à venir |
| — | pt 1 état de l'art | livré hors repo : note datée du 2026-10-05 sur [#19380](https://github.com/jsboige/CoursIA/issues/19380) ; mémo inventaire local du 2026-10-07 (po-2024:CoursIA-2) sur [#14499](https://github.com/jsboige/CoursIA/issues/14499) |
| — | pts 3-6 (déterminisme, couverture langages, coût, verdict) | à venir |

## 2. Modes d'orchestration — exemples exécutés

### 2.1 Semantic Kernel — couverture réelle du dépôt (mesuré)

`VERIFIÉ` (lecture intégrale des 8 cellules de code de [`06-SemanticKernel-ProcessFramework.ipynb`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb), kernel python3, twin exécuté 6/6) :

- la série démontre des pipelines **séquentiels manuels** (`run_content_pipeline`, `run_iterative_pipeline` : boucle de révision explicite en Python) ;
- l'API **événementielle** du Process Framework (`ProcessBuilder` + `on_event`/`send_event_to`) n'apparaît **que en prose** (sections descriptives et schéma d'architecture) — **aucune cellule ne l'exécute** ;
- le point user « orchestration événementielle sous-exploitée » ([#14499](https://github.com/jsboige/CoursIA/issues/14499), contre-point 2) est donc **confirmé par la mesure** : le mode est documenté mais jamais exécuté dans le corpus.

Conséquence pour l'évaluation : le pilote événementiel ci-dessous est le **premier** exemple exécuté de ce mode dans le dépôt — il ne reduplique rien.

### 2.2 Pilote SK Process Framework (événementiel, déterministe)

`VERIFIÉ` — pilote [`eval-pilots/sk_process_pilot.py`](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/eval-pilots/sk_process_pilot.py) (151 lignes), exécuté sous `py -3.11` / semantic_kernel **1.41.3** (le kernel de la série), **sans LLM** : chaque étape est une transformation déterministe (intake → enrich → review → publish|reject, règle de seuil ≥ 3 mots). Reproduction firsthand depuis l'emplacement livré : exit 0.

Trace d'exécution (deux entrées, deux embranchements événementiels) :

```
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

### 2.3 À venir (SK)

Modes restants à exécuter : séquentiel (déjà démontré manuellement dans la série — le pilote comparatif consignera la version agentique), concurrent, handoff, group chat, Magentic, et le même couplage déterministe. L'emplacement `eval-pilots/` les accueillera un par un.
