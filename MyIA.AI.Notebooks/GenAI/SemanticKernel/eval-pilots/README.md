# eval-pilots — pilotes d'évaluation des moteurs agentiques

Pilotes du chantier #14499 (« ce que chaque moteur offre *réellement* »). Chaque
pilote est un fichier autonome, exécuté firsthand ; la mesure et son analyse sont
publiées dans
[`docs/reference/agentic-engines-deep-eval.md`](../../../../docs/reference/agentic-engines-deep-eval.md).

## Modèle épinglé, et pourquoi il ne se choisit pas à l'exécution

Les pilotes qui appellent un LLM utilisent **`gpt-4o-mini`, température 0**, déclaré
en **constante** (`MODEL`, `MODEL_ID`) — jamais choisi par une sonde qui bascule.

Raison : le protocole déterministe exige `temperature=0`, que la famille *reasoning*
(`gpt-5-mini`) refuse par un `400 unsupported_value`. Un repli automatique ferait
donc dépendre le **modèle effectif** d'un comportement d'API, et la comparaison
entre pilotes (« même modèle, même réglage, même scénario ») se casserait **sans
aucun signal** le jour où la sonde passerait. La sonde reste présente — elle atteste
que le service répond sur ce modèle — mais elle **échoue fort (exit 2)** au lieu de
basculer.

## Exécution des pilotes Python

Interpréteur `py -3.11` (semantic_kernel 1.41.3). La clé OpenAI est lue dans
`.secrets/master.env` — jamais affichée.

```bash
py -3.11 sk_process_pilot.py               # T1 — sans LLM, re-dérivable depuis sa source
py -3.11 sk_agents_handoff_pilot.py        # T2 — handoff, budget dur 10 appels
py -3.11 sk_orchestration_modes_pilot.py   # T4 — les 5 modes d'orchestration
py -3.11 maf_workflow_pilot.py             # T5 — graphe typé MAF
```

Le pilote T3 (Google ADK) vit dans la série Track2 :

```bash
py -3.11 ../../../ML/DataScienceWithAgents/Track2-GoogleADK/eval-pilots/adk_handoff_pilot.py
```

## Sonde C# (T6)

**App mono-fichier .NET 10** : aucun `.csproj` n'est livré, donc aucun impact sur
`MyIA.CoursIA.sln`, `MyIA.AI.Shared.sln` ni sur les workflows .NET (tous filtrés par
chemin). Les versions des paquets sont épinglées par les directives `#:package` en
tête du fichier :

```text
#:package Microsoft.SemanticKernel.Agents.Core@1.81.0
#:package Microsoft.Agents.AI@1.24.0
#:package Microsoft.Agents.AI.Workflows@1.24.0
```

```bash
dotnet run csharp_coverage_probe.cs   # .NET 10 ; réseau requis pour la restauration
```

Exit 0 = contrôles négatif et positif passés. La sonde publie le détail **par
assemblage** en plus de l'union dédoublonnée — l'union sur nom court est un
**plancher** de types, pas un compte (deux types homonymes de namespaces distincts y
fusionnent), et elle dépend de ce que le projet hôte a restauré.

## Traces committées

`traces/out-T*.txt` sont les **stdout** des pilotes, telles quelles. Elles sont
committées pour qu'une affirmation `VÉRIFIÉ` du doc soit une propriété du dépôt et
non du poste de l'auteur.

Le **stderr n'est pas committé** : les avertissements Python y impriment des chemins
absolus (`C:\Users\…`, `…\site-packages\…`), et un fichier committé ne porte pas de
chemin machine. Cette séparation est faite **à la capture** (`> out-….txt 2> /dev/null`),
jamais par retrait de lignes après coup : une trace retouchée n'est plus une trace.
Le code de sortie de chaque pilote est reporté dans le doc ; un échec reste donc
visible sans le stderr.

Une trace committée **n'est pas** un contrôle : le contrôle est le pilote, rejouable
par la commande ci-dessus. La trace est le témoin daté de ce qu'il a produit.
