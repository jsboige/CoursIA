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

Le pilote T7 (MAF couche agents) est mesuré sur une **ligne de versions alignée**
différente de T5 : `agent-framework-core` 1.21.0 + `agent-framework-orchestrations`
1.3.1, sous le venv projet (core 1.15.0 + orchestrations 1.1.1, l'état antérieur
de l'env, est incompatible sur le protocole request-info du handoff) :

```bash
<venv>/Scripts/python maf_agents_handoff_pilot.py   # T7 — handoff, budget dur 40 appels
```

Le pilote T8 (MAF couche agents — GroupChat et Magentic) est mesuré sur une
**ligne de versions alignée** différente de T5 : `agent-framework-core` 1.21.0 +
`agent-framework-orchestrations` 1.3.1, sous le venv projet :

```bash
<venv>/Scripts/python maf_groupchat_magentic_pilot.py   # T8 — GroupChat + Magentic, budget dur 60 appels
```

Le pilote P1 (issue #14499, point 3 — réplique SK du **pilote identique** sur une
vraie charge) utilise la même ligne SK que T2/T4. La charge n'est pas un scénario
écrit pour l'occasion mais la **fixture figée** `distill_charge_fixture.md` :
cellules 0..8 du carnet `01-SemanticKernel-Intro.ipynb`, figées à une tête — les
répliques P2 (MAF) et P3 (ADK) distilleront ce même fichier, byte-stable :

```bash
py -3.11 sk_distillation_pilot.py   # P1 — GroupChat à manager custom, budget dur 16 appels
```

Le pilote P2 (réplique **MAF** du même pilote identique) utilise le venv MAF de
T7/T8 (`agent-framework-core 1.21.0` + `orchestrations 1.3.1` ; connecteur
`agent-framework-openai` résolu par pip, 1.16.0 mesuré — la 1.21.0 n'existe pas
sur PyPI). Même fixture figée, mêmes instructions, même modèle épinglé, même
budget dur de 16 appels ; la boucle est scellée par une `termination_condition`
posée sur le builder :

```bash
<venv-maf>/Scripts/python maf_distillation_pilot.py   # P2 — GroupChatBuilder + selection function, budget dur 16 appels
```

Le pilote P3 (réplique **ADK** du même pilote identique) utilise un venv dédié
portant `google-adk 2.8.0` + `openai` + `litellm` + `pydantic-settings` (le pilote
réutilise l'organe du Track2 — `utils/adk_runtime.build_agent`, `config/providers`
— qui importe ces dépendances). Même fixture figée, mêmes instructions, même
modèle épinglé, même budget dur de 16 appels. Il n'y a **pas** de manager de
group-chat en ADK : la politique de tour vit dans une boucle Python de
**désignation explicite** sur une `InMemorySessionService` partagée ; chaque rôle
est invoqué avec un prompt de désignation (passer `prompt=None` laisserait ADK
router par handoff implicite et produirait des `Event from an unknown agent`) :

```bash
<venv-adk>/Scripts/python adk_distillation_pilot.py   # P3 — boucle de désignation explicite, budget dur 16 appels
```

Le pilote T3 (Google ADK) vit dans la série Track2 :

```bash
py -3.11 ../../../ML/DataScienceWithAgents/07-Agent-Orchestration/eval-pilots/adk_handoff_pilot.py
```

## Sonde C# (T6)

**App mono-fichier .NET 10** : aucun `.csproj` n'est livré, donc aucun impact sur
`dotnet/MyIA.CoursIA.sln`, `dotnet/MyIA.AI.Shared/MyIA.AI.Shared.sln` ni sur les workflows .NET (tous filtrés par
chemin). Les versions des paquets sont épinglées par les directives `#:package` en
tête du fichier :

```text
#:package Microsoft.SemanticKernel.Agents.Core@1.81.0
#:package Microsoft.Agents.AI@1.27.0
#:package Microsoft.Agents.AI.Workflows@1.27.0
```

```bash
dotnet run csharp_coverage_probe.cs   # .NET 10 ; réseau requis pour la restauration
```

Les sondes C# (T6 ci-dessus, T9 plus bas) exigent un **SDK** .NET (l'app mono-fichier compile avant de
tourner). Si le `dotnet` du `PATH` ne résout qu'un **runtime** — le cas d'un
`PATH` qui pointe vers une installation runtime-only —, `dotnet run` échoue sur
« No .NET SDKs were found » : il faut alors appeler l'exécutable d'un SDK
installé par l'utilisateur (par exemple `~/.dotnet/dotnet.exe` sous un SDK
10.0.x), qui résout les deux.

Exit 0 = contrôles négatif et positif passés. La sonde publie le détail **par
assemblage** en plus de l'union dédoublonnée — l'union sur nom court est un
**plancher** de types, pas un compte (deux types homonymes de namespaces distincts y
fusionnent), et elle dépend de ce que le projet hôte a restauré.

> **Versions mises à jour au 2026-11-04 (Q17).** Les pins MAF passent de 1.24.0 à
> **1.27.0** (version courante, publiée le 2026-10-30) : le delta de surface est donc
> mesuré, et non supposé. Le pin SK reste **1.81.0** — rien de neuf n'a été publié
> côté .NET SK depuis le 2026-10-06.

## Sonde C# — surface preview (T9)

`Microsoft.SemanticKernel.Agents.Orchestration` et `…Agents.Magentic` **n'ont jamais
eu de version stable** : sur NuGet, leurs 32 versions sont toutes `-preview`, la
dernière étant `1.81.0-preview` (2026-10-06). La sonde T6 mesure la surface
**stable** et rend donc « absent » pour les cinq topologies C# de SK.

La sonde T9 mesure cette surface **preview**, dans un processus **distinct** — la
restauration de paquets supplémentaires changerait les assemblages déployés, donc
l'union que T6 publie et que le §2.7 du document compare.

```text
#:package Microsoft.SemanticKernel.Agents.Core@1.81.0
#:package Microsoft.SemanticKernel.Agents.Orchestration@1.81.0-preview
#:package Microsoft.SemanticKernel.Agents.Magentic@1.81.0-preview
```

```bash
dotnet run csharp_preview_surface_probe.cs   # .NET 10 ; réseau requis
```

Elle porte un **contrôle négatif de provenance** : les cinq topologies doivent
être présentes, et **absentes** de l'assemblage stable — sans quoi un « présent »
ne dirait pas d'où il vient, et la distinction stable/preview est justement le
point mesuré. Résultat (2026-11-04) : les cinq topologies **sont** présentes
(`…Agents.Orchestration.dll` pour quatre, `…Agents.Magentic.dll` pour
`MagenticOrchestration`), et la reprise (`Checkpoint`), l'OTel (`OpenTelemetry`,
`Telemetry`) et la surface `Workflow` restent **AUCUN** type — en preview comme en
stable.

## Sonde d'API courante (Q17)

Sonde **sans appel LLM ni clé API** : elle mesure la **surface d'API** de chaque
moteur aux versions courantes, et la **forme de l'appel** (construction réelle d'un
client, sans requête). Chaque capacité porte un contrôle positif et un contrôle
négatif ; s'y ajoute un **contrôle négatif inter-moteurs** (les deux autres moteurs
doivent être non importables dans l'environnement mesuré), qui prouve qu'un
verdict « ABSENT » ne vient pas d'un environnement contaminé.

```bash
python current_api_probe.py --engine sk    # semantic-kernel 1.46.0
python current_api_probe.py --engine maf   # agent-framework-core 1.24.0 + orchestrations 1.4.1
python current_api_probe.py --engine adk   # google-adk 2.13.0
```

Le comptage de tokens y est mesuré au niveau du **champ** (pydantic
`model_fields`, dataclass `dataclasses.fields`, `__annotations__`, `dir()` en repli),
pas du symbole : une recherche par symbole seul rendrait « absent » à tort.

Ce que la sonde **ne** mesure pas : le comportement à l'exécution. Les pilotes
P1/P2/P3 restent la preuve comportementale, et ils datent de leurs versions de
septembre.

## Traces committées

`traces/out-*.txt` sont les **stdout** des pilotes, telles quelles. Elles sont
committées pour qu'une affirmation `VÉRIFIÉ` du doc soit une propriété du dépôt et
non du poste de l'auteur.

Le **stderr n'est pas committé** : les avertissements Python y impriment des chemins
absolus (`C:\Users\…`, `…\site-packages\…`), et un fichier committé ne porte pas de
chemin machine. Cette séparation est faite **à la capture** (`> out-….txt 2> /dev/null`),
jamais par retrait de lignes après coup : une trace retouchée n'est plus une trace.
Le code de sortie de chaque pilote est reporté dans le doc ; un échec reste donc
visible sans le stderr.

Corollaire de cette règle : **l'en-tête d'une trace est écrit par la sonde
elle-même**, jamais ajouté à la main après la capture. Les quatre sondes Q17
(`current_api_probe.py`, `csharp_coverage_probe.cs`, `csharp_preview_surface_probe.cs`
et les pilotes antérieurs) impriment donc leur propre en-tête — moteur, date
**calculée au runtime**, versions épinglées — sur leur stdout. Une date figée
dans la source mentirait sur la datation d'une re-exécution ; un en-tête collé à
la main rendrait la trace « retouchée », donc invérifiable.

Les sondes C# neutralisent en outre l'avertissement d'analyseur **IL2026**
(`Assembly.LoadFrom` / `GetExportedTypes` marqués `RequiresUnreferencedCode`) :
il est sans objet — la sonde n'est ni trimée ni publiée, elle énumère les
assemblages déployés — et il porterait le **chemin local du fichier source**
dans la trace.

Une trace committée **n'est pas** un contrôle : le contrôle est le pilote, rejouable
par la commande ci-dessus. La trace est le témoin daté de ce qu'il a produit.

Deuxième piège de capture, mesuré sur P3 : le bandeau d'échec de `litellm` part sur
**stdout**, et il est **coloré**. Une trace qui le porte laisse des séquences ANSI dans
le fichier committé, et `gh pr diff` refuse alors de rendre le diff de la PR — le garde
de périmètre n'a plus rien à mesurer (`rc=2`, verdict `UNKNOWN`), donc un rouge qui
n'accuse aucun défaut de périmètre. Le pilote neutralise ces séquences **dans son
propre stdout** (`_StdoutSansAnsi`), la trace restant son stdout et non une version
filtrée à la capture ; et la capture force l'UTF-8, sans quoi les accents sortent dans
la page de code de la console :

```bash
PYTHONIOENCODING=utf-8 <venv-adk>/Scripts/python adk_distillation_pilot.py \
    > traces/out-P3-adk-distillation.txt 2> /dev/null
```
