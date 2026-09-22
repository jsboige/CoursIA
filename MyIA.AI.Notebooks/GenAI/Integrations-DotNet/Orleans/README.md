# Orleans — acteurs stateful pour les workloads IA

Axe **Orleans** de la série *The Unexpected AI Stack: C#/.NET* ([EPIC #10473](https://github.com/jsboige/CoursIA/issues/10473)) — dernier axe de la Part 1 non encore distillé. Le registre des axes de la série vit dans [`../Aspire/distilled-axes-registry.md`](../Aspire/distilled-axes-registry.md).

## Contenu

| Notebook | Sujet |
|---|---|
| [01-Orleans-Grains-Agents.ipynb](01-Orleans-Grains-Agents.ipynb) | Grains acteurs : sessions d'agents isolées par clé, compteurs de tokens partagés sans verrou, concurrence turn-based, routage grain-à-grain |
| [02-Orleans-Aspire-CoHost.ipynb](02-Orleans-Aspire-CoHost.ipynb) | Le silo orchestré par un AppHost Aspire (`Aspire.Hosting.Orleans` + CLI `aspire run`), identités générées `IGrainWithGuidKey`, reprise par identité, client process séparé |

Le dossier `OrleansAgentLab/` contient le projet .NET 10 réel exécuté par le notebook 01 (silo co-hosté en mémoire, `Microsoft.Orleans.Server` 10.3.1). Les scénarios sont pilotés par argument : `demo`, `ex1`, `ex2`, `ex3` — les trois derniers consomment les méthodes à compléter de `Grains.cs`.

Le dossier `OrleansAspireLab/` contient l'application distribuée du notebook 02 : `apphost.cs` (AppHost Aspire file-based) orchestre `Silo/` (projet silo, gateway 30000), `ClientDriver/` (client process séparé) et `Grains/` (contrat partagé). Mêmes scénarios par argument (`demo`, `ex1`–`ex3`, `resume <guid>`) ; la CLI Aspire (`dotnet tool install -g aspire.cli`) est requise.

## Prérequis

- .NET SDK 10 (`dotnet --version` >= 10.0)
- kernel Jupyter `.net-csharp` (extension .NET Interactive)
