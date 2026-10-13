# Orleans — acteurs stateful pour les workloads IA

Axe **Orleans** de la série *The Unexpected AI Stack: C#/.NET* ([EPIC #10473](https://github.com/jsboige/CoursIA/issues/10473)) — dernier axe de la Part 1 non encore distillé. Le registre des axes de la série vit dans [`../Aspire/distilled-axes-registry.md`](../Aspire/distilled-axes-registry.md).

## Contenu

| Notebook | Sujet |
|---|---|
| [01-Orleans-Grains-Agents.ipynb](01-Orleans-Grains-Agents.ipynb) | Grains acteurs : sessions d'agents isolées par clé, compteurs de tokens partagés sans verrou, concurrence turn-based, routage grain-à-grain |
| [02-Orleans-Aspire-CoHost.ipynb](02-Orleans-Aspire-CoHost.ipynb) | Le silo orchestré par un AppHost Aspire (`Aspire.Hosting.Orleans` + CLI `aspire run`), identités générées `IGrainWithGuidKey`, reprise par identité, client process séparé |
| [03-Orleans-Persistance-Redis.ipynb](03-Orleans-Persistance-Redis.ipynb) | L'état des grains dans un Redis réel (`IPersistentState<T>` + `Microsoft.Orleans.Persistence.Redis`) : survie au redémarrage du process contre perte avec le stockage mémoire, document stocké lu avec `redis-cli`, concurrence optimiste par ETag entre deux silos |
| [04-Orleans-Aspire-Cluster-Redis.ipynb](04-Orleans-Aspire-Cluster-Redis.ipynb) | Un cluster de deux silos (`WithReplicas(2)`) dont l'appartenance et l'état sont déclarés par l'AppHost (`WithClustering`, `WithGrainStorage`) : silo sans code d'infrastructure, activation unique quelle que soit la réplique appelée, reprise d'une session après arrêt propre puis mort brutale du silo qui l'héberge, et ce que le redémarrage complet perd |

Le dossier `OrleansAgentLab/` contient le projet .NET 10 réel exécuté par le notebook 01 (silo co-hosté en mémoire, `Microsoft.Orleans.Server` 10.3.1). Les scénarios sont pilotés par argument : `demo`, `ex1`, `ex2`, `ex3` — les trois derniers consomment les méthodes à compléter de `Grains.cs`.

Le dossier `OrleansAspireLab/` contient l'application distribuée du notebook 02 : `apphost.cs` (AppHost Aspire file-based) orchestre `Silo/` (projet silo, gateway 30000), `ClientDriver/` (client process séparé) et `Grains/` (contrat partagé). Mêmes scénarios par argument (`demo`, `ex1`–`ex3`, `resume <guid>`) ; la CLI Aspire (`dotnet tool install -g aspire.cli`) est requise.

Le dossier `OrleansPersistenceLab/` contient le projet du notebook 03 : un grain `PersistentSessionGrain` dont l'état est un `IPersistentState<SessionState>`, et un silo qui choisit son fournisseur au démarrage (Redis ou mémoire). Chaque scénario est un process distinct (`write`, `read`, `conflict`, `ex1`–`ex3`), pour que la survie de l'état se mesure d'un process à l'autre. Redis tourne dans un conteneur `redis:7-alpine` que le notebook démarre et arrête ; l'adresse passe par la variable `ORLEANS_REDIS`. Les silos du lab écoutent sur 11131/30031 et 11132/30032, pour ne pas entrer en collision avec les labs 01 et 02.

Le dossier `OrleansClusterLab/` contient l'application distribuée du notebook 04 : `apphost.cs` déclare un Redis, un service Orleans qui s'en sert pour l'appartenance au cluster et pour le stockage `sessions`, et deux répliques de `Silo/` derrière le port HTTP 5310. Le silo n'appelle que `UseOrleans()` : fournisseurs, identifiants et ports arrivent par la configuration qu'Aspire injecte. Son API HTTP (`/cluster`, `/redis/members`, `/session/{id}/turn`...) sert d'instrument de mesure au notebook. Les exercices 1 et 2-3 se complètent dans `apphost.cs` et `Silo/Grains.cs`.

## Prérequis

- .NET SDK 10 (`dotnet --version` >= 10.0)
- kernel Jupyter `.net-csharp` (extension .NET Interactive)
- Docker, pour le Redis des notebooks 03 et 04
- CLI Aspire (`aspire`, outil .NET global), pour les notebooks 02 et 04
