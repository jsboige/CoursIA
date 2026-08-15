# aspire-otel — backend OTLP Aspire pour le notebook SK-4

Ce dossier contient un **AppHost Aspire minimal** qui sert de **backend
d'observabilité OTLP** au notebook Python
[`../04-SemanticKernel-Filters-Observability.ipynb`](../04-SemanticKernel-Filters-Observability.ipynb)
(section 6, « OpenTelemetry »).

## Rôle

L'AppHost n'orchestre **aucune** ressource de la pile GenAI. Son unique
fonction est d'exposer, au démarrage :

- le **dashboard Aspire** (interface web de visualisation des traces) ;
- un **endpoint OTLP** (`http://localhost:4317` en gRPC, `4318` en HTTP)
  qui reçoit les spans exportés par le notebook Python Semantic Kernel.

C'est la forme de parité la plus forte décrite par l'issue #10474 : un
outil **.NET** (le dashboard Aspire) rend service à une chaîne **Python**
(le notebook SK), sans que celle-ci change de langage. La frontière est
le protocole OTLP — un standard de l'OpenTelemetry.

## Prérequis

- SDK **.NET 10** (`dotnet --version` ≥ 10.0.110)
- CLI Aspire : `dotnet tool install --global aspire.cli` (fournit `aspire` ;
  l'ancienne « charge de travail » (workload) Aspire est dépréciée sous
  .NET 10)
- Package **Aspire.Hosting.AppHost** 13.4.6 (livré via NuGet via le
  `#:sdk` de `apphost.cs`).

## Démarrage — mode standalone (recommandé pour le notebook)

Le dashboard Aspire embarque un mode **standalone**, conçu précisément
pour recevoir la télémétrie d'applications **externes** (ici, le notebook
Python) :

```bash
aspire dashboard run \
  --allow-anonymous \
  --otlp-grpc-url http://localhost:4317 \
  --frontend-url http://localhost:18888 \
  --non-interactive --nologo \
  -- --Dashboard:Api:Enabled=true --Dashboard:Api:AuthMode=Unsecured
```

- `http://localhost:4317` : endpoint OTLP gRPC que cible le notebook ;
- `http://localhost:18888` : UI du dashboard **et** son API de télémétrie
  (`/api/telemetry/spans`), que la cellule de relecture du notebook
  interroge pour relire les spans ;
- `--Dashboard:Api:*` active l'API HTTP de télémétrie sans authentification.

> Avertissement sécurité : ce mode laisse l'endpoint OTLP **sans
> authentification** — acceptable en boucle locale (`localhost`) sur un
> poste de dev, à ne pas exposer au-delà (cf. [considérations de sécurité
> du dashboard
> Aspire](https://learn.microsoft.com/dotnet/aspire/fundamentals/dashboard/security-considerations)).

Vérification en ligne de commande (retrouve les spans `gen_ai` envoyés
par le notebook) :

```bash
aspire otel spans --dashboard-url http://localhost:18888 --search gen_ai --non-interactive --nologo
```

## Démarrage — mode AppHost (`aspire run`)

Le dossier [`SkOtel.AppHost/`](SkOtel.AppHost/) contient l'**AppHost
minimal** (application *file-based* .NET 10, `apphost.cs` sans ressource) :
c'est le modèle de code de référence — un orchestrateur Aspire qui n'héberge
rien et ne fait que servir le dashboard. On le lance avec la CLI Aspire :

```bash
aspire run --apphost SkOtel.AppHost/apphost.cs
```

Pour le **notebook**, préférez le mode standalone ci-dessus : en mode
CLI-managed, l'endpoint OTLP est automatiquement sécurisé par une clé
d'API (les variables `ASPIRE_DASHBOARD_OTLP_*` sont ignorées), ce qui
convient aux ressources .NET de l'AppHost mais pas à un client Python
externe sans provisionnement de clé.

## Voir aussi

- Issue [#10474](https://github.com/jsboige/CoursIA/issues/10474) — grain SK-4 §6.
- Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473) — série *The Unexpected AI Stack: C#/.NET*.
- Notebook [`04-SemanticKernel-Filters-Observability.ipynb`](../04-SemanticKernel-Filters-Observability.ipynb) — consommateur OTLP.
