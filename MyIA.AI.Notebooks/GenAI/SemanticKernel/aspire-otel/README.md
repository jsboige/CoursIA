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
- Package **Aspire.Hosting.AppHost** 13.4.6 (livré via NuGet — l'ancienne
  « charge de travail » (workload) Aspire est dépréciée sous .NET 10 ; ce
  projet ne la requiert pas).

## Démarrage

```bash
cd SkOtel.AppHost
dotnet run
```

Au démarrage, la console affiche l'URL du dashboard (typiquement
`http://localhost:18888`) et l'endpoint OTLP gravé dans
`ASPIRE_ENDPOINT` / OTLP. Le notebook Python cible alors cet endpoint
pour exporter ses spans.

## Voir aussi

- Issue [#10474](https://github.com/jsboige/CoursIA/issues/10474) — grain SK-4 §6.
- Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473) — série *The Unexpected AI Stack: C#/.NET*.
- Notebook [`04-SemanticKernel-Filters-Observability.ipynb`](../04-SemanticKernel-Filters-Observability.ipynb) — consommateur OTLP.
