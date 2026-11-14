# Integrations-DotNet — hub des bindings .NET GenAI

Point de chute canonique des bindings .NET GenAI de la série *The Unexpected AI Stack:
C#/.NET* ([EPIC #10473](https://github.com/jsboige/CoursIA/issues/10473)) : les axes de la
série qui n'ont pas de série pédagogique à part entière vivent ici, un binding par dossier.
Le registre des axes distillables de la série vit dans
[`Aspire/distilled-axes-registry.md`](Aspire/distilled-axes-registry.md).

## Contenu

| Trajectoire | Contenu |
|---|---|
| [Aspire/](Aspire/README.md) | Série principale : orchestrer la pile GenAI dans un AppHost compilé et typé — observabilité OpenTelemetry, streaming d'agents, tests d'intégration, garde-fous Roslyn, flotte sémantique multi-connecteurs |
| [Orleans/](Orleans/README.md) | Grains acteurs stateful pour les workloads IA, silo co-hosté par un AppHost, persistance Redis, cluster |
| [CopilotSDK/](CopilotSDK/README.md) | Le SDK GitHub Copilot piloté depuis C# en streaming, endpoints typés + projet compagnon `CopilotAgent.App/` |
| [Scrutor/](Scrutor/README.md) | Des endpoints de minimal API découverts par convention (`Scan()`) + lab `ScrutorLab/` |
| [01-EFCore-Requetes-Compilees.ipynb](01-EFCore-Requetes-Compilees.ipynb) | EF Core : le compilateur comme garde-fou jusque dans les requêtes (`EF.CompileQuery` mesuré 2,93×, `ToQueryString()`, `FromSqlInterpolated`) — binding sans projet compagnon, à la racine du hub |

## Rangement

La règle de niveau du hub : **un binding sans projet compagnon vit à la racine du hub, un
binding dont le carnet exécute un projet .NET réel garde son dossier** — et c'est cette raison
que chaque README de dossier écrit en une phrase.

- **EF Core** : mono-carnet, aucun projet compagnon → absorbé à la racine du hub (ce PR,
  soldant la promesse d'absorption de [PR #14431](https://github.com/jsboige/CoursIA/pull/14431),
  [#13581](https://github.com/jsboige/CoursIA/issues/13581) T2), et listé dans l'index ci-dessus.
- **Copilot SDK** : le carnet exécute `CopilotAgent.App/` → garde son dossier, déclaré dans
  [`CopilotSDK/README.md`](CopilotSDK/README.md).
- **Scrutor** : le carnet exécute `ScrutorLab/` → garde son dossier, déclaré dans
  [`Scrutor/README.md`](Scrutor/README.md).
