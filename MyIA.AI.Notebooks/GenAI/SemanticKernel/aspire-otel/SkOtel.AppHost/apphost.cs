#:sdk Aspire.AppHost.Sdk@13.4.6
// AppHost Aspire minimal (modèle file-based SDK-10) pour l'axe observabilité
// du notebook SK-4 (#10474, Epic #10473 *The Unexpected AI Stack*).
//
// Ce hôte n'orchestre AUCUNE ressource de notre pile GenAI. Il sert exclusivement
// de backend OTLP pour le notebook Python 04-SemanticKernel-Filters-Observability
// (section 6 « OpenTelemetry ») : le dashboard Aspire et l'endpoint OTLP sont
// exposés au démarrage (cf. apphost.run.json, OTLP piné sur localhost:4317).
//
// Le notebook Python envoie ses spans SK sur cet endpoint ; le dashboard .NET les
// reçoit et les affiche. C'est la forme de parité la plus forte décrite par
// l'issue : un outil .NET rend service à la chaîne Python, sans que celle-ci
// change de langage. La frontière est le protocole OTLP.
//
// Note tooling : la directive de SDK file-based `#:sdk Aspire.AppHost.Sdk` (modèle
// canonique SDK-10) remplace le couple `<IsAspireHost>true</IsAspireHost>` +
// `<PackageReference Aspire.Hosting.AppHost>` — sous .NET 10, IsAspireHost
// déclenche NETSDK1228 (workload Aspire déprécié), et le package seul n'est pas
// reconnu par le ProjectLocator de `aspire run`. Le SDK file-based câble DCP +
// dashboard ET satisfait le locator.

var builder = DistributedApplication.CreateBuilder(args);

// Aucune ressource ajoutée : le dashboard OTLP est l'unique surface.

builder.Build().Run();
