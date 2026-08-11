using Aspire.Hosting;

// AppHost Aspire minimal pour l'axe observabilité du notebook SK-4 (#10474, Epic #10473).
//
// Ce hôte n'orchestre AUCUNE ressource de notre pile GenAI. Il sert exclusivement
// de backend OTLP pour le notebook Python 04-SemanticKernel-Filters-Observability
// (section 6 « OpenTelemetry ») : le dashboard Aspire et l'endpoint OTLP
// (http://localhost:4317 en gRPC, 4318 en HTTP) sont exposés automatiquement par
// DCP au démarrage. Le notebook Python envoie ses spans SK sur cet endpoint ;
// le dashboard .NET les reçoit et les affiche. C'est la forme de parité la plus
// forte décrite par l'issue : un outil .NET rend service à la chaîne Python,
// sans que celle-ci change de langage.
var builder = DistributedApplication.CreateBuilder(args);

// Aucune ressource ajoutée : le dashboard OTLP est l'unique surface.

builder.Build().Run();
