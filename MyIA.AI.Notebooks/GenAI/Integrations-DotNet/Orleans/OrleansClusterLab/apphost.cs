#:sdk Aspire.AppHost.Sdk@13.4.6
#:package Aspire.Hosting.Orleans@13.4.6
#:package Aspire.Hosting.Redis@13.4.6
using Aspire.Hosting;

// Lab 04 Orleans x Aspire : un cluster de deux silos dont l'appartenance ET l'etat
// des grains vivent dans un Redis declare par l'AppHost (epic #10473, suite nommee
// par le registre des axes : "cabler WithGrainStorage dans l'AppHost Aspire").
//
// Difference avec le lab 02 : le silo ne contient plus AUCUN code de clustering ni
// de stockage. L'AppHost declare le Redis, le rattache au service Orleans pour deux
// usages (table d'appartenance + fournisseur "sessions"), et Aspire injecte cette
// topologie dans chaque replique sous forme de configuration.

var builder = DistributedApplication.CreateBuilder(args);

// Le Redis est un conteneur gere par l'AppHost (image, port, mot de passe genere).
var redis = builder.AddRedis("redis");
// TODO etudiant (Exercice 1) : faire survivre l'etat des sessions a un redemarrage
// de l'AppHost. Indices : la ressource Redis sait monter un volume de donnees nomme
// et regler la frequence de ses instantanes sur disque. Attention : ce Redis porte
// AUSSI la table d'appartenance du cluster. La rendre durable ressuscite au
// redemarrage des silos morts, que les nouveaux silos tentent de joindre avant
// d'entrer dans le cluster (notebook 04, exercice 1).

var orleans = builder.AddOrleans("cluster")
    .WithClusterId("cluster-lab")
    .WithServiceId("orleans-cluster-lab")
    .WithClustering(redis)                 // table d'appartenance du cluster dans Redis
    .WithGrainStorage("sessions", redis);  // fournisseur de stockage "sessions" dans Redis

// Deux repliques du meme projet silo, derriere un seul port HTTP : Aspire place un
// proxy sur 5310 qui repartit les connexions entre les repliques.
builder.AddProject("silo", "./Silo/Silo.csproj")
    .WithReference(orleans)
    .WaitFor(redis)
    .WithHttpEndpoint(port: 5310, name: "api")
    .WithReplicas(2);

builder.Build().Run();
