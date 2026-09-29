#:sdk Aspire.AppHost.Sdk@13.4.6
#:package Aspire.Hosting.Orleans@13.4.6
using Aspire.Hosting;

// Lab 02 Orleans x Aspire : le silo comme RESSOURCE d'une application
// distribuee, declaree en C# (epic #10473, axe successeur Orleans du registre —
// "co-host Aspire AppHost + IGrainWithGuidKey").
//
// L'AppHost n'embarque PAS de runtime Orleans : Aspire.Hosting.Orleans fournit
// le modele de DECLARATION du service (cluster id, clustering dev, providers).
// Le silo lui-meme est le projet ./Silo — orchestre par l'AppHost (lifecycle,
// logs, sante dans le dashboard), contrairement au lab 01 ou le silo etait un
// process ad hoc lance par le notebook.

var builder = DistributedApplication.CreateBuilder(args);

var orleans = builder.AddOrleans("agent-cluster")
    .WithClusterId("agent-cluster")
    .WithServiceId("orleans-aspire-lab")
    .WithDevelopmentClustering();

builder.AddProject("silo", "./Silo/Silo.csproj")
    .WithReference(orleans);

builder.Build().Run();
