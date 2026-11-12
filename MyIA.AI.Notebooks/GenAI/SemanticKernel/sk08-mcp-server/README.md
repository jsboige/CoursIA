# Serveur MCP du carnet SK-08

Ce projet .NET 9 utilise les SDK officiels `ModelContextProtocol` 2.4.0 et `Microsoft.SemanticKernel` 1.82.0. Depuis le dossier du carnet, `dotnet build sk08-mcp-server/Sk08McpServer.csproj` restaure et compile le serveur. Le carnet lance ensuite la DLL via le client MCP stdio et ferme les clients. Le mode `--sk` exporte le plugin Semantic Kernel. La sortie standard est réservée au protocole ; aucun journal n'y est écrit.

La vérification de chemin est lexicale et ne résout pas les liens symboliques ; elle illustre le protocole, pas un contrôle de sécurité de fichiers. Les bornes numériques sont vérifiées dans les fonctions serveur ; les erreurs remontent en `isError`. Les objets de démonstration sont sérialisés dans le contenu textuel MCP.
