using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.SemanticKernel;
using SKernel = Microsoft.SemanticKernel.Kernel;


namespace MyIA.AI.Notebooks;
class Program
{

	static async Task Main(string[] args)
	{
		 await UpdateNotebook();
	}

	static async Task UpdateNotebook()
	{
		Thread.CurrentThread.CurrentCulture = CultureInfo.InvariantCulture;
		Console.WriteLine("Initialisation...");

		// Initialisation du logger
		var logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);

		// Configuration des services de l'AI
		var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();

		// Configuration du kernel semantic
		var builder = SKernel.CreateBuilder();

		builder.Services.AddLogging(loggingBuilder =>
		{
			loggingBuilder.AddProvider(new DisplayLoggerProvider(LogLevel.Information));
		});

		if (useAzureOpenAI)
			builder.AddAzureOpenAIChatCompletion(model, azureEndpoint, apiKey);
		else
			builder.AddOpenAIChatCompletion(model, apiKey, orgId);

		var semanticKernel = builder.Build();

		Console.WriteLine("Kernel et Semantic Kernel initialisés.");

		// Description de la tâche
		string taskDescription = "Créer un notebook .Net interactive permettant de requêter DBPedia, utilisant le package Nuget dotNetRDF. Choisir un exemple de requête dont le résultat peut être synthétisé dans un graphique. Utiliser Plotly.NET.Interactive ou XPlot.Plotly.Interactive pour afficher un graphique synthétisant les résultats et ne pas oublier de documenter l'ensemble dans le markdown et dans le code.";

		// Initialisation du notebook
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(taskDescription, notebookPath);

		// Création et exécution de NotebookUpdater
		var nbIterations = 50;
		Console.WriteLine("Création de l'instance NotebookUpdater...");
		var updater = new NotebookUpdater(semanticKernel, notebookPath, logger, nbIterations);

		Console.WriteLine("Appel à UpdateNotebook...");
		var response = await updater.UpdateNotebook();

		Console.WriteLine($"Résultat de l'exécution du notebook :\n{response}");
	}

	static void SetStartingNotebook(string taskDescription, string notebookPath)
	{
		var notebookTemplatePath = "./Semantic-Kernel/Workbook-Template.ipynb";
		string notebookContent = File.Exists(notebookPath) ? File.ReadAllText(notebookPath) : File.ReadAllText(notebookTemplatePath);

		notebookContent = notebookContent.Replace("{{TASK_DESCRIPTION}}", taskDescription);
		var dirNotebook = new FileInfo(notebookPath).Directory;
		if (!dirNotebook.Exists)
		{
			dirNotebook.Create();
		}

		File.WriteAllText(notebookPath, notebookContent);
		Console.WriteLine($"Notebook personnalisé prêt à l'exécution\n{notebookContent}");
	}
}

