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
using Microsoft.DotNet.Interactive;
using Microsoft.SemanticKernel.ChatCompletion;
using System.ComponentModel;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;


namespace MyIA.AI.Notebooks;
class Program
{

	static async Task Main(string[] args)
	{
		 await UpdateNotebook();
	}

	static async Task UpdateNotebook()
	{
		Thread.CurrentThread.CurrentCulture = new CultureInfo("en-US"); 
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
		var updater = new NotebookPlannerUpdater(semanticKernel, notebookPath, logger, nbIterations);

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



//	public static async Task UpdateNotebookWithAgents(string[] args)
//	{
//		var serviceCollection = new ServiceCollection();
//		serviceCollection.AddLogging(builder => builder.AddConsole().SetMinimumLevel(LogLevel.Information));
//		var serviceProvider = serviceCollection.BuildServiceProvider();
//		var logger = serviceProvider.GetRequiredService<ILogger<Program>>();

//		var kernel = SKernel.Builder.Build();
//		var compositeKernel = new CompositeKernel();

//		kernel.ImportPluginFromType<WorkbookInteraction>(compositeKernel, logger);
//		kernel.ImportPluginFromType<ProjectManagerPlugin>();

//#pragma warning disable SKEXP0110
//		var coderAgent = new ChatCompletionAgent
//		{
//			Instructions = "You are an assistant coder. Your role is to update the notebook as instructed.",
//			Name = "CoderAgent",
//			Kernel = kernel,
//		};

//		var projectManagerAgent = new ChatCompletionAgent
//		{
//			Instructions = "You are the project manager. You oversee the notebook's progress and determine when the task is complete.",
//			Name = "ProjectManagerAgent",
//			Kernel = kernel,
//		};

//		KernelFunction terminationFunction = KernelFunctionFactory.CreateFromPrompt(
//			"""
//            Determine if the task is complete. If so, respond with a single word: yes.

//            History:
//            {{$history}}
//            """);

//		KernelFunction selectionFunction = KernelFunctionFactory.CreateFromPrompt(
//			"""
//            Determine the next participant in the conversation. Choose between "CoderAgent" and "ProjectManagerAgent".

//            History:
//            {{$history}}
//            """);

//		var chat = new AgentGroupChat(coderAgent, projectManagerAgent)
//		{
//			ExecutionSettings = new()
//			{
//				TerminationStrategy = new NotebookTerminationStrategy(terminationFunction, kernel),
//				SelectionStrategy = new NotebookSelectionStrategy(selectionFunction, kernel),
//			}
//		};

//		string input = "Create a .NET interactive notebook for querying DBPedia and visualizing results.";
//		chat.AddChatMessage(new ChatMessageContent(AuthorRole.User, input));
//		Console.WriteLine($"# {AuthorRole.User}: '{input}'");

//		await foreach (var content in chat.InvokeAsync())
//		{
//			Console.WriteLine($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
//		}

//		Console.WriteLine($"# IS COMPLETE: {chat.IsComplete}");
//	}


}


//public class ProjectManagerPlugin
//{
//	//[KernelFunction]
//	//[Description("Check if the notebook task is complete.")]
//	//public string CheckTaskCompletion(string notebookJson)
//	//{
//	//	// Logic to check if the task is complete.
//	//	// For simplicity, we assume the task is complete if a specific string is found in the notebook JSON.
//	//	if (notebookJson.Contains("TASK_COMPLETED"))
//	//	{
//	//		return "yes";
//	//	}
//	//	return "no";
//	//}

//	[KernelFunction]
//	[Description("Send the final answer when the notebook task is complete.")]
//	public string SendFinalAnswer(string answer)
//	{
//		return "TASK_COMPLETED:\n" answer;
//	}
//}


//public class NotebookTerminationStrategy : KernelFunctionTerminationStrategy
//{
//	public NotebookTerminationStrategy(KernelFunction terminationFunction, Kernel kernel)
//		: base(terminationFunction, kernel)
//	{
//		Agents = new List<ChatCompletionAgent>
//		{
//			new ChatCompletionAgent
//			{
//				Name = "ProjectManagerAgent",
//				Kernel = kernel,
//				Instructions = "Check if the notebook task is complete and send the final answer."
//			}
//		};
//		ResultParser = (result) => result.GetValue<string>()?.Contains("yes", StringComparison.OrdinalIgnoreCase) ?? false;
//		HistoryVariableName = "history";
//		MaximumIterations = 10;
//	}
//}


//public class NotebookSelectionStrategy : KernelFunctionSelectionStrategy
//{
//	public NotebookSelectionStrategy(KernelFunction selectionFunction, Kernel kernel)
//		: base(selectionFunction, kernel)
//	{
//		ResultParser = (result) => result.GetValue<string>() ?? "CoderAgent";
//		AgentsVariableName = "agents";
//		HistoryVariableName = "history";
//	}
//}

