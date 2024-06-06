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
using System.Diagnostics.CodeAnalysis;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Microsoft.SemanticKernel.Connectors.OpenAI;


namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
class Program
{
	private const string? WorkbookUpdaterName = "WorkbookUpdater";
	private const string? WorkbookValidatorName = "WorkbookValidator";
	private static DisplayLogger _logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);

	[Experimental("SKEXP0110")]
	static async Task Main(string[] args)
	{
		 //await UpdateNotebook();
		 //await RunGameAsync();
		 await UpdateNotebookWithAgents();
	}

	static async Task UpdateNotebook()
	{
		Thread.CurrentThread.CurrentCulture = new CultureInfo("en-US"); 
		var semanticKernel = InitSemanticKernel();

		Console.WriteLine("Kernel et Semantic Kernel initialisés.");

		// Description de la tâche
		string taskDescription = "Créer un notebook .Net interactive permettant de requêter DBPedia, utilisant le package Nuget dotNetRDF. Choisir un exemple de requête dont le résultat peut être synthétisé dans un graphique. Utiliser Plotly.NET.Interactive ou XPlot.Plotly.Interactive pour afficher un graphique synthétisant les résultats et ne pas oublier de documenter l'ensemble dans le markdown et dans le code.";

		// Initialisation du notebook
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(taskDescription, notebookPath);

		// Création et exécution de NotebookUpdater
		var nbIterations = 50;
		Console.WriteLine("Création de l'instance NotebookUpdater...");
		var updater = new NotebookPlannerUpdater(semanticKernel, notebookPath, _logger, nbIterations);

		Console.WriteLine("Appel à UpdateNotebook...");
		var response = await updater.UpdateNotebook();

		Console.WriteLine($"Résultat de l'exécution du notebook :\n{response}");
	}

	private static SKernel InitSemanticKernel()
	{
		Console.WriteLine("Initialisation...");

		// Initialisation du logger

		// Configuration des services de l'AI
		var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();

		// Configuration du kernel semantic
		var builder = SKernel.CreateBuilder();

		builder.Services.AddLogging(loggingBuilder =>
		{
			loggingBuilder.AddProvider(new DisplayLoggerProvider(LogLevel.Trace));
		});

		if (useAzureOpenAI)
			builder.AddAzureOpenAIChatCompletion(model, azureEndpoint, apiKey);
		else
			builder.AddOpenAIChatCompletion(model, apiKey, orgId);

		var semanticKernel = builder.Build();
		return semanticKernel;
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



	public static async Task UpdateNotebookWithAgents()
	{
		var serviceCollection = new ServiceCollection();
		serviceCollection.AddLogging(builder => builder.AddProvider(new DisplayLoggerProvider(LogLevel.Trace)));
		var serviceProvider = serviceCollection.BuildServiceProvider();

		

		Console.WriteLine("Kernel et Semantic Kernel initialisés.");

		// Description de la tâche
		string taskDescription = "Créer un notebook .Net interactive permettant de requêter DBPedia, utilisant le package Nuget dotNetRDF. Choisir un exemple de requête dont le résultat peut être synthétisé dans un graphique. Utiliser Plotly.NET.Interactive ou XPlot.Plotly.Interactive pour afficher un graphique synthétisant les résultats et ne pas oublier de documenter l'ensemble dans le markdown et dans le code.";

		// Initialisation du notebook
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(taskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		//var compositeKernel = new CompositeKernel();

		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, _logger);
		var updaterKernel = InitSemanticKernel();
		updaterKernel.ImportPluginFromObject(workbookInteraction);
		var workbookValidation = new WorkbookValidation(notebookPath, _logger);
		var validationKernel = InitSemanticKernel();
		validationKernel.ImportPluginFromObject(workbookValidation);

#pragma warning disable SKEXP0110
		var coderAgent = new ChatCompletionAgent
		{
			Instructions = "You are an assistant coder. Your role is to update the notebook as instructed."+
			               $"Assist in creating the following interactive .NET notebook, which includes a description of its purpose.\n" +
			               $"You are part of a group chat with 2 assistants having conversation discussing and using function calls to incrementally improve and validate it. The other assistant reviews you changes when you submit the notebook for validation:\n" +
			               $"- Initially, use the ReplaceWorkbookCell function to edit targeted cells. As the notebook evolves, use ReplaceBlockInWorkbookCell or InsertInWorkbookCell. Pay attention to these functions' distinct signatures to avoid mismatches.\n" +
			               $"- These functions execute the code cells by default, returning corresponding outputs. You can also choose to restart the kernel and run the entire notebook when necessary.\n" +
			               $"- Continue updating the notebook until it runs without errors, with code cells correctly implementing the required tasks and markdown cells containing appropriate documentation.\n" +
			               $"- Be cautious with NuGet packages to avoid mix-ups in package names and namespaces.\n"+
							$"- When you feel the notebook can be validated, use the SubmitNotebook to have the other assistant validate it.\n",
			Name = WorkbookUpdaterName,
			Kernel = updaterKernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
		};

		var projectManagerAgent = new ChatCompletionAgent
		{
			Instructions = "You are the project manager. You oversee the notebook's progress and determine when the task is complete."+
			               $"Assist in creating the following interactive .NET notebook, which includes a description of its purpose.\n" +
			               $"You are part of a group chat with 2 assistants having conversation discussing and using function calls to incrementally improve and validate it. The other assistant is updating the notebook, you mus discuss and validate its work:\n" +
			               $"- Use the RunNotebook function to run and return the outputs of the current notebook.\n" +
							$"- Use the ApproveNotebook function once the notebook was tester with appropriate outputs.\n",
			Name = WorkbookValidatorName,
			Kernel = validationKernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
		};

		KernelFunction terminationFunction = KernelFunctionFactory.CreateFromPrompt(
			"""
	            Determine if the task is complete. If so, respond with a single word: yes.

	            History:
	            {{$history}}
	            """);

		KernelFunction selectionFunction = KernelFunctionFactory.CreateFromPrompt(
			"""
	            Determine the next participant in the conversation. Choose between "CoderAgent" and "ProjectManagerAgent".

	            History:
	            {{$history}}
	            """);

		var chat = new AgentGroupChat(coderAgent, projectManagerAgent)
		{
			ExecutionSettings = new()
			{
				TerminationStrategy = new NotebookTerminationStrategy(){WorkbookValidation = workbookValidation},
				SelectionStrategy = new NotebookSelectionStrategy(){WorkbookUpdateInteraction = workbookInteraction},
			},
			LoggerFactory = new DisplayLogger(nameof(Program), LogLevel.Trace)
		};


		var input = $"\nHere is the starting notebook:\n{notebookJson}\nEnsure that the workbook is thoroughly tested, documented, and cleaned before calling the 'ApproveNotebook' function.";
		chat.AddChatMessage(new ChatMessageContent(AuthorRole.User, input));
		Console.WriteLine($"# {AuthorRole.User}: '{taskDescription}'");

		await foreach (var content in chat.InvokeAsync())
		{
			Console.WriteLine($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
		}

		Console.WriteLine($"# IS COMPLETE: {chat.IsComplete}");
	}


	[Experimental("SKEXP0110")]
	private class NotebookTerminationStrategy : TerminationStrategy
	{

		public WorkbookValidation WorkbookValidation { get; set; }


		protected override Task<bool> ShouldAgentTerminateAsync(Agent agent, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken)
		{
			return Task.FromResult(WorkbookValidation.IsApproved);
		}
	}

	[Experimental("SKEXP0110")]
	public class NotebookSelectionStrategy : SelectionStrategy
	{

		public WorkbookUpdateInteraction WorkbookUpdateInteraction { get; set; }


		public override Task<Agent> NextAsync(IReadOnlyList<Agent> agents, IReadOnlyList<ChatMessageContent> history,
			CancellationToken cancellationToken = new CancellationToken())
		{
			if (WorkbookUpdateInteraction.IsPendingApproval)
			{
				return Task.FromResult(agents.First(a => a.Name == WorkbookValidatorName));
			}
			else
			{
				return Task.FromResult(agents.First(a => a.Name == WorkbookUpdaterName));
			}
		}
	}

	[Experimental("SKEXP0110")]
	public static async Task RunGameAsync()
	{

		var motADeviner = "Anticonstitutionnellement";

		const string pereFourasSystemPrompt = @"Tu es le Père Fouras de Fort Boyard. Tu discutes avec l'assistant Laurent Jalabert.
        Tu dois lui faire deviner le mot ou l'expression suivante : '{{word}}'. 
        Parle en charades et en réponses énigmatiques. Ne mentionne jamais l'expression à deviner";

		const string laurentJalabertSystemPrompt = @"Tu es Laurent Jalabert. Tu discutes avec l'assistant Père Fouras. 
        Tu dois retrouver le mot ou l'expression que le Père Fouras est chargé de te fait deviner. 
        Tu as le droit de poser des questions fermées (réponse oui ou non).";

		var pereFourasPrompt = pereFourasSystemPrompt.Replace("{{word}}", motADeviner);
		var laurentJalabertPrompt = laurentJalabertSystemPrompt;

		// Define the agent
		ChatCompletionAgent agentReviewer = new()
		{
			Instructions = pereFourasPrompt,
			Name = "Pere_Fouras",
			Kernel = InitSemanticKernel(),
		};

		ChatCompletionAgent agentWriter = new()
		{
			Instructions = laurentJalabertPrompt,
			Name = "Laurent_Jalabert",
			Kernel = InitSemanticKernel(),
		};

		// Create a chat for agent interaction.
		AgentGroupChat chat = new(agentReviewer, agentWriter)
		{
			ExecutionSettings = new()
			{
				TerminationStrategy = new ApprovalTerminationStrategy(motADeviner)
				{
					Agents = new List<ChatCompletionAgent> { agentWriter },
					MaximumIterations = 30,
				},
			}
		};

		await foreach (var content in chat.InvokeAsync())
		{
			_logger.LogInformation($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
		}
	}

	[Experimental("SKEXP0110")]
	private class ApprovalTerminationStrategy(string motADeviner) : TerminationStrategy
	{
		protected override Task<bool> ShouldAgentTerminateAsync(Agent agent, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken)
		{
			return Task.FromResult(history[^1].Content?.Contains(motADeviner, StringComparison.OrdinalIgnoreCase) ?? false);
		}
	}




}



