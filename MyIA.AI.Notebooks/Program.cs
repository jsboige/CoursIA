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
using AutoGen.Core;
using AutoGen.OpenAI;
using AutoGen.OpenAI.Extension;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using AutoGen.SemanticKernel;
using Azure.AI.OpenAI;
using Humanizer;


namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
class Program
{
	private const string? CoderAgentName = "Coder_Agent";
	private const string? ReviewerAgentName = "Reviewer_Agent";
	private const string? AdminAgentName = "Admin_Agent";

	private const string? GeneralGroupChatInstructions = $"Assist in creating the following .NET interactive notebook, which includes a description of its objective.\n" +
														 $"You are part of a group chat with several assistants conversing and using function calls to incrementally improve, review and validate it.\n";

	private const string? CoderAgentInstructions = "You are an assistant coder. Your role is to update a notebook as instructed, using provided functions.\n" + GeneralGroupChatInstructions +
												   $"- Initially, use the ReplaceWorkbookCell function to edit targeted cells. As the notebook evolves, use ReplaceBlockInWorkbookCell or InsertInWorkbookCell for large cells. Pay attention to these functions' distinct signatures to avoid mismatches.\n" +
												   $"- These functions execute the code cells by default, returning corresponding outputs. You can also choose to restart the kernel, run and return the entire notebook when necessary, but keep that use limited to the cases where the state is unclear from the conversation, because it shoots up the token budget for the agent conversation.\n" +
												   //$"- If Auto-invoke is applied, continue updating the notebook by yourself chatting with tools but only up to a maximum of 5 tool calls round trips. Try to fix errors, to feed code cells by correctly implementing the required tasks and to feed markdown cells with thought process and appropriate documentation.\n" +
												   $"- Be cautious with NuGet packages to avoid mix-ups in package names and namespaces, and use display(myObj) or myObj.Display() to output intermediate results.\n" +
												   //$"- Always add messages together with your function calls to document your thinking process, because empty function calls and the tool responses will be considered internal and removed from the group chat.\n" +
												   //Todo: remove autogen fix   $"- Always add messages together with your function calls to document your thinking process, because empty function calls and the tool responses will be considered internal and removed from the group chat.\n" +
												   $"- Please use as many simultaneous tool calls as possible to save conversational tokens, and when calling tools, do leave the chat text response empty because we're using AutoGen.Net for agents orchestration, and it won't process your function calls unless the response message is empty.\n" +
												   $"- When you don't know why a call failed because a cell was not found, if you get stuck with bugs over several fixing attempts, or simply every once in while (4-5 tool calls) for external feedback from other assistants, simply return a message that explains the current status without doing any more function calls. This will let other agents take the opportunity to reflect on your updates, and you will get other rounds of tool call updates to finish up with a fresher perspective.\n" +
												   $"- When you gathered enough positive feedback and you think the notebook can be validated, that is, once you were able to state that all cells content and outputs are giving satisfaction, then use the SubmitNotebook to submit your work for a final round of validation.\n";

	private const string? ReviewerAgentInstructions = "You are an assistant coder supervisor. Your role is to comment on the updates performed on a notebook by the assistant coder." + GeneralGroupChatInstructions +
															$"Your role is to review and comment the updates performed by the coder assistant, and to unstuck him if needed.\n" +
															$"If the ongoing conversation isn't clear enough to assess the current state of the notebook, you can use the RunNotebook function to run the notebook from scratch and return the resulting json with outputs.\n" +
															$"Answer with comments of what's been done right and wrong and suggestions to get going, in order to help the coder assistant making the appropriate updates and fixes. Pay attention to the error outputs and make sure the objectif is being properly implemented.\n";

	private const string? AdminAgentInstructions = "You are a strict project manager with high coding skills, in charge of managing a development task. You oversee development progress and determine when the task is complete." + GeneralGroupChatInstructions +
															$"- Use the RunNotebook function to run and return the outputs of the current notebook.\n" +
															$"- Use the ApproveNotebook function once the notebook was tested with appropriate outputs.\n" +
															$"- Before you approve the notebook make sure to explicitly review all cells, the validity of their outputs and make a clear statement explaining why you think the notebook's goal was completed, based on the cells' content and outputs.\n";

	private const string NotebookTaskDescription = "Créer un notebook .Net interactive permettant de requêter DBPedia, utilisant les package Nuget dotNetRDF et XPlot.Plotly.Interactive. Commencer par éditer les cellules de Markdown pour définir et affiner l'exemple de requête dont le graphique final sera le plus pertinent. Choisir un exemple de requête complexe, manipulant des aggrégats, qui pourront être synthétisés dans un graphique. Une fois les cellules de code alimentées et les bugs corrigés, s'assurer que la sortie de la cellule générant le graphique est conforme et pertinente.";

	//private const string NotebookTaskDescription = "Créer un notebook .Net interactive permettant de requêter giTHUB ET ME Faire une liste des projets en python ayant le plus grand nombre de stars";

	private static DisplayLogger _logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);

	[Experimental("SKEXP0110")]
	static async Task Main(string[] args)
	{
		//await UpdateNotebook();
		//await RunGameAsync();
		//await UpdateNotebookWithAutoInvokeSKAgents();
		await UpdateNotebookWithAutoGenSKAgents();
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



	public static async Task UpdateNotebookWithAutoInvokeSKAgents()
	{
		var serviceCollection = new ServiceCollection();
		serviceCollection.AddLogging(builder => builder.AddProvider(new DisplayLoggerProvider(LogLevel.Trace)));
		var serviceProvider = serviceCollection.BuildServiceProvider();


		// Description de la tâche
		string taskDescription = NotebookTaskDescription;

		// Initialisation du notebook
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(taskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, _logger);
		var workbookSupervision = new WorkbookInteractionBase(notebookPath, _logger);
		var workbookValidation = new WorkbookValidation(notebookPath, _logger);


		var groupChatAgents = GetSKGroupChatAgents(workbookInteraction, workbookSupervision, workbookValidation);


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

		var chat = new AgentGroupChat(groupChatAgents.Values.Select(tuple => (Agent) tuple.agent).ToArray())
		{
			ExecutionSettings = new()
			{
				TerminationStrategy = new NotebookTerminationStrategy() { WorkbookValidation = workbookValidation },
				SelectionStrategy = new NotebookSelectionStrategy() { WorkbookUpdateInteraction = workbookInteraction },
			},
			LoggerFactory = new DisplayLogger(nameof(Program), LogLevel.Trace)
			//Todo: remove autogen fix	//LoggerFactory = new DisplayLogger(nameof(Program), LogLevel.Trace)
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



	public static async Task UpdateNotebookWithAutoGenSKAgents()
	{
		//var serviceCollection = new ServiceCollection();
		//serviceCollection.AddLogging(builder => builder.AddProvider(new DisplayLoggerProvider(LogLevel.Trace)));
		//var serviceProvider = serviceCollection.BuildServiceProvider();

		// Description de la tâche
		string taskDescription = NotebookTaskDescription;

		// Initialisation du notebook
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(taskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, _logger);
		var workbookSupervision = new WorkbookInteractionBase(notebookPath, _logger);
		var workbookValidation = new WorkbookValidation(notebookPath, _logger);

		var groupChatAgents = GetSKGroupChatAgents(workbookInteraction, workbookSupervision, workbookValidation);
		var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();
		var openAIClient = new OpenAIClient(apiKey);


		var messageConnector = new SemanticKernelChatMessageContentConnector();
		
		var coderKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[CoderAgentName].agent.Kernel, groupChatAgents[CoderAgentName].plugin);
		//var coderAutoGenAgent = new SemanticKernelChatCompletionAgent(groupChatAgents[CoderAgentName].agent)
		//	.RegisterPrintMessage()
		//	.RegisterMiddleware(coderKernelPluginMiddleware)
		//	.RegisterMiddleware(messageConnector);

		var coderAutoGenAgent = new OpenAIChatAgent(
				openAIClient: openAIClient,
				name: CoderAgentName,
				systemMessage: CoderAgentInstructions,
				modelName: model)
			.RegisterMessageConnector() // register message connector so it support AutoGen built-in message types like TextMessage.
			.RegisterMiddleware(coderKernelPluginMiddleware) // register the middleware to handle the plugin functions
			.RegisterPrintMessage(); // pretty print the message to the console

		var reviewerKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[ReviewerAgentName].agent.Kernel, groupChatAgents[ReviewerAgentName].plugin);
		//var reviewerAutoGenAgent = new SemanticKernelChatCompletionAgent(groupChatAgents[ReviewerAgentName].agent)
		//	.RegisterPrintMessage()
		//	.RegisterMiddleware(reviewerKernelPluginMiddleware)
		//	.RegisterMiddleware(messageConnector);

		var reviewerAutoGenAgent = new OpenAIChatAgent(
				openAIClient: openAIClient,
				name: ReviewerAgentName,
				systemMessage: ReviewerAgentInstructions,
				modelName: model)
			.RegisterMessageConnector() // register message connector so it support AutoGen built-in message types like TextMessage.
			.RegisterMiddleware(reviewerKernelPluginMiddleware) // register the middleware to handle the plugin functions
			.RegisterPrintMessage(); // pretty print the message to the console

		var adminKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[AdminAgentName].agent.Kernel, groupChatAgents[AdminAgentName].plugin);
		//var adminAutoGenAgent = new SemanticKernelChatCompletionAgent(groupChatAgents[AdminAgentName].agent)
		//	.RegisterPrintMessage()
		//	.RegisterMiddleware(async (msgs, option, agent, _) =>
		//		{
		//			var reply = await agent.GenerateReplyAsync(msgs, option);
		//			if (reply is TextMessage textMessage && workbookValidation.IsApproved)
		//			{
		//				var content = $"{textMessage.Content}\n\n {GroupChatExtension.TERMINATE}";

		//				return new TextMessage(Role.Assistant, content, from: reply.From);
		//			}

		//			return reply;
		//		})
		//	.RegisterMiddleware(adminKernelPluginMiddleware)
		//	.RegisterMiddleware(messageConnector);

		var adminAutoGenAgent = new OpenAIChatAgent(
				openAIClient: openAIClient,
				name: AdminAgentName,
				systemMessage: AdminAgentInstructions,
				modelName: model)
			.RegisterMessageConnector()
			.RegisterMiddleware(async (msgs, option, agent, _) =>
			{
				var reply = await agent.GenerateReplyAsync(msgs, option);
				if (reply is TextMessage textMessage && workbookValidation.IsApproved)
				{
					var content = $"{textMessage.Content}\n\n {GroupChatExtension.TERMINATE}";

					return new TextMessage(Role.Assistant, content, from: reply.From);
				}

				return reply;
			})
			.RegisterMiddleware(adminKernelPluginMiddleware)
			.RegisterPrintMessage(); // pretty print the message to the console


		var admin2CoderTransition = Transition.Create(from: adminAutoGenAgent,
		to: coderAutoGenAgent,
		canTransitionAsync: async (from, to, messages) =>
		{
			return !workbookValidation.IsApproved;
		});
		var reviewer2CoderTransition = Transition.Create(reviewerAutoGenAgent, coderAutoGenAgent);
		var coder2ReviewerTransition = Transition.Create(
			from: coderAutoGenAgent,
			to: reviewerAutoGenAgent,
			canTransitionAsync: async (from, to, messages) =>
			{
				return !workbookInteraction.IsPendingApproval;
			});
		var coder2AdminTransition = Transition.Create(
			from: coderAutoGenAgent,
			to: reviewerAutoGenAgent,
			canTransitionAsync: async (from, to, messages) =>
			{
				return workbookInteraction.IsPendingApproval;
			});



		var workflow = new Graph(
		[
			admin2CoderTransition,
			coder2ReviewerTransition,
			reviewer2CoderTransition,
		]);

		var groupChat = new GroupChat(
			admin: adminAutoGenAgent,
			workflow: workflow,
			members:
			[
				adminAutoGenAgent,
				coderAutoGenAgent,
				reviewerAutoGenAgent,
			]);
		adminAutoGenAgent.SendIntroduction("Welcome to my group, please work together to resolve my task", groupChat);
		coderAutoGenAgent.SendIntroduction("I will incrementally update the markdown and code cells of the notebook to resolve task", groupChat);
		reviewerAutoGenAgent.SendIntroduction($"I will help {CoderAgentName} by reviewing his work", groupChat);




		var input = $"\nHere is the starting notebook:\n{notebookJson}\n Now let's fill up those cells.";

		var groupChatManager = new GroupChatManager(groupChat);

		var conversationHistory = await adminAutoGenAgent.InitiateChatAsync(groupChatManager, input, maxRound: 40);

		var lastMessage = conversationHistory.Last();



	}

	private static Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin) > GetSKGroupChatAgents(WorkbookUpdateInteraction workbookInteraction,
		WorkbookInteractionBase workbookSupervision, WorkbookValidation workbookValidation)
	{
		var updaterKernel = InitSemanticKernel();
		var updaterPlugin = updaterKernel.ImportPluginFromObject(workbookInteraction);

		var coderAgent = new ChatCompletionAgent
		{
			Instructions = CoderAgentInstructions,
			Name = CoderAgentName,
			Kernel = updaterKernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
		};


		var supervisorKernel = InitSemanticKernel();
		var supervisorPlugin = supervisorKernel.ImportPluginFromObject(workbookSupervision);
		var coderSupervisorAgent = new ChatCompletionAgent
		{
			Instructions = ReviewerAgentInstructions,
			Name = ReviewerAgentName,
			Kernel = supervisorKernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.EnableKernelFunctions },
		};


		var validationKernel = InitSemanticKernel();
		var validationPlugin = validationKernel.ImportPluginFromObject(workbookValidation);

		var projectManagerAgent = new ChatCompletionAgent
		{
			Instructions = AdminAgentInstructions,
			Name = AdminAgentName,
			Kernel = validationKernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.EnableKernelFunctions },
		};

		var groupChatAgents = new Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin)>
		{
			{CoderAgentName, (coderAgent, updaterPlugin)},
			{ReviewerAgentName, (coderSupervisorAgent, supervisorPlugin)},
			{AdminAgentName, (projectManagerAgent, validationPlugin)}
		};
		return groupChatAgents;
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
				return Task.FromResult(agents.First(a => a.Name == AdminAgentName));
			}
			else
			{
				if (history.Last().AuthorName == CoderAgentName)
				{
					return Task.FromResult(agents.First(a => a.Name == ReviewerAgentName));
				}
				else
				{
					return Task.FromResult(agents.First(a => a.Name == CoderAgentName));
				}
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



