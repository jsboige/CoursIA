using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Connectors.OpenAI;

namespace MyIA.AI.Notebooks
{
	[Experimental("SKEXP0110")]
	public class NotebookUpdater
	{
		protected ILogger logger;

		public string CoderAgentName { get; set; } = "Coder_Agent";
		public string ReviewerAgentName { get; set; } = "Reviewer_Agent";
		public string AdminAgentName { get; set; } = "Admin_Agent";

		public static string ToolsUsageInstructions { get; set; } =
			"When using tools:\n- Use as many simultaneous tool calls as possible to save on conversational tokens,\n" +
			"- Auto-invoke is enabled, meaning using tools will have a dedicated 'tool' agent further the conversation by answering your tool call messages with the corresponding answers, leaving you other opportunities to call tools, before you resume the normal conversation by answering without making any more tool call.\n" +
			"- Do not use more than 5 consecutive rounds of tool calling messages, monopolising all the conversation tokens discussing with tools and yourself. This will let other agents take the opportunity to reflect on your updates, and you will get other rounds of tool call updates to finish up with a fresher perspective.\n" +
			"- Do leave the chat text response empty when calling tools, because function calls with empty messages and the tool responses will be considered internal conversation and removed from the group chat, which is a good thing to save on tokens.\n" +
			"- When you are finished calling tools, do provide a text message explaining the sequence of calls and the current state since your tool calls and answers will be removed for other agents.\n";

		public static string GeneralGroupChatInstructions { get; set; } =
			"Assist in creating the following .NET interactive notebook, which includes a description of its objective.\n" +
			"You are part of a group chat with several assistants conversing and using function calls to incrementally improve, review and validate it.\n";

		public string CoderAgentInstructions
		{ get; set; } = $"You are an assistant coder. Your role is to update a notebook as instructed, using provided functions.\n" +
		                $"{GeneralGroupChatInstructions}" +
		                $"- Initially, use the ReplaceWorkbookCell function to edit targeted cells. As the notebook evolves, use ReplaceBlockInWorkbookCell or InsertInWorkbookCell for large cells. Pay attention to these functions' distinct signatures to avoid mismatches.\n" +
		                $"- These functions execute the code cells by default, returning corresponding outputs. You can also choose to restart the kernel, run and return the entire notebook when necessary, but keep that use limited to the cases where the state is unclear from the conversation, because it shoots up the token budget for the agent conversation.\n" +
		                $"- Try to fix errors, to feed code cells by correctly implementing the required tasks and to feed markdown cells with thought process and appropriate documentation.\n" +
		                $"- Be cautious with NuGet packages to avoid mix-ups in package names and namespaces, and use display(myObj) or myObj.Display() to output intermediate results.\n" +
		                $"- When you don't know why a call failed because a cell was not found, if you get stuck with bugs over several fixing attempts, or simply every once in while for external feedback from other assistants, simply return a message that explains the current status without doing any more function calls. \n" +
		                $"- When you gathered enough positive feedback and you think the notebook can be validated, that is, once you were able to state that all cells content and outputs are giving satisfaction, then use the SubmitNotebook to submit your work for a final round of validation.\n" +
		                $"{ToolsUsageInstructions}";

		public string ReviewerAgentInstructions { get; set; } = $"You are an assistant coder supervisor. Your role is to review and comment on the updates performed by the coder assistant, and to unstuck him if needed.\n" +
		                                                            $"{GeneralGroupChatInstructions}" +
		                                                            $"If the ongoing conversation isn't clear enough to assess the current state of the notebook, you can use the RunNotebook function to run the notebook from scratch and obtain the resulting json with outputs.\n" +
		                                                            $"Answer with comments of what's been done right and wrong and suggestions to get going, in order to help the coder assistant making the appropriate updates and fixes. Pay attention to the error outputs and make sure the objective is being properly implemented.\n" +
		                                                            $"{ToolsUsageInstructions}";

		protected string AdminAgentInstructions { get; set; } =
			$"You are a strict project manager with high coding skills, in charge of managing a development task. You oversee development progress and determine when the task is complete.\n" +
			$"{GeneralGroupChatInstructions}" +
			$"- Use the RunNotebook function to run and return the outputs of the current notebook.\n" +
			$"- Use the ApproveNotebook function once the notebook was tested with appropriate outputs.\n" +
			$"- Before you approve the notebook make sure to explicitly review all cells, the validity of their outputs and make a clear statement explaining why you think the notebook's goal was completed, based on the cells' content and outputs.\n" +
			$"{ToolsUsageInstructions}";

		public string NotebookTaskDescription { get; set; } = "Créer un notebook .Net interactive permettant de requêter DBPedia, utilisant les package Nuget dotNetRDF et XPlot.Plotly.Interactive. Commencer par éditer les cellules de Markdown pour définir et affiner l'exemple de requête dont le graphique final sera le plus pertinent. Choisir un exemple de requête complexe, manipulant des aggrégats, qui pourront être synthétisés dans un graphique. Une fois les cellules de code alimentées et les bugs corrigés, s'assurer que la sortie de la cellule générant le graphique est conforme et pertinente.";

		public NotebookUpdater()
		{
			logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);
		}

		protected Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin)> GetSKGroupChatAgents(
			WorkbookUpdateInteraction workbookInteraction,
			WorkbookInteractionBase workbookSupervision,
			WorkbookValidation workbookValidation)
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
				ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
			};

			var validationKernel = InitSemanticKernel();
			var validationPlugin = validationKernel.ImportPluginFromObject(workbookValidation);

			var projectManagerAgent = new ChatCompletionAgent
			{
				Instructions = AdminAgentInstructions,
				Name = AdminAgentName,
				Kernel = validationKernel,
				ExecutionSettings = new OpenAIPromptExecutionSettings() { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
			};

			return new Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin)>
			{
				{CoderAgentName, (coderAgent, updaterPlugin)},
				{ReviewerAgentName, (coderSupervisorAgent, supervisorPlugin)},
				{AdminAgentName, (projectManagerAgent, validationPlugin)}
			};
		}

		protected Kernel InitSemanticKernel()
		{
			Console.WriteLine("Initialisation...");

			var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();

			var builder = Kernel.CreateBuilder();

			builder.Services.AddLogging(loggingBuilder =>
			{
				LoggingBuilderExtensions.AddProvider(loggingBuilder, new DisplayLoggerProvider(LogLevel.Trace));
			});

			if (useAzureOpenAI)
				builder.AddAzureOpenAIChatCompletion(model, azureEndpoint, apiKey);
			else
				builder.AddOpenAIChatCompletion(model, apiKey, orgId);

			return builder.Build();
		}

		protected void SetStartingNotebook(string taskDescription, string notebookPath)
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
}

