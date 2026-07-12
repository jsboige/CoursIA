using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Microsoft.SemanticKernel.ChatCompletion;
using Microsoft.SemanticKernel.Connectors.OpenAI;

namespace MyNotebookLib;

[Experimental("SKEXP0110")]
public class AutoInvokeSKAgentsNotebookUpdater(string notebookPath, ILogger logger)
	: NotebookUpdaterBase(notebookPath, logger)
{
	protected override async Task PerformNotebookUpdateAsync()
	{
		var notebookJson = File.ReadAllText(NotebookPath);

		var workbookInteraction = new WorkbookUpdateInteraction(NotebookPath, Logger);
		var workbookSupervision = new WorkbookInteractionBase(NotebookPath, Logger);
		var workbookValidation = new WorkbookValidation(NotebookPath, Logger);

		var groupChatAgents = GetSKGroupChatAgents(workbookInteraction, workbookSupervision, workbookValidation);

		var chat = new AgentGroupChat(groupChatAgents.Values.Select(tuple => (Agent)tuple.agent).ToArray())
		{
			ExecutionSettings = new()
			{
				TerminationStrategy = new NotebookTerminationStrategy { WorkbookValidation = workbookValidation, Updater = this },
				SelectionStrategy = new NotebookSelectionStrategy { WorkbookUpdateInteraction = workbookInteraction, Updater = this },
			},
			LoggerFactory = new DisplayLogger(nameof(AutoInvokeSKAgentsNotebookUpdater), LogLevel.Trace)
		};

		var input = $"\nHere is the starting notebook:\n{notebookJson}\nEnsure that the workbook is thoroughly tested, documented, and cleaned before calling the 'ApproveNotebook' function.";
		chat.AddChatMessage(new ChatMessageContent(AuthorRole.User, input));
		//Console.WriteLine($"# {AuthorRole.User}: '{NotebookTaskDescription}'");

		await foreach (var content in chat.InvokeAsync())
		{
			Console.WriteLine($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
		}

		Console.WriteLine($"# IS COMPLETE: {chat.IsComplete}");
	}

	private Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin)> GetSKGroupChatAgents(
		WorkbookUpdateInteraction workbookInteraction,
		WorkbookInteractionBase workbookSupervision,
		WorkbookValidation workbookValidation)
	{
		var coderAgent = CreateAgent(CoderAgentName, CoderAgentInstructions, workbookInteraction);
		var reviewerAgent = CreateAgent(ReviewerAgentName, ReviewerAgentInstructions, workbookSupervision);
		var adminAgent = CreateAgent(AdminAgentName, AdminAgentInstructions, workbookValidation);

		return new Dictionary<string, (ChatCompletionAgent agent, KernelPlugin plugin)>
		{
			{ CoderAgentName, coderAgent },
			{ ReviewerAgentName, reviewerAgent },
			{ AdminAgentName, adminAgent }
		};
	}

	private (ChatCompletionAgent agent, KernelPlugin plugin) CreateAgent(string name, string instructions, object pluginObject)
	{
		var kernel = InitSemanticKernel();
		var plugin = kernel.ImportPluginFromObject(pluginObject);

		var agent = new ChatCompletionAgent
		{
			Instructions = instructions,
			Name = name,
			Kernel = kernel,
			ExecutionSettings = new OpenAIPromptExecutionSettings { ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions },
		};

		return (agent, plugin);
	}

	private class NotebookTerminationStrategy : TerminationStrategy
	{
		public NotebookUpdaterBase Updater { get; set; }
		public WorkbookValidation WorkbookValidation { get; set; }

		protected override Task<bool> ShouldAgentTerminateAsync(Agent agent, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken)
		{
			return Task.FromResult(WorkbookValidation.IsApproved);
		}
	}

	private class NotebookSelectionStrategy : SelectionStrategy
	{
		public NotebookUpdaterBase Updater { get; set; }
		public WorkbookUpdateInteraction WorkbookUpdateInteraction { get; set; }

		public override Task<Agent> NextAsync(IReadOnlyList<Agent> agents, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken = new CancellationToken())
		{
			if (WorkbookUpdateInteraction.IsPendingApproval)
			{
				return Task.FromResult(agents.First(a => a.Name == Updater.AdminAgentName));
			}
			else
			{
				return Task.FromResult(history.Last().AuthorName == Updater.CoderAgentName
					? agents.First(a => a.Name == Updater.ReviewerAgentName)
					: agents.First(a => a.Name == Updater.CoderAgentName));
			}
		}
	}
}