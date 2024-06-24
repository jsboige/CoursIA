using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Microsoft.SemanticKernel.ChatCompletion;

namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
public class AutoInvokeSKAgentsNotebookUpdater : NotebookUpdater
{
	public async Task UpdateNotebookWithAutoInvokeSKAgents()
	{
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(NotebookTaskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, logger);
		var workbookSupervision = new WorkbookInteractionBase(notebookPath, logger);
		var workbookValidation = new WorkbookValidation(notebookPath, logger);

		var groupChatAgents = GetSKGroupChatAgents(workbookInteraction, workbookSupervision, workbookValidation);

		var chat = new AgentGroupChat(groupChatAgents.Values.Select(tuple => (Agent)tuple.agent).ToArray())
		{
			ExecutionSettings = new()
			{
				TerminationStrategy = new NotebookTerminationStrategy { WorkbookValidation = workbookValidation, Updater = this},
				SelectionStrategy = new NotebookSelectionStrategy { WorkbookUpdateInteraction = workbookInteraction, Updater = this },
			},
			LoggerFactory = new DisplayLogger(nameof(Program), LogLevel.Trace)
		};

		var input = $"\nHere is the starting notebook:\n{notebookJson}\nEnsure that the workbook is thoroughly tested, documented, and cleaned before calling the 'ApproveNotebook' function.";
		chat.AddChatMessage(new ChatMessageContent(AuthorRole.User, input));
		Console.WriteLine($"# {AuthorRole.User}: '{NotebookTaskDescription}'");

		await foreach (var content in chat.InvokeAsync())
		{
			Console.WriteLine($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
		}

		Console.WriteLine($"# IS COMPLETE: {chat.IsComplete}");
	}

	[Experimental("SKEXP0110")]
	private class NotebookTerminationStrategy : TerminationStrategy
	{

		public NotebookUpdater Updater { get; set; }

		public WorkbookValidation WorkbookValidation { get; set; }

		protected override Task<bool> ShouldAgentTerminateAsync(Agent agent, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken)
		{
			return Task.FromResult(WorkbookValidation.IsApproved);
		}
	}

	[Experimental("SKEXP0110")]
	public class NotebookSelectionStrategy : SelectionStrategy
	{
		public NotebookUpdater Updater { get; set; }

		public WorkbookUpdateInteraction WorkbookUpdateInteraction { get; set; }

		public override Task<Agent> NextAsync(IReadOnlyList<Agent> agents, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken = new CancellationToken())
		{
			if (WorkbookUpdateInteraction.IsPendingApproval)
			{
				return Task.FromResult(agents.First(a => a.Name == Updater.AdminAgentName));
			}
			else
			{
				if (history.Last().AuthorName == Updater.CoderAgentName)
				{
					return Task.FromResult(agents.First(a => a.Name == Updater.ReviewerAgentName));
				}
				else
				{
					return Task.FromResult(agents.First(a => a.Name == Updater.CoderAgentName));
				}
			}
		}
	}
}
