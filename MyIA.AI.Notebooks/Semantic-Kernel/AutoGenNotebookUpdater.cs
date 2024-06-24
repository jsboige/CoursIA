using System.Diagnostics.CodeAnalysis;
using AutoGen.Core;
using AutoGen.OpenAI;
using AutoGen.OpenAI.Extension;
using AutoGen.SemanticKernel;
using Azure.AI.OpenAI;

namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
public class AutoGenNotebookUpdater : NotebookUpdater
{
	public async Task UpdateNotebookWithAutoGenSKAgents()
	{
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(NotebookTaskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, logger);
		var workbookSupervision = new WorkbookInteractionBase(notebookPath, logger);
		var workbookValidation = new WorkbookValidation(notebookPath, logger);

		var groupChatAgents = GetSKGroupChatAgents(workbookInteraction, workbookSupervision, workbookValidation);
		var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();
		var openAIClient = new OpenAIClient(apiKey);

		var coderKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[CoderAgentName].agent.Kernel, groupChatAgents[CoderAgentName].plugin);
		var coderAutoGenAgent = new OpenAIChatAgent(
				openAIClient: openAIClient,
				name: CoderAgentName,
				systemMessage: CoderAgentInstructions,
				modelName: model)
			.RegisterMessageConnector()
			.RegisterMiddleware(coderKernelPluginMiddleware)
			.RegisterPrintMessage();
		//var coderAutoGenAgent = new SemanticKernelChatCompletionAgent(groupChatAgents[CoderAgentName].agent)
		//	.RegisterPrintMessage()
		//	.RegisterMiddleware(coderKernelPluginMiddleware)
		//	.RegisterMiddleware(messageConnector);

		var reviewerKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[ReviewerAgentName].agent.Kernel, groupChatAgents[ReviewerAgentName].plugin);
		var reviewerAutoGenAgent = new OpenAIChatAgent(
				openAIClient: openAIClient,
				name: ReviewerAgentName,
				systemMessage: ReviewerAgentInstructions,
				modelName: model)
			.RegisterMessageConnector()
			.RegisterMiddleware(reviewerKernelPluginMiddleware)
			.RegisterPrintMessage();
		//var reviewerAutoGenAgent = new SemanticKernelChatCompletionAgent(groupChatAgents[ReviewerAgentName].agent)
		//	.RegisterPrintMessage()
		//	.RegisterMiddleware(reviewerKernelPluginMiddleware)
		//	.RegisterMiddleware(messageConnector);

		var adminKernelPluginMiddleware = new KernelPluginMiddleware(groupChatAgents[AdminAgentName].agent.Kernel, groupChatAgents[AdminAgentName].plugin);
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
			.RegisterPrintMessage();
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

		var admin2CoderTransition = Transition.Create(from: adminAutoGenAgent, to: coderAutoGenAgent, canTransitionAsync: async (from, to, messages) => !workbookValidation.IsApproved);
		var reviewer2CoderTransition = Transition.Create(reviewerAutoGenAgent, coderAutoGenAgent);
		var coder2ReviewerTransition = Transition.Create(from: coderAutoGenAgent, to: reviewerAutoGenAgent, canTransitionAsync: async (from, to, messages) => !workbookInteraction.IsPendingApproval);
		var coder2AdminTransition = Transition.Create(from: coderAutoGenAgent, to: reviewerAutoGenAgent, canTransitionAsync: async (from, to, messages) => workbookInteraction.IsPendingApproval);

		var workflow = new Graph(
		[
			admin2CoderTransition,
			coder2ReviewerTransition,
			reviewer2CoderTransition,
		]);

		var groupChat = new GroupChat(admin: adminAutoGenAgent, workflow: workflow, members: [adminAutoGenAgent, coderAutoGenAgent, reviewerAutoGenAgent]);
		adminAutoGenAgent.SendIntroduction("Welcome to my group, please work together to resolve my task", groupChat);
		coderAutoGenAgent.SendIntroduction("I will incrementally update the markdown and code cells of the notebook to resolve task", groupChat);
		reviewerAutoGenAgent.SendIntroduction($"I will help {CoderAgentName} by reviewing his work", groupChat);

		var input = $"\nHere is the starting notebook:\n{notebookJson}\n Now let's fill up those cells.";

		var groupChatManager = new GroupChatManager(groupChat);

		var conversationHistory = await adminAutoGenAgent.InitiateChatAsync(groupChatManager, input, maxRound: 40);

		var lastMessage = conversationHistory.Last();
	}
}
