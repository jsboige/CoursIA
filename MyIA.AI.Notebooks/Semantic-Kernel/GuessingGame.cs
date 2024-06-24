using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.ChatCompletion;
using System.ComponentModel;
using System.Diagnostics.CodeAnalysis;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Humanizer;

namespace MyIA.AI.Notebooks
{
	[Experimental("SKEXP0110")]
	public static class GuessingGame
	{
		public static async Task RunGameAsync(ILogger logger, Func<Kernel> initSemanticKernel)
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
				Kernel = initSemanticKernel(),
			};

			ChatCompletionAgent agentWriter = new()
			{
				Instructions = laurentJalabertPrompt,
				Name = "Laurent_Jalabert",
				Kernel = initSemanticKernel(),
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
				logger.LogInformation($"# {content.Role} - {content.AuthorName ?? "*"}: '{content.Content}'");
			}
		}

		private class ApprovalTerminationStrategy : TerminationStrategy
		{
			private readonly string _motADeviner;

			public ApprovalTerminationStrategy(string motADeviner)
			{
				_motADeviner = motADeviner;
			}

			protected override Task<bool> ShouldAgentTerminateAsync(Agent agent, IReadOnlyList<ChatMessageContent> history, CancellationToken cancellationToken)
			{
				return Task.FromResult(history[^1].Content?.Contains(_motADeviner, StringComparison.OrdinalIgnoreCase) ?? false);
			}
		}
	}
}
