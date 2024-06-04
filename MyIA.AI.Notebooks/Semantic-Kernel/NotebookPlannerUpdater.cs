using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using Microsoft.SemanticKernel.Planning;

namespace MyIA.AI.Notebooks;
#pragma warning disable SKEXP0060
public class NotebookPlannerUpdater
{
	private readonly FunctionCallingStepwisePlanner _planner;
	private readonly Kernel _semanticKernel;
	private readonly string _notebookPath;
	private readonly ILogger _logger;

	private static string GetPlanTemplate()
	{
		var planTemplate = File.ReadAllText("./Semantic-Kernel/Resources/generate_plan.yaml");
		return planTemplate;
	}

	private static string GetStepPromptTemplate()
	{
		var toReturn = File.ReadAllText("./Semantic-Kernel/Resources/StepPrompt.txt");
		return toReturn;
	}

	public NotebookPlannerUpdater(Kernel semanticKernel, string notebookPath, ILogger logger, int maxIterations = 5)
	{
		_semanticKernel = semanticKernel;
		_notebookPath = notebookPath;
		var options = new FunctionCallingStepwisePlannerOptions
		{
			MaxTokens = 100000,
			MaxTokensRatio = 0.3,
			MaxIterations = maxIterations,
			ExecutionSettings = new OpenAIPromptExecutionSettings
			{
				ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions,
			},
			GetInitialPlanPromptTemplate = GetPlanTemplate,
			GetStepPromptTemplate = GetStepPromptTemplate,
		};
		_planner = new FunctionCallingStepwisePlanner(options);
		_logger = logger;

		var workbookInteraction = new WorkbookInteraction(notebookPath, _logger);
		_semanticKernel.ImportPluginFromObject(workbookInteraction);
	}

	public async Task<string> UpdateNotebook()
	{
		Console.WriteLine("Reading notebook content...");
		var notebookJson = File.ReadAllText(_notebookPath);

		Console.WriteLine("Calling ChatGPT with initialized workbook...");

		var plannerPrompt = $"Assist in creating the following interactive .NET notebook, which includes a description of its purpose.\n" +
							$"Use function calls to incrementally improve and validate it:\n" +
							$"- Initially, use the ReplaceWorkbookCell function to edit targeted cells. As the notebook evolves, use ReplaceBlockInWorkbookCell or InsertInWorkbookCell. Pay attention to these functions' distinct signatures to avoid mismatches.\n" +
							$"- These functions execute the code cells by default, returning corresponding outputs. You can also choose to restart the kernel and run the entire notebook when necessary.\n" +
							$"- Continue updating the notebook until it runs without errors, with code cells correctly implementing the required tasks and markdown cells containing appropriate documentation.\n" +
							$"- Be cautious with NuGet packages to avoid mix-ups in package names and namespaces.\n" +
							$"\nHere is the starting notebook:\n{notebookJson}\nEnsure that the workbook is thoroughly tested, documented, and cleaned before calling the 'SendFinalAnswer' function.";

		_logger.LogInformation($"Sending prompt to planner...\n{plannerPrompt}");

		var result = await _planner.ExecuteAsync(_semanticKernel, plannerPrompt);

		_logger.LogInformation("Notebook successfully updated.");

		return result.FinalAnswer;
	}
}



