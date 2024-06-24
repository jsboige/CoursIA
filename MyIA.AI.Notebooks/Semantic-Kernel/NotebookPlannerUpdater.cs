using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using Microsoft.SemanticKernel.Planning;

namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
public class NotebookPlannerUpdater : NotebookUpdater
{
	private readonly FunctionCallingStepwisePlanner _planner;
	private readonly Kernel _semanticKernel;

	public NotebookPlannerUpdater(string notebookPath, ILogger objLogger, int maxIterations = 5)
	{
		var options = new FunctionCallingStepwisePlannerOptions
		{
			MaxTokens = 100000,
			MaxTokensRatio = 0.3,
			MaxIterations = maxIterations,
			ExecutionSettings = new OpenAIPromptExecutionSettings
			{
				ToolCallBehavior = ToolCallBehavior.AutoInvokeKernelFunctions,
			},
			GetInitialPlanPromptTemplate = () => File.ReadAllText("./Semantic-Kernel/Resources/generate_plan.yaml"),
			GetStepPromptTemplate = () => File.ReadAllText("./Semantic-Kernel/Resources/StepPrompt.txt"),
		};
		_semanticKernel = InitSemanticKernel();
		var workbookInteraction = new WorkbookUpdateInteraction(notebookPath, logger);
		_semanticKernel.ImportPluginFromObject(workbookInteraction);
		_planner = new FunctionCallingStepwisePlanner(options);
		this.logger = objLogger;
	}

	public async Task UpdateNotebook()
	{
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		SetStartingNotebook(NotebookTaskDescription, notebookPath);
		var notebookJson = File.ReadAllText(notebookPath);

		var plannerPrompt = $"Assist in creating the following interactive .NET notebook, which includes a description of its purpose.\n" +
							$"- Initially, use the ReplaceWorkbookCell function to edit targeted cells. As the notebook evolves, use ReplaceBlockInWorkbookCell or InsertInWorkbookCell.\n" +
							$"- These functions execute the code cells by default, returning corresponding outputs. You can also choose to restart the kernel and run the entire notebook when necessary.\n" +
							$"- Continue updating the notebook until it runs without errors, with code cells correctly implementing the required tasks and markdown cells containing appropriate documentation.\n" +
							$"- Be cautious with NuGet packages to avoid mix-ups in package names and namespaces.\n" +
							$"\nHere is the starting notebook:\n{notebookJson}\nEnsure that the workbook is thoroughly tested, documented, and cleaned before calling the 'SendFinalAnswer' function.";

		logger.LogInformation($"Sending prompt to planner...\n{plannerPrompt}");

		var result = await _planner.ExecuteAsync(_semanticKernel, plannerPrompt);

		logger.LogInformation("Notebook successfully updated.");

		Console.WriteLine($"Résultat de l'exécution du notebook :\n{result.FinalAnswer}");
	}
}
