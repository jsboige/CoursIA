using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using Microsoft.SemanticKernel.Planning;

namespace MyIA.AI.Notebooks;
#pragma warning disable SKEXP0060
public class NotebookUpdater
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

	public NotebookUpdater(Kernel semanticKernel, string notebookPath, ILogger logger, int maxIterations = 5)
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
		Console.WriteLine("Lecture du contenu du notebook...");
		var notebookJson = File.ReadAllText(_notebookPath);

		Console.WriteLine("Appel de ChatGPT avec le workbook initialisé...");




		var plannerPrompt = $"Help create the following interactive .Net notebook, which contains a description of its purpose.\n" +
		                    $"Use function calling to improve and validate it with incremental edits:\n" +
		                    $"- Use the ReplaceWorkbookCell function to edit targeted cells within the notebook initially, and then ReplaceBlockInWorkbookCell or InsertInWorkbookCell as they grow in size. Pay attention to those 3 functions distinctive signatures to avoid strings mismatched or mis-replaced\n" +
		                    $"- Those functions do run the code cells by default, returning corresponding outputs, but you can also choose to restart the Kernel and run the entire notebook when needed.\n" +
		                    //$"- Make sure to always start editing Markdown cells to explain the following code, and to include comments and make use of output displays in your code cells for sanity checks of intermediate results, and state your current sub-goals in the accompanying message.\n" +
		                    $"- Continue to update the notebook until it runs without any error, the code cells are properly fed with actual code that fully accomplishes the requested task and the markdown cells with the appropriate documentation.\n" +
		                    $"- Concerning Nuget packages, note that you might find yourself in a tough spot if you start hallucinating Nuget packages. Pay special attention and don't mix-up package names and namespaces.\n" +
							$"\n\nHere is the starting notebook.\n{notebookJson}\nRemember, only once the workbook was run and thoroughly tested, documented and cleaned should you call the 'SendFinalAnswer' function.";
		
		_logger.LogInformation($"Sending prompt to planner...\n{plannerPrompt}");



		var result = await _planner.ExecuteAsync(_semanticKernel, plannerPrompt);

		_logger.LogInformation("Notebook mis à jour avec succès.");

		return result.FinalAnswer;
	}

}