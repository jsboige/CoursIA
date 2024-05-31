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

		var plannerPrompt = $"Help create the following interactive .Net notebook, which contains a description of its purpose.\n Use function calling to improve and validate it with incremental edits:\n - Use the UpdateSmallWorkbookCell function to edit targeted cells within the notebook initially, and then UpdateLargeWorkbookCell as they grow in size. \n- Use the RunNotebook function on a regular basis after one large or several small edits to re-execute the notebook and produce outputs, checking for potential issues, and further edit faulty cells to fix all errors found in the json outputs.\n Make sure to also edit Markdown cells to explain your sub-goals, and to include display in your code cells for sanity checks of intermediate results.\n- Continue updating the notebook until it runs without any error and the code cells are filled with code that fully accomplishes the requested task.\n\n{notebookJson}\nRemember, only once the workbook was  run and thoroughly tested should you call the SendFinalAnswer function.";
		Console.WriteLine($"Envoi du prompt au planner...\n{plannerPrompt}");

		var result = await _planner.ExecuteAsync(_semanticKernel, plannerPrompt);

		Console.WriteLine("Notebook mis à jour avec succès.");

		return result.FinalAnswer;
	}

}