using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using MyIA.AI.Notebooks.Config;
using SKernel = Microsoft.SemanticKernel.Kernel;

namespace MyNotebookLib;

public abstract class NotebookUpdaterBase
{
	protected ILogger Logger;
	protected SKernel SemanticKernel;
	protected string NotebookPath;
	public string NotebookTemplatePath { get; set; } = "./Semantic-Kernel/Workbook-Template.ipynb";

	protected int MaxRetries = 3;


	private const string DefaultNotebookTaskDescription =
		@"Créer un notebook .NET Interactive capable de requêter **DBpedia** via une requête SPARQL et d’afficher un **graphique** final avec [`dotNetRDF`](https://www.nuget.org/packages/dotNetRDF/) et [`Plotly.Net`](https://www.nuget.org/packages/Plotly.NET/).  

**Étapes suggérées** :

1. Renseigner et tester les **cellules de code** C#.  
2. Corriger d’éventuels bugs qui apparaissent des les sorties de cellule de code.
3. Valider les sorties de cellule de code intermédiaires
3. Valider la **sortie graphique** finale.  

**Résultat attendu** :
  
1. Une requête complexe sur DBpedia (avec agrégats) correctement exécutée.  
2. Un graphique Plotly.Net **pertinent** reflétant les données issues de DBpedia.";

	private const string DefaultToolsUsageInstructions =
		@"**Tool Usage Guidelines**:

1. **Simultaneous Calls**: 
   - Whenever possible, group multiple tool calls into one round to save conversational tokens.
   - 'Auto-invoke' is enabled, meaning a dedicated 'tool' agent will respond to your tool call messages.

2. **Limit Consecutive Rounds**:
   - DO NOT EXCEED **5 consecutive rounds** of tool-calling messages. 
   - This helps avoid token overuse and gives other agents the opportunity to provide feedback.

3. **Empty Chat Response**: 
   - Leave the main chat text **empty** when calling tools. 
   - Tool calls and responses are considered *internal conversation* and will be removed from the group chat log (saving tokens).

4. **Final Summary**:
   - Once you finish calling tools, provide a **text message** describing the sequence of calls made and the current state of the notebook.
   - Remember: all tool call details and responses are stripped from the final conversation.

Follow these rules to optimize usage and keep the conversation log efficient.";


	//private const string DefaultGeneralGroupChatInstructions = "Assist in creating the following .NET interactive notebook, which includes a description of its objective.\nYou are part of a group chat with several assistants conversing and using function calls to incrementally improve, review and validate it.\n";


	public string CoderAgentName { get; set; } = "Coder_Agent";
	public string ReviewerAgentName { get; set; } = "Reviewer_Agent";
	public string AdminAgentName { get; set; } = "Admin_Agent";

	public string NotebookTaskDescription { get; set; }
	public string ToolsUsageInstructions { get; set; }
	public string GeneralGroupChatInstructions { get; set; } =
		@"You are part of a **group chat** involving multiple assistants (Coder, Reviewer, and Admin) who collaborate to create or update a .NET Interactive notebook (either in c# or in python through an externel kernel import). 
Each assistant has specific roles:

- **Coder** updates notebook code cells by calling the provided functions.
- **Reviewer** reviews changes, provides feedback, and can run the entire notebook for diagnostics.
- **Admin** oversees the final validation and can approve the notebook once it meets the requirements.

**Guidelines**:
- Maintain clarity between Markdown and code cells. 
- Follow the naming conventions and parameters of the provided notebook functions (e.g., ReplaceWorkbookCell).
- Avoid unnecessary function calls or partial updates that might cause confusion.   

Use the conversation to **incrementally improve** the notebook until the Admin agent decides to approve it. 
Any direct modifications must be done via the proper function calls. 
Group chat messages should remain concise and focused on the task. 
Tool usage instructions apply to any function calls you make.";

	public string CoderAgentInstructions { get; set; } =
		$@"### General Guidelines:
1. **Markdown Cells**:
   - **IGNORE** Markdown cells. You are strictly tasked with updating **code cells**.

2. **Code Cells**:
   - Update only **code cells** identified by existing content strings (e.g., comments or placeholders).
   - Ensure that all updated cells contain functional, executable code.
   - Validate the outputs of the code cells and fix any errors.

3. **Identification**:
   - Use existing comments or initial placeholders to identify the relevant code cells.
   - Do not attempt to modify or interact with Markdown content under any circumstance.
   - Note that sometimes cell or content identification may fail for various reasons resulting in missed updates. Notification will indicate when such a failure occurs. When and only when that happens, renew your function calls with the appropriate fixes and don't take your updates for granted unless you were able to double-check the outputs resulting from their execution.
   - Conversely, pay attention to your successful updates. Notification will indicate new cell content: don't try to replace content that was already replaced, and be careful not to duplicate your function calls or the cells content one way or another, as this may lead to unnecessary updates or errors.
   - If you are uncertain about the content of a cell, don't hesitate to run the entire notebook to verify the cells and outputs.
	

### Key Errors to Avoid:
- Leaving code cells empty.
- Misidentifying a Markdown cell as a code cell.
- Duplicating code in code cells.
- When in doubt, stop function calling and let the reviewer assess the situation.


**Tool Usage**:
{DefaultToolsUsageInstructions}";


	public string ReviewerAgentInstructions { get; set; } =
		$@"You are the **Reviewer assistant**. Your role is to validate and provide feedback on the notebook updates made by the Coder assistant.

### Responsibilities:
1. Review updates to code cells for:
   - Syntax correctness and functionality.
   - Alignment with the notebook’s objectives (e.g., correct external data queries, appropriate visualizations).
   - Valid outputs without errors or exceptions.
2. Identify and point out missing or incomplete sections in the notebook.

### Process:
1. Call `RunNotebook()` to execute the entire notebook and analyze outputs.
2. Provide feedback on:
   - Errors or inconsistencies in code cells.
   - Suggestions for improvement or corrections.
3. Collaborate with the Coder assistant to refine the notebook.

### Key Points:
- Provide actionable feedback in a concise manner.
- Highlight misplaced or unclear content.
- Ensure the notebook is incrementally improved and ready for Admin validation.

**Tool usage**:
{DefaultToolsUsageInstructions}";


	public string AdminAgentInstructions { get; set; } =
		$@"You are the **Admin assistant**. Your role is to oversee and validate the final notebook.

### Responsibilities:
1. Monitor the updates and feedback provided by the Coder and Reviewer agents.
2. Verify that the notebook meets all task requirements:
   - Code cells are correct, functional, and aligned with the notebook’s objectives. No errors remain in code cells outputs.
3. Call `RunNotebook()` to validate the notebook outputs.

### Approval Criteria:
- All code cells are correctly typed.
- No errors remain in code cells outputs.
- The notebook achieves the stated objectives and is complete.

### Key Points:
- Collaborate with the other agents only when necessary.
- Approve the notebook with `ApproveNotebook()` once it satisfies all criteria.
- Do not approve the notebook if errors or incomplete sections are present.

**Tool usage**:
{DefaultToolsUsageInstructions}";



	public NotebookUpdaterBase(string notebookPath, ILogger logger)
	{
		NotebookPath = notebookPath;
		Logger = logger;
		SemanticKernel = InitSemanticKernel();

		// Initialize properties with default values
		NotebookTaskDescription = DefaultNotebookTaskDescription;
		ToolsUsageInstructions = DefaultToolsUsageInstructions;
	}

	protected SKernel InitSemanticKernel()
	{
		var (useAzureOpenAI, model, azureEndpoint, apiKey, orgId) = Settings.LoadFromFile();
		var builder = SKernel.CreateBuilder();
		builder.Services.AddLogging(loggingBuilder => loggingBuilder.AddProvider(new DisplayLoggerProvider(LogLevel.Trace)));

		if (useAzureOpenAI)
			builder.AddAzureOpenAIChatCompletion(model, azureEndpoint, apiKey);
		else
			builder.AddOpenAIChatCompletion(model, apiKey, orgId);

		return builder.Build();
	}

	public void SetStartingNotebookFromTemplate(string taskDescription)
	{
		// Échapper correctement avec Newtonsoft.Json
		taskDescription = Newtonsoft.Json.JsonConvert.ToString(taskDescription);

		// Retirer les guillemets ajoutés autour de la chaîne
		taskDescription = taskDescription.Substring(1, taskDescription.Length - 2);

		string notebookContent;
		if (File.Exists(NotebookPath))
		{
			notebookContent = File.ReadAllText(NotebookPath);
		}
		else if (File.Exists(NotebookTemplatePath))
		{
			notebookContent = File.ReadAllText(NotebookTemplatePath);
		}
		else
		{
			throw new FileNotFoundException($"Neither the notebook file at '{NotebookPath}' nor the template file at '{NotebookTemplatePath}' exists.");
		}

		notebookContent = notebookContent.Replace("{{TASK_DESCRIPTION}}", taskDescription);

		var dirNotebook = new FileInfo(NotebookPath).Directory;
		if (!dirNotebook.Exists) dirNotebook.Create();
		File.WriteAllText(NotebookPath, notebookContent);
	}

	public async Task UpdateNotebookAsync()
	{
		for (int i = 0; i < MaxRetries; i++)
		{
			try
			{
				await PerformNotebookUpdateAsync();
				break; // Exit loop if successful
			}
			catch (Exception ex)
			{
				Logger.LogError(ex, "Error updating notebook. Retrying...");
				if (i == MaxRetries - 1)
				{
					Logger.LogError("Max retries reached. Update failed.");
					throw;
				}
			}
		}
	}

	protected abstract Task PerformNotebookUpdateAsync();
}