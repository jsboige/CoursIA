using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using System.Threading.Tasks;
using System.Collections.Generic;
using System.Linq;
using System.IO;
using System.Text.Json;
using SKernel = Microsoft.SemanticKernel.Kernel;

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

1. Éditer les **cellules de Markdown** pour présenter l’objectif et affiner la requête SPARQL (avec agrégats).
2. Renseigner et tester les **cellules de code** C#.  
3. Corriger d’éventuels bugs puis valider la **sortie graphique** finale.  

**Résultat attendu** :
  
1. Une requête complexe sur DBpedia (avec agrégats) correctement exécutée.  
2. Un graphique Plotly.Net **pertinent** reflétant les données issues de DBpedia.  
3. Des cellules Markdown expliquant la démarche, l’exemple de requête et la visualisation.";

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


	private const string DefaultGeneralGroupChatInstructions = "Assist in creating the following .NET interactive notebook, which includes a description of its objective.\nYou are part of a group chat with several assistants conversing and using function calls to incrementally improve, review and validate it.\n";


	public string CoderAgentName { get; set; } = "Coder_Agent";
	public string ReviewerAgentName { get; set; } = "Reviewer_Agent";
	public string AdminAgentName { get; set; } = "Admin_Agent";

	public string NotebookTaskDescription { get; set; }
	public string ToolsUsageInstructions { get; set; }
	public string GeneralGroupChatInstructions { get; set; } =
		@"You are part of a **group chat** involving multiple assistants (Coder, Reviewer, and Admin) who collaborate to create or update a .NET Interactive notebook. 
Each assistant has specific roles:

- **Coder** updates notebook cells (Markdown or code) by calling the provided functions.
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
		$@"You are the **Coder assistant**. Your task is to update and refine a .NET Interactive notebook incrementally, ensuring clarity, correctness, and functionality.

### General Guidelines:
1. **Markdown Cells**:
   - Use Markdown cells to **describe the task**, **provide context**, and **explain code logic**.
   - DO NOT INSERT CODE in Markdown cells. All functional code belongs in code cells.

2. **Code Cells**:
   - Write functional and executable code directly in **code cells**. Do not leave code cells empty before addressing following cells.
   - **Avoid duplicating code** between Markdown cells and code cells.
   - Check code for correctness within the .NET Interactive environment before submission.
   - Ensure code cells are functional by checking the returned output of eac

3. **Clear Separation**:
   - Markdown = Explanations, logic, and methodology.
   - Code Cells = Functional and executable code.

### Process:
1. Analyze the notebook's current state.
2. Add or modify cells as follows:
   - Use **Markdown cells** for textual content only.
   - Use **code cells** to execute functional code. Do not replicate this code in Markdown.
3. Ensure that:
   - Code cells are **non-empty** and contain executable, relevant code.
   - Markdown clearly describes the code and logic **without duplicating the actual code content**.
4. Validate the output of each cell and re-run if necessary.

### Key Errors to Avoid:
- Leaving code cells empty.
- Placing complete code examples in Markdown cells.
- Duplicating code between Markdown and code cells.

**Tool Usage**:
{DefaultToolsUsageInstructions}";


	public string ReviewerAgentInstructions { get; set; } =
		$@"You are the **Reviewer assistant**. Your role is to validate and provide feedback on the notebook updates made by the Coder assistant.

### Responsibilities:
1. Review updates to Markdown cells for:
   - Clarity, relevance, and correctness.
   - Logical flow of instructions or explanations.
2. Review updates to code cells for:
   - Syntax correctness and functionality.
   - Alignment with the notebook’s objectives (e.g., correct external data queries, appropriate visualizations).
3. Identify and point out missing or incomplete sections in the notebook.

### Process:
1. Call `RunNotebook()` to execute the entire notebook and analyze outputs.
2. Provide feedback on:
   - Errors or inconsistencies in Markdown and code cells.
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
   - Markdown cells are clear, well-structured, and relevant.
   - Code cells are correct, functional, and aligned with the notebook’s objectives.
3. Call `RunNotebook()` to validate the notebook outputs.

### Approval Criteria:
- All cells are correctly typed (Markdown or code).
- No errors remain in code cells.
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

