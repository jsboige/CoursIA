using System.ComponentModel;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Web;
using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.Commands;
using Microsoft.DotNet.Interactive.CSharp;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Documents.Jupyter;
using Microsoft.DotNet.Interactive.Jupyter;
using Microsoft.DotNet.Interactive.PackageManagement;
using Microsoft.Extensions.Logging;
using Microsoft.ML.Probabilistic.Distributions.Kernels;
using Microsoft.SemanticKernel;

public class WorkbookInteractionBase
{
	protected const string uniqueContentDescription = "A short string from the cell to update (e.g., a title in a markdown cell or a comment in a code cell) that is unique across all cells in the notebook";
	protected const string restartKernelDescription = "Whether to restart the kernel and reset the entire notebook from the beginning instead of just running the cell";

	private string _notebookPath;
	private NotebookExecutor _executor;
	private int _iterationCount = 0;
	protected ILogger _logger;

	public string PythonKernelSpec { get; set; } = "python3";

	public WorkbookInteractionBase(string notebookPath, ILogger logger)
	{
		_notebookPath = notebookPath;
		_logger = logger;
		// On ne fait pas InitializeExecutor() immédiatement 
		// car on veut d’abord charger le notebook pour déterminer son type.
	}

	/// <summary>
	/// Lit le notebook, détecte s'il est Python ou C#, puis initialise l'executor approprié
	/// </summary>
	private async Task InitializeExecutorIfNeeded()
	{
		if (_executor != null)
		{
			// Déjà initialisé
			return;
		}

		var notebook = await LoadNotebookAsync();
		var kernelSpec = notebook.Metadata.TryGetValue("kernelspec", out var rawKernelspec)
			? rawKernelspec as Dictionary<string, object>
			: null;

		string language = kernelSpec?.GetValueOrDefault("language")?.ToString()?.ToLowerInvariant() ?? "";

		// Cas 1: Notebook Python (ou jugé Python)
		if (language.Contains("python"))
		{
			_logger.LogInformation("Notebook appears to be Python; connecting Python kernel.");
			await InitializePythonExecutor();
		}
		// Cas 2: Notebook .NET / C#
		else
		{
			_logger.LogInformation("Notebook appears to be C# or .NET by default.");
			InitializeCSharpExecutor();
		}
	}

	/// <summary>
	/// Initialise un kernel Python unique, via la directive #!connect jupyter
	/// </summary>
	private async Task InitializePythonExecutor()
	{
		var compositeKernel = new CompositeKernel();
		// On se connecte uniquement au kernel Python
		await compositeKernel.SendAsync(new SubmitCode($"#!connect jupyter --kernel-name pythonkernel --kernel-spec {PythonKernelSpec}"));
		_executor = new NotebookExecutor(compositeKernel, _logger);
	}

	/// <summary>
	/// Initialise un kernel C# unique
	/// </summary>
	private void InitializeCSharpExecutor()
	{
		var cSharpKernel = new CSharpKernel()
			.UseKernelHelpers()
			.UseWho()
			.UseValueSharing()
			.UseImportMagicCommand()
			.UseDefaultMagicCommands()
			.UseJupyterHelpers();

		cSharpKernel.UseNugetDirective((k, resolvedPackageReference) =>
		{
			k.AddAssemblyReferences(resolvedPackageReference.SelectMany(r => r.AssemblyPaths));
			return Task.CompletedTask;
		}, false);

		var compositeKernel = new CompositeKernel { cSharpKernel };
		compositeKernel.DefaultKernelName = "csharp";

		compositeKernel.AddConnectDirective(
			new ConnectJupyterKernelDirective()
				.AddConnectionOptions(new JupyterHttpKernelConnectionOptions())
				.AddConnectionOptions(new JupyterLocalKernelConnectionOptions()));

		_executor = new NotebookExecutor(compositeKernel, _logger);
	}

	protected async Task<InteractiveDocument> LoadNotebookAsync()
	{
		return await InteractiveDocument.LoadAsync(new FileInfo(_notebookPath));
	}

	private void SaveNotebook(InteractiveDocument notebook)
	{
		var notebookJson = notebook.ToJupyterJson();
		File.WriteAllText(_notebookPath, notebookJson);
	}

	private string ExtractCellOutput(string notebookJson, int cellIndex)
	{
		var cell = ExtractCell(notebookJson, cellIndex);
		if (!cell.TryGetProperty("outputs", out var outputs))
		{
			return string.Empty;
		}
		return outputs.GetRawText();
	}

	private JsonElement ExtractCell(string notebookJson, int cellIndex)
	{
		var document = JsonDocument.Parse(notebookJson);
		var cell = document.RootElement.GetProperty("cells")[cellIndex];
		return cell;
	}

	public static string DecodeValue(string newValue)
	{
		newValue = Regex.Unescape(newValue);
		newValue = HttpUtility.HtmlDecode(newValue);
		newValue = HttpUtility.UrlDecode(newValue);
		return newValue;
	}

	private int _blindUpdatesCounter = 0;

	protected async Task UpdateCellAsync(
		string uniqueContent,
		Func<InteractiveDocumentElement, string> updateFunc,
		StringBuilder returnMessage,
		bool runNotebook,
		bool returnNotebook)
	{
		// Initialise l'executor en fonction du type du notebook
		await InitializeExecutorIfNeeded();

		var notebook = await LoadNotebookAsync();
		var cell = notebook.Elements.FirstOrDefault(e => e.Contents.Contains(uniqueContent));
		if (cell == null)
		{
			throw new ArgumentException($"Cell with identifying string '{uniqueContent}' not found in notebook.");
		}

		returnMessage.AppendLine($"Successfully identified cell with unique string:\n{uniqueContent}\n");

		var cellIndex = notebook.Elements.IndexOf(cell);
		var newContent = updateFunc(cell);
		if (newContent == cell.Contents)
		{
			throw new ArgumentException("You attempted to update a notebook cell without changing its content. Please provide new content.");
		}

		cell.Contents = newContent;
		SaveNotebook(notebook);

		_iterationCount++;
		_logger.LogInformation($"WorkbookInteraction Iteration {_iterationCount} completed.");
		returnMessage.AppendLine($"Cell #{cellIndex} successfully updated with new content:\n{cell.Contents}\n");

		if (!runNotebook && _blindUpdatesCounter > 3)
		{
			returnMessage.AppendLine($"After more that 3 blind updates, we are running and returning the entire notebook to refresh context\n");
			_blindUpdatesCounter = 0;
			runNotebook = true;
			returnNotebook = true;
		}

		if (runNotebook)
		{
			var outputJson = await RunNotebookAsync(returnMessage, returnNotebook, notebook);
		}
		else
		{
			_blindUpdatesCounter++;
			returnMessage.AppendLine("Running cell\n...");
			await _executor.RunCell(cell);
			returnMessage.AppendLine("Cell execution completed.");

			var outputJson = notebook.ToJupyterJson();
			var cellOutput = ExtractCellOutput(outputJson, cellIndex);
			if (string.IsNullOrEmpty(cellOutput) || cellOutput == "[]")
			{
				returnMessage.AppendLine("Cell has no output.");
			}
			else
			{
				returnMessage.AppendLine($"Cell Outputs:\n{cellOutput}\n");
				if (cellOutput.Contains("\"output_type\": \"error\""))
				{
					returnMessage.AppendLine("Cell has an error output. Please fix the content of this cell before proceeding.");
				}
			}
		}
	}

	public static IEnumerable<int> FindAllIndex<T>(IEnumerable<T> list, Predicate<T> predicate)
	{
		int index = 0;
		foreach (T item in list)
		{
			if (predicate(item)) yield return index;
			index++;
		}
	}

	public async Task<string> RunNotebookAsync(StringBuilder returnMessage, bool returnNotebook, InteractiveDocument? notebook = null)
	{
		await InitializeExecutorIfNeeded(); // Choisir Python ou C# si pas déjà fait

		if (notebook == null)
		{
			notebook = await LoadNotebookAsync();
		}

		returnMessage.AppendLine("Restarting Kernel and running entire notebook\n...");

		// On recrée le kernel selon le type de notebook, pour simuler un vrai "restart"
		_executor = null;
		await InitializeExecutorIfNeeded();

		await _executor.RunNotebookAsync(notebook);
		returnMessage.AppendLine("Notebook execution completed.");

		var outputJson = notebook.ToJupyterJson();
		if (returnNotebook)
		{
			returnMessage.AppendLine($"Complete Notebook Jupyter json:\n{outputJson}\n");
		}
		else
		{
			var cellsWithErrors = FindAllIndex(notebook.Elements, e => e.Outputs.Exists(output => output is ErrorElement)).ToList();
			if (cellsWithErrors.Count > 0)
			{
				returnMessage.AppendLine($"The notebook contains {cellsWithErrors.Count} cells with errors. Please fix the content of these cells before proceeding.");
				if (!returnNotebook)
				{
					var errorCellsContent = cellsWithErrors.Select(i => ExtractCell(outputJson, i).GetRawText()).ToList();
					returnMessage.AppendLine($"Cells with errors:\n{string.Join("\n", errorCellsContent)}\n");
				}
			}
			else
			{
				returnMessage.AppendLine("No errors found in outputs, but please ensure the notebook achieves its intended purpose before proceeding.");
			}
		}
		return outputJson;
	}

	protected async Task ExecuteWithExceptionHandling(Func<Task> function, StringBuilder returnMessage)
	{
		try
		{
			await function();
		}
		catch (Exception ex)
		{
			returnMessage.AppendLine($"Error: {ex.Message}");
		}
	}

	[KernelFunction]
	[Description("Runs the latest version of the notebook and returns the output")]
	public async Task<string> RunNotebook()
	{
		var returnMessage = new StringBuilder();
		returnMessage.AppendLine("Start RunNotebook\n");

		await ExecuteWithExceptionHandling(async () =>
		{
			await RunNotebookAsync(returnMessage, true);
		}, returnMessage);

		returnMessage.AppendLine("End RunNotebook");
		var toReturn = returnMessage.ToString();
		_logger.LogInformation($"{toReturn}\n");
		return toReturn;
	}
}
