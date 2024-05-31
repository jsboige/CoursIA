using System.ComponentModel;
using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using System.Web;
using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.CSharp;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Documents.Jupyter;
using Microsoft.DotNet.Interactive.PackageManagement;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;

namespace MyIA.AI.Notebooks;

public class WorkbookInteraction
{
	private readonly string _notebookPath;
	private readonly NotebookExecutor _executor;
	private int _iterationCount = 0;

	private readonly ILogger _logger;

	public WorkbookInteraction(string notebookPath, ILogger logger)
	{
		_notebookPath = notebookPath;

		var cSharpKernel = new CSharpKernel()
			.UseKernelHelpers()
			.UseWho()
			.UseValueSharing();

		cSharpKernel.UseNugetDirective((k, resolvedPackageReference) =>
		{
			k.AddAssemblyReferences(Enumerable
				.SelectMany<ResolvedPackageReference, string>(resolvedPackageReference, r => r.AssemblyPaths));
			return Task.CompletedTask;
		}, false);

		var compositeKernel = new CompositeKernel
		{
			cSharpKernel
		};

		_executor = new NotebookExecutor(compositeKernel);
		_logger = logger;
	}

	//[KernelFunction]
	//[Description("Runs an updated version of the workbook and returns the notebook with output cells")]
	//public async Task<string> UpdateEntireWorkbook(
	//	[Description("the new version of the workbook in ipynb json format, with multiple edited cells, and outputs optional")] string updatedWorkbook)
	//{
	//	Console.WriteLine($"Appel en function calling à UpdateWorkbook avec le notebook...\n{updatedWorkbook}");
	//	File.WriteAllText(_notebookPath, updatedWorkbook);

	//	try
	//	{
	//		var notebook = await InteractiveDocument.LoadAsync(new FileInfo(_notebookPath));
	//		var resultDocument = await _executor.RunNotebookAsync(notebook);
	//		var outputJson = resultDocument.ToJupyterJson();
	//		File.WriteAllText(_notebookPath, outputJson);
	//		Console.WriteLine($"Appel à UpdateWorkbook terminé, renvoi du workbook après réexécution...\n{outputJson}");
	//		_iterationCount++;
	//		Console.WriteLine($"WorkbookInteraction Itération {_iterationCount} terminée.");
	//		return outputJson;
	//	}
	//	catch (Exception ex)
	//	{
	//		var message = $"Erreur lors de l'exécution du notebook: {ex.Message}";
	//		Console.WriteLine(message);
	//		_logger.LogError(ex, "Erreur lors de l'exécution du notebook");
	//		return message;
	//	}
	//}

	[KernelFunction]
	[Description("Runs the current .Net interactive notebook, returns the notebook saved in json format with errors in output cells and counts the number of error outputs")]
	public async Task<string> RunNotebook()
	{
		Console.WriteLine($"Appel en function calling à RunNotebook");
		var returnMessage = new StringBuilder();
		returnMessage.AppendLine($"Running .Net interactive Notebook\n...\n");

		try
		{

			var notebook = await InteractiveDocument.LoadAsync(new FileInfo(_notebookPath));
			var resultDocument = await _executor.RunNotebookAsync(notebook);
			var outputJson = resultDocument.ToJupyterJson();
			returnMessage.AppendLine($".Net interactive Notebook run ended with the following outputs\n{outputJson}\n");
			var errors = resultDocument.Elements.Where(e => e.Outputs.Exists(output => output is ErrorElement error)).ToList();
			if (errors.Count>0)
			{
				returnMessage.AppendLine($"{errors.Count} cells have outputs with errors, please fix the content of their parent cells' source before moving forward.");
			}
			else
			{
				returnMessage.AppendLine("No error was found in outputs, but please check that the notebook reaches its stated goal before returning.");
			}
			_iterationCount++;
			Console.WriteLine($"WorkbookInteraction Itération {_iterationCount} terminée.");
		}
		catch (Exception ex)
		{
			var message = $"Error running notebook:\n{ex.Message}";
			returnMessage.AppendLine($"{message}");
			_logger.LogError(ex, "Erreur lors de l'exécution du notebook");

		}
		var toReturn = returnMessage.ToString();
		Console.WriteLine(toReturn);
		return toReturn;
	}

	public static string DecodeValue(string newValue)
	{
		newValue = Regex.Unescape(newValue);
		newValue = HttpUtility.HtmlDecode(newValue);
		newValue = HttpUtility.UrlDecode(newValue);
		return newValue;
	}

	[KernelFunction]
	[Description("Updates a specific Markdown or code cell in the current .Net interactive notebook by providing the entire new content")]
	public async Task<string> ReplaceWorkbookCell(
		[Description(uniqueContentDescription)] string uniqueContent,
		[Description("The new entire string for the target cell's content")] string newCellContent)
	{
		uniqueContent = DecodeValue(uniqueContent).Trim();
		newCellContent = DecodeValue(newCellContent);


		var returnMessage = new StringBuilder();
		returnMessage.AppendLine($"Updating cell containing: {uniqueContent}\n\nReplacement cell:{newCellContent}\n...\n");
		try
		{
			var notebook = await InteractiveDocument.LoadAsync(new FileInfo(_notebookPath));
			var cell = notebook.Elements.FirstOrDefault(e => e.Contents.Contains(uniqueContent));
			if (cell == null)
			{
				throw new Exception($"Cell with identifying string '{uniqueContent}' not found.");
			}

			cell.Contents = newCellContent;


			var notebookJson = notebook.ToJupyterJson();
			File.WriteAllText(_notebookPath, notebookJson);
			_iterationCount++;
			Console.WriteLine($"WorkbookInteraction Itération {_iterationCount} terminée.");
			returnMessage.AppendLine("Cell Successfully updated. Don't forget to run the notebook to check for progress.");
		}
		catch (Exception ex)
		{
			var message = $"Error replacing notebook cell:\n {ex.Message}";
			_logger.LogError(ex, "Erreur lors de l'exécution du notebook");
			returnMessage.AppendLine(message);
		}

		var toReturn = returnMessage.ToString();
		Console.WriteLine(toReturn);
		return toReturn;
	}

	private const string uniqueContentDescription = "A short string that the target cell to edit contains, and that is found nowhere else in the other cells, thus identifying the cell univoquely by lookup";

	//[KernelFunction]
	//[Description("Updating function for large notebook cells with 15+ unchanged lines: use to replace or insert a specific string locally without having to write the entire cell")]
	//public async Task<string> UpdateLargeWorkbookCell(
	//	[Description(uniqueContentDescription)] string uniqueContent,
	//	[Description("A string directly preceding the position where the new content should be added in the target cell, or empty for appending the new content at a new line at the end of the cell")] string editLocation,
	//	[Description("In case of a replacement, a string that finishes the content block to be replaced, which starts a the end of the editLocation string, or empty for inserting the new content at the same location but without replacing an existing block")] string replacedBlockEnd,
	//	[Description("The new content for replacement or insertion")] string newContent)
	//{
	//	uniqueContent = DecodeValue(uniqueContent);
	//	replacedBlockEnd = DecodeValue(replacedBlockEnd);
	//	editLocation = DecodeValue(editLocation);

	//	newContent = DecodeValue(newContent);


	//	var returnMessage = new StringBuilder();
	//	returnMessage.AppendLine($"Updating large cell containing: {uniqueContent}\nInsert location:{editLocation}\nReplaced block end:{replacedBlockEnd}\nNew content:{newContent}\n...\n");
	//	try
	//	{
	//		var notebook = await InteractiveDocument.LoadAsync(new FileInfo(_notebookPath));
	//		var cell = notebook.Elements.FirstOrDefault(e => e.Contents.Contains(uniqueContent));
	//		if (cell == null)
	//		{
	//			throw new Exception($"Cell with identifying string '{uniqueContent}' not found.");
	//		}

	//		if (string.IsNullOrEmpty(editLocation))
	//		{
	//			cell.Contents = $"{cell.Contents}\n{newContent}";
	//		}
	//		else if (!cell.Contents.Contains(editLocation))
	//		{
	//			throw new Exception($"Edit location '{editLocation}' not found in target cell.");
	//		}
	//		else
	//		{
	//			var editLocationIdx = cell.Contents.IndexOf(editLocation, StringComparison.InvariantCultureIgnoreCase) + editLocation.Length;
	//			if (string.IsNullOrEmpty(replacedBlockEnd))
	//			{
	//				cell.Contents =
	//					$"{cell.Contents.Substring(0, editLocationIdx)}\n{newContent}\n{cell.Contents.Substring(editLocationIdx)}";
	//			}
	//			else if (!cell.Contents.Contains(replacedBlockEnd))
	//			{
	//				throw new Exception($"Replaced Block End'{replacedBlockEnd}' not found in target cell.");
	//			}
	//			else
	//			{
	//				var replacedEndIndex = cell.Contents.IndexOf(replacedBlockEnd, StringComparison.InvariantCultureIgnoreCase) + replacedBlockEnd.Length;
	//				var replacedBlock = cell.Contents.Substring(editLocationIdx, replacedEndIndex - editLocationIdx);
	//				cell.Contents = cell.Contents.Replace(replacedBlock, newContent);
	//			}
	//		};


	//		var notebookJson = notebook.ToJupyterJson();
	//		File.WriteAllText(_notebookPath, notebookJson);
			
	//		_iterationCount++;
	//		Console.WriteLine($"WorkbookInteraction Itération {_iterationCount} terminée.");
	//		returnMessage.AppendLine($"Cell Successfully updated. New Cell content:\n{cell.Contents}\n Please fix any typo, and don't forget to run the notebook to check for outputs before moving on with next steps.");
	//	}
	//	catch (Exception ex)
	//	{
	//		var message = $"Error updating large notebook cell:\n {ex.Message}";
	//		Console.WriteLine(message);
	//		_logger.LogError(ex, "Erreur lors de l'exécution du notebook");
	//		returnMessage.AppendLine(message);
	//	}

	//	var toReturn = returnMessage.ToString();
	//	Console.WriteLine(toReturn);
	//	return toReturn;
	//}


}