using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System.Web;
using AngleSharp.Html.Dom.Events;
using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.CSharp;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Documents.Jupyter;
using Microsoft.DotNet.Interactive.PackageManagement;
using Microsoft.Extensions.Logging;
using Microsoft.ML.Probabilistic.Collections;
using Microsoft.SemanticKernel;

namespace MyIA.AI.Notebooks
{
	public class WorkbookInteraction
	{
		private readonly string _notebookPath;
		private NotebookExecutor _executor;
		private int _iterationCount = 0;
		private readonly ILogger _logger;

		public WorkbookInteraction(string notebookPath, ILogger logger)
		{
			_notebookPath = notebookPath;
			_logger = logger;

			InitializeExecutor();
		}

		public void InitializeExecutor()
		{
			var cSharpKernel = new CSharpKernel()
				.UseKernelHelpers()
				.UseWho()
				.UseValueSharing();

			cSharpKernel.UseNugetDirective((k, resolvedPackageReference) =>
			{
				k.AddAssemblyReferences(resolvedPackageReference
					.SelectMany(r => r.AssemblyPaths));
				return Task.CompletedTask;
			}, false);

			var compositeKernel = new CompositeKernel
			{
				cSharpKernel
			};

			_executor = new NotebookExecutor(compositeKernel, _logger);
		}

		private async Task<InteractiveDocument> LoadNotebookAsync()
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

		private async Task UpdateCellAsync(string uniqueContent, Func<InteractiveDocumentElement, string> updateFunc, StringBuilder returnMessage, bool runNotebook, bool returnNotebook)
		{
			var notebook = await LoadNotebookAsync();
			var cell = notebook.Elements.FirstOrDefault(e => e.Contents.Contains(uniqueContent));
			if (cell == null)
			{
				throw new ArgumentException($"Cell with identifying string '{uniqueContent}' not found in notebook.");
			}
			else
			{
				returnMessage.AppendLine($"Successfully identified cell with unique string:\n{uniqueContent}\n");
			}

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

			if (runNotebook)
			{
				returnMessage.AppendLine("Restarting Kernel and running entire notebook\n...");
				this.InitializeExecutor();
				await _executor.RunNotebookAsync(notebook);
				returnMessage.AppendLine("Notebook execution completed.");
				var outputJson = notebook.ToJupyterJson();
				if (returnNotebook)
				{
					returnMessage.AppendLine($"Complete Notebook Jupyter json:\n{outputJson}\n");
				}

				var cellsWithErrors = notebook.Elements.FindAllIndex(e => e.Outputs.Exists(output => output is ErrorElement)).ToList();
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
			else
			{
				returnMessage.AppendLine("Running cell\n...");
				await _executor.RunCell(cell);
				returnMessage.AppendLine("Cell execution completed.");
				var outputJson = notebook.ToJupyterJson();
				var cellOutput = ExtractCellOutput(outputJson, cellIndex);
				if (cellOutput == string.Empty | cellOutput == "[]")
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

		private async Task ExecuteWithExceptionHandling(Func<Task> function, StringBuilder returnMessage)
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
		[Description("Updates a specific Markdown or code cell in the current .NET interactive notebook by providing the entire new content")]
		public async Task<string> ReplaceWorkbookCell(
		[Description(uniqueContentDescription)] string uniqueContent,
		[Description("The new content for the target cell")] string newCellContent,
		[Description(restartKernelDescription)] bool restartKernel = false)
		{
			var returnMessage = new StringBuilder();
			returnMessage.AppendLine("Start ReplaceWorkbookCell\n");
			newCellContent = DecodeValue(newCellContent);

			await ExecuteWithExceptionHandling(async () =>
			{
				await UpdateCellAsync(uniqueContent, cell => newCellContent, returnMessage, restartKernel, false);
			}, returnMessage);

			returnMessage.AppendLine("End ReplaceWorkbookCell");
			_logger.LogInformation($"{returnMessage}\n");
			return returnMessage.ToString();
		}

		[KernelFunction]
		[Description("Replaces a specific block within a cell identified by a unique string")]
		public async Task<string> ReplaceBlockInWorkbookCell(
			[Description(uniqueContentDescription)] string uniqueContent,
			[Description("The block of text to be replaced")] string oldBlock,
			[Description("The new content to replace the specified block")] string newContent,
			[Description(restartKernelDescription)] bool restartKernel = false)
		{
			var returnMessage = new StringBuilder();
			returnMessage.AppendLine("Start ReplaceBlockInWorkbookCell\n");

			uniqueContent = DecodeValue(uniqueContent);
			oldBlock = DecodeValue(oldBlock);
			newContent = DecodeValue(newContent);

			await ExecuteWithExceptionHandling(async () =>
			{
				await UpdateCellAsync(uniqueContent, cell =>
				{
					if (!cell.Contents.Contains(oldBlock))
					{
						throw new ArgumentException($"Block to replace not found in target cell.\nBlock:\"{oldBlock}\"\nCell Content:\n\"{cell.Contents}\"", nameof(oldBlock));
					}

					return cell.Contents.Replace(oldBlock, newContent);
				}, returnMessage, restartKernel, false);
			}, returnMessage);

			returnMessage.AppendLine("End ReplaceBlockInWorkbookCell");
			_logger.LogInformation($"{returnMessage}\n");
			return returnMessage.ToString();
		}

		[KernelFunction]
		[Description("Inserts new content after a specified location in a cell identified by a unique string")]
		public async Task<string> InsertInWorkbookCell(
			[Description(uniqueContentDescription)] string uniqueContent,
			[Description("The string directly preceding the position where the new content should be added")] string insertAfter,
			[Description("The new content to be inserted")] string newContent,
			[Description(restartKernelDescription)] bool restartKernel = false)
		{
			var returnMessage = new StringBuilder();
			returnMessage.AppendLine("Start InsertInWorkbookCell\n");

			uniqueContent = DecodeValue(uniqueContent);
			insertAfter = DecodeValue(insertAfter);
			newContent = DecodeValue(newContent);

			await ExecuteWithExceptionHandling(async () =>
			{
				await UpdateCellAsync(uniqueContent, cell =>
				{
					if (!cell.Contents.Contains(insertAfter))
					{
						throw new ArgumentException($"Insert location '{insertAfter}' not found in target cell:\n\"{cell.Contents}\"", nameof(insertAfter));
					}

					var insertIndex = cell.Contents.IndexOf(insertAfter, StringComparison.InvariantCultureIgnoreCase) + insertAfter.Length;
					return cell.Contents.Insert(insertIndex, $"\n{newContent}");
				}, returnMessage, restartKernel, false);
			}, returnMessage);

			returnMessage.AppendLine("End InsertInWorkbookCell");
			_logger.LogInformation($"{returnMessage}\n");
			return returnMessage.ToString();
		}

		private const string uniqueContentDescription = "A short string from the cell to update (e.g., a title in a markdown cell or a comment in a code cell) that is unique across all cells in the notebook";
		private const string restartKernelDescription = "Whether to restart the kernel and reset the entire notebook from the beginning instead of just running the cell";
	}
}
