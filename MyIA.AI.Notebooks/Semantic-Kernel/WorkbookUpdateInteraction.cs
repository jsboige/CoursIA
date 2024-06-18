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
	public class WorkbookUpdateInteraction(string notebookPath, ILogger logger)
		: WorkbookInteractionBase(notebookPath, logger)
	{
		private bool _isPendingApproval;

		public bool IsPendingApproval => _isPendingApproval;

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
			var toReturn = returnMessage.ToString();
			_logger.LogInformation($"{toReturn}\n");
			return toReturn;
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
			var toReturn = returnMessage.ToString();
			_logger.LogInformation($"{toReturn}\n");
			return toReturn;
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
			var toReturn = returnMessage.ToString();
			_logger.LogInformation($"{toReturn}\n");
			return toReturn;
		}


		[KernelFunction]
		[Description("Submits the latest version for aproval")]
		public Task<string> SubmitNotebook()
		{
			this._isPendingApproval = true;
			var message = $"Notebook submitted\n";
			_logger.LogInformation(message);
			return Task.FromResult(message);
		}

	}
}
