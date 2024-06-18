using System.ComponentModel;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;

namespace MyIA.AI.Notebooks;

public class WorkbookValidation(string notebookPath, ILogger logger) : WorkbookInteractionBase(notebookPath, logger)
{

	private bool _isApproved;

	public bool IsApproved => _isApproved;

		

	[KernelFunction]
	[Description("Submits the latest version for aproval")]
	public Task<string> ApproveNotebook()
	{
		this._isApproved = true;
		var message = $"Notebook approved\n";
		_logger.LogInformation(message);
		return Task.FromResult(message);
	}
}