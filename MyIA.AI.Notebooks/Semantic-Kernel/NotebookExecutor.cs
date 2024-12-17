using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.Commands;
using Microsoft.DotNet.Interactive.Connection;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Documents.Jupyter;
using Microsoft.DotNet.Interactive.Events;
using Microsoft.DotNet.Interactive.Utility;
using Microsoft.Extensions.Logging;
using System;
using System.Diagnostics;
using System.Reflection;
using System.Threading;
using KernelInfo = Microsoft.DotNet.Interactive.Documents.KernelInfo;

public class NotebookExecutor
{
	private readonly CompositeKernel _kernel;
	private readonly Dictionary<string, KernelInfo> _kernelLookup;
	public int TruncationLength = 500;
	private readonly ILogger _logger;

	public event EventHandler<DisplayEvent>? DisplayEvent;
	public event EventHandler<CommandFailed>? CommandFailed;

	public NotebookExecutor(CompositeKernel kernel, ILogger logger)
	{
		_logger = logger;
		_kernel = kernel;

		var kernelInfoCollection = CreateKernelInfos(_kernel);
		_kernelLookup = kernelInfoCollection.ToDictionary(k => k.Name, StringComparer.OrdinalIgnoreCase);

		kernel.KernelEvents.Subscribe(OnKernelEventReceived);
	}

	public async Task RunNotebookAsync(
		InteractiveDocument notebook,
		IDictionary<string, string>? parameters = null,
		CancellationToken cancellationToken = default)
	{
		_logger.LogInformation("Exécution du notebook en cours...\n");

		if (parameters is not null)
		{
			parameters = new Dictionary<string, string>(parameters, StringComparer.InvariantCultureIgnoreCase);
		}

		foreach (var element in notebook.Elements)
		{
			await RunCell(element);
		}

		// On définit la langue par défaut du notebook selon le kernel par défaut
		var defaultKernelName = _kernel.DefaultKernelName;
		var defaultKernel = _kernel.ChildKernels.SingleOrDefault(k => k.Name == defaultKernelName);
		var languageName = defaultKernel?.KernelInfo.LanguageName
						   ?? notebook.GetDefaultKernelName()
						   ?? "C#";

		notebook.Metadata["kernelspec"] = new Dictionary<string, object>
		{
			{ "name", defaultKernel?.Name ?? "csharp" },
			{ "language", languageName }
		};

		_logger.LogInformation("Exécution du notebook terminée.");
	}

	public async Task RunCell(InteractiveDocumentElement element)
	{
		// Vérifie s’il s’agit d’une cellule Markdown
		if (_kernelLookup.TryGetValue(element.KernelName ?? "", out var kernelInfo) &&
			string.Equals(kernelInfo.LanguageName, "Markdown", StringComparison.OrdinalIgnoreCase))
		{
			var formattedValue = new FormattedValue("text/markdown", element.Contents);
			var displayValue = new DisplayValue(formattedValue);
			await _kernel.SendAsync(displayValue);
			return;
		}

		// Sinon, c’est du code
		try
		{
			// S'il n'y a pas de KernelName, on suppose que c'est celui par défaut (souvent "csharp" ou "pythonkernel")
			var targetKernelName = string.IsNullOrEmpty(element.KernelName)
				? _kernel.DefaultKernelName
				: element.KernelName;

			if (targetKernelName.Contains("python", StringComparison.OrdinalIgnoreCase))
			{
				element.Contents = $"#!{targetKernelName}\n{element.Contents}";
			}

			var submitCode = new SubmitCode(element.Contents, targetKernelName);
			KernelCommandResult codeResult = await _kernel.SendAsync(submitCode);

			var outputs = new List<InteractiveDocumentOutputElement>();
			var displayedValues = new Dictionary<string, int>();

			foreach (var ev in codeResult.Events)
			{
				switch (ev)
				{
					case ErrorProduced errorProduced:
						outputs.Add(CreateErrorOutputElement(errorProduced));
						break;

					case StandardOutputValueProduced stdOutput:
						outputs.Add(CreateDisplayOutputElement(stdOutput));
						break;

					case StandardErrorValueProduced stdError:
						outputs.Add(CreateDisplayOutputElement(stdError));
						break;

					case CommandFailed commandFailed:
						outputs.Add(CreateErrorOutputElement(commandFailed));
						CommandFailed?.Invoke(this, commandFailed);
						break;

					case DisplayedValueProduced displayedValueProduced:
						outputs.Add(CreateDisplayOutputElement(displayedValueProduced));
						displayedValues[displayedValueProduced.ValueId] = outputs.Count - 1;
						break;

					case DisplayedValueUpdated displayedValueUpdated:
						if (displayedValues.TryGetValue(displayedValueUpdated.ValueId, out var index))
						{
							outputs[index] = CreateDisplayOutputElement(displayedValueUpdated);
						}
						else
						{
							throw new InvalidOperationException($"Displayed value with id {displayedValueUpdated.ValueId} not found for updating.");
						}
						break;

					case ReturnValueProduced returnValueProduced:
						outputs.Add(CreateDisplayOutputElement(returnValueProduced));
						break;

					case DiagnosticsProduced diagnosticsProduced:
						diagnosticsProduced.Diagnostics
							.Select(d => new ErrorElement(d.Message, d.Severity.ToString()))
							.ToList()
							.ForEach(e => outputs.Add(e));
						break;
				}
			}

			element.Outputs.Clear();
			element.Outputs.AddRange(outputs);
		}
		catch (Exception ex)
		{
			_logger.LogError($"Kernel crash for cell '{element.KernelName}': {ex}");
		}
	}

	private KernelInfoCollection CreateKernelInfos(CompositeKernel kernel)
	{
		KernelInfoCollection kernelInfos = new();

		foreach (var childKernel in kernel.ChildKernels)
		{
			kernelInfos.Add(
				new KernelInfo(
					childKernel.Name,
					languageName: childKernel.KernelInfo.LanguageName,
					aliases: childKernel.KernelInfo.Aliases));
		}

		// Ajoute un kernel "markdown" fictif dans le lookup si non présent
		if (!kernelInfos.Contains("markdown"))
		{
			kernelInfos = kernelInfos.Clone();
			kernelInfos.Add(new KernelInfo("markdown", languageName: "Markdown"));
		}

		return kernelInfos;
	}

	private DisplayElement CreateDisplayOutputElement(DisplayEvent displayEvent) =>
		new(displayEvent.FormattedValues
			.ToDictionary(v => v.MimeType, v => (object)Truncate(v.Value)));

	private ErrorElement CreateErrorOutputElement(ErrorProduced errorProduced) =>
		new("Error", errorProduced.Message);

	private ErrorElement CreateErrorOutputElement(CommandFailed failed) =>
		new(
			"Error",
			failed.Message,
			stackTrace: failed.Exception switch
			{
				{ } ex => SplitIntoLines(ex.StackTrace ?? ""),
				_ => Array.Empty<string>()
			});

	public static string[] SplitIntoLines(string s) =>
		s.Split(new[] { "\r\n", "\n" }, StringSplitOptions.None);

	public string Truncate(string s) => s.Length <= TruncationLength ? s : s[..TruncationLength] + "(...)";

	private void OnKernelEventReceived(KernelEvent ke)
	{
		switch (ke)
		{
			case DisplayEvent de:
				DisplayEvent?.Invoke(this, de);
				break;
			case CommandFailed cf:
				CommandFailed?.Invoke(this, cf);
				break;
		}
	}
}
