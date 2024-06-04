using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.Commands;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Events;
using Microsoft.Extensions.Logging;
using KernelInfo = Microsoft.DotNet.Interactive.Documents.KernelInfo;

namespace MyIA.AI.Notebooks
{
	public class NotebookExecutor
	{
		private readonly CompositeKernel _kernel;
		private readonly Dictionary<string, KernelInfo> _kernelLookup;
		public int TruncationLength = 500;
		private readonly ILogger _logger;

		public NotebookExecutor(CompositeKernel kernel, ILogger logger)
		{
			_logger = logger;
			_kernel = kernel;
			var kernelInfoCollection = CreateKernelInfos(_kernel);
			_kernelLookup = kernelInfoCollection.ToDictionary(k => k.Name, StringComparer.OrdinalIgnoreCase);
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

			var defaultKernelName = _kernel.DefaultKernelName;
			var defaultKernel = _kernel.ChildKernels.SingleOrDefault(k => k.Name == defaultKernelName);
			var languageName = defaultKernel?.KernelInfo.LanguageName ?? notebook.GetDefaultKernelName() ?? "C#";

			notebook.Metadata["kernelspec"] = new Dictionary<string, object>
			{
				{ "name", defaultKernel?.Name ?? "csharp" },
				{ "language", languageName }
			};

			_logger.LogInformation("Exécution du notebook terminée.");
		}

		public async Task RunCell(InteractiveDocumentElement element)
		{
			if (_kernelLookup.TryGetValue(element.KernelName!, out var kernelInfo) &&
			    StringComparer.OrdinalIgnoreCase.Equals(kernelInfo.LanguageName, "markdown"))
			{
				var formattedValue = new FormattedValue("text/markdown", element.Contents);
				var displayValue = new DisplayValue(formattedValue);
				await _kernel.SendAsync(displayValue);
			}
			else
			{
				try
				{
					var submitCode = new SubmitCode(element.Contents, element.KernelName);
					KernelCommandResult codeResult = await _kernel.SendAsync(submitCode);

					var outputs = new List<InteractiveDocumentOutputElement>();

					var displayedValues = new Dictionary<string, int>();

					foreach (var ev in codeResult.Events)
					{
						//if (ev is DisplayEvent displayEvent)
						//{
						//	outputs.Add(CreateDisplayOutputElement(displayEvent));
						//}
						if (ev is ErrorProduced errorProduced)
						{
							outputs.Add(CreateErrorOutputElement(errorProduced));
						}
						else if (ev is StandardOutputValueProduced stdOutput)
						{
							outputs.Add(CreateDisplayOutputElement(stdOutput));
						}
						else if (ev is StandardErrorValueProduced stdError)
						{
							outputs.Add(CreateDisplayOutputElement(stdError));
						}
						else if (ev is CommandFailed commandFailed)
						{
							outputs.Add(CreateErrorOutputElement(commandFailed));
						}
						else if (ev is DisplayedValueProduced displayedValueProduced)
						{
							outputs.Add(CreateDisplayOutputElement(displayedValueProduced));
							displayedValues[displayedValueProduced.ValueId] = outputs.Count - 1;
						}
						else if (ev is DisplayedValueUpdated displayedValueUpdated)
						{
							if (displayedValues.TryGetValue(displayedValueUpdated.ValueId, out var index))
							{
								outputs[index] = CreateDisplayOutputElement(displayedValueUpdated);
							}
							else
							{
								throw new InvalidOperationException($"Displayed value with id {displayedValueUpdated.ValueId} not found for updating.");
							}
						}
						else if (ev is ReturnValueProduced returnValueProduced)
						{
							outputs.Add(CreateDisplayOutputElement(returnValueProduced));
						}
						else if (ev is DiagnosticsProduced diagnosticsProduced)
						{
							diagnosticsProduced.Diagnostics
								.Select(d => new ErrorElement(d.Message, d.Severity.ToString()))
								.ToList()
								.ForEach(e => outputs.Add(e));
						}
					}

					element.Outputs.Clear();
					element.Outputs.AddRange(outputs);
				}
				catch (Exception ex)
				{
					_logger.LogError(message:$"Crash du kernel {element.KernelName}",exception:ex);
					//var errorElement = new ErrorElement("Error", ex.Message);
					//element.Outputs.Clear();
					//element.Outputs.Add(errorElement);
				}
			}
		}

		private KernelInfoCollection CreateKernelInfos(CompositeKernel kernel)
		{
			KernelInfoCollection kernelInfos = new();

			foreach (var childKernel in kernel.ChildKernels)
			{
				kernelInfos.Add(new KernelInfo(childKernel.Name, languageName: childKernel.KernelInfo.LanguageName, aliases: childKernel.KernelInfo.Aliases));
			}

			if (!kernelInfos.Contains("markdown"))
			{
				kernelInfos = kernelInfos.Clone();
				kernelInfos.Add(new KernelInfo("markdown", languageName: "Markdown"));
			}

			return kernelInfos;
		}

		private DisplayElement CreateDisplayOutputElement(DisplayEvent displayEvent) =>
			new(displayEvent
				.FormattedValues
				.ToDictionary(
					v => v.MimeType,
					v => (object)Truncate(v.Value)));

		private ErrorElement CreateErrorOutputElement(ErrorProduced errorProduced) =>
			new(errorName: "Error", errorValue: errorProduced.Message);

		private ErrorElement CreateErrorOutputElement(CommandFailed failed) =>
			new(errorName: "Error",
				errorValue: failed.Message,
				stackTrace: failed.Exception switch
				{
					{ } ex => SplitIntoLines(ex.StackTrace ?? ""),
					_ => Array.Empty<string>()
				});

		public static string[] SplitIntoLines(string s) =>
			s.Split(new[] { "\r\n", "\n" }, StringSplitOptions.None);


		public string Truncate(string s) => s.Length <= TruncationLength ? s : s.Substring(0, TruncationLength) + "(...)";
			
	}



}
