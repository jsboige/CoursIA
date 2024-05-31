using Microsoft.DotNet.Interactive;
using Microsoft.DotNet.Interactive.Commands;
using Microsoft.DotNet.Interactive.Documents;
using Microsoft.DotNet.Interactive.Events;

namespace MyIA.AI.Notebooks;

public class NotebookExecutor
{
	private readonly CompositeKernel _kernel;

	public NotebookExecutor(CompositeKernel kernel)
	{
		_kernel = kernel;
	}

	public async Task<InteractiveDocument> RunNotebookAsync(
		InteractiveDocument notebook,
		IDictionary<string, string>? parameters = null,
		CancellationToken cancellationToken = default)
	{
		Console.WriteLine("Exécution du notebook en cours...\n");

		var resultDocument = new InteractiveDocument();

		if (parameters is not null)
		{
			parameters = new Dictionary<string, string>(parameters, StringComparer.InvariantCultureIgnoreCase);
		}

		var kernelInfoCollection = CreateKernelInfos(_kernel);
		var lookup = kernelInfoCollection.ToDictionary(k => k.Name, StringComparer.OrdinalIgnoreCase);

		foreach (var element in notebook.Elements)
		{
			if (lookup.TryGetValue(element.KernelName!, out var kernelInfo) &&
			    StringComparer.OrdinalIgnoreCase.Equals(kernelInfo.LanguageName, "markdown"))
			{
				var formattedValue = new FormattedValue("text/markdown", element.Contents);
				var displayValue = new DisplayValue(formattedValue);
				Console.WriteLine($"Affichage du markdown: \n{element.Contents}");
				await _kernel.SendAsync(displayValue);
				resultDocument.Add(element);
			}
			else
			{
				try
				{
					var submitCode = new SubmitCode(element.Contents, element.KernelName);
					Console.WriteLine($"Envoi du code au kernel {element.KernelName}:\n{element.Contents}");

					KernelCommandResult codeResult = await _kernel.SendAsync(submitCode);

					var outputs = new List<InteractiveDocumentOutputElement>();

					foreach (var ev in codeResult.Events)
					{
						if (ev is DisplayEvent displayEvent)
						{
							outputs.Add(CreateDisplayOutputElement(displayEvent));
						}
						else if (ev is ErrorProduced errorProduced)
						{
							outputs.Add(CreateErrorOutputElement(errorProduced));
						}
						else if (ev is StandardOutputValueProduced stdOutput)
						{
							outputs.Add(new TextElement(stdOutput.Value.ToString(), "stdout"));
						}
						else if (ev is StandardErrorValueProduced stdError)
						{
							outputs.Add(new TextElement(stdError.Value.ToString(), "stderr"));
						}
						else if (ev is CommandFailed commandFailed)
						{
							outputs.Add(CreateErrorOutputElement(commandFailed));
						}
						else if (ev is DisplayedValueProduced displayedValueProduced)
						{
							outputs.Add(CreateDisplayOutputElement(displayedValueProduced));
						}
						else if (ev is DisplayedValueUpdated displayedValueUpdated)
						{
							outputs.Add(CreateDisplayOutputElement(displayedValueUpdated));
						}
						else if (ev is ReturnValueProduced returnValueProduced)
						{
							outputs.Add(CreateDisplayOutputElement(returnValueProduced));
						}
						else if (ev is DiagnosticsProduced diagnosticsProduced)
						{
							diagnosticsProduced.Diagnostics
								.Select(d => new ErrorElement(d.Severity.ToString(), d.Message))
								.ToList()
								.ForEach(e => outputs.Add(e));
						}
					}

					var newElement = new InteractiveDocumentElement(
						element.Contents,
						element.KernelName,
						outputs);

					resultDocument.Add(newElement);
				}
				catch (Exception ex)
				{
					Console.WriteLine($"Crash du kernel {element.KernelName}");
					var errorElement = new ErrorElement("Error", ex.Message);
					var newElement = new InteractiveDocumentElement(
						element.Contents, element.KernelName,
						new List<InteractiveDocumentOutputElement> { errorElement });

					resultDocument.Add(newElement);
				}
			}
		}

		var defaultKernelName = _kernel.DefaultKernelName;
		var defaultKernel = _kernel.ChildKernels.SingleOrDefault(k => k.Name == defaultKernelName);
		var languageName = defaultKernel?.KernelInfo.LanguageName ?? notebook.GetDefaultKernelName() ?? "C#";

		resultDocument.Metadata["kernelspec"] = new Dictionary<string, object>
		{
			{ "name", defaultKernel?.Name ?? "csharp" },
			{ "language", languageName }
		};

		Console.WriteLine("Exécution du notebook terminée.");

		return resultDocument;
	}

	private KernelInfoCollection CreateKernelInfos(CompositeKernel kernel)
	{
		KernelInfoCollection kernelInfos = new();

		foreach (var childKernel in kernel.ChildKernels)
		{
			kernelInfos.Add(new Microsoft.DotNet.Interactive.Documents.KernelInfo(childKernel.Name, languageName: childKernel.KernelInfo.LanguageName, aliases: childKernel.KernelInfo.Aliases));
		}

		if (!kernelInfos.Contains("markdown"))
		{
			kernelInfos = kernelInfos.Clone();
			kernelInfos.Add(new Microsoft.DotNet.Interactive.Documents.KernelInfo("markdown", languageName: "Markdown"));
		}

		return kernelInfos;
	}

	private DisplayElement CreateDisplayOutputElement(DisplayEvent displayEvent) =>
		new(displayEvent
			.FormattedValues
			.ToDictionary(
				v => v.MimeType,
				v => (object)v.Value));

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
}