using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.SemanticKernel;
using SKernel = Microsoft.SemanticKernel.Kernel;
using Microsoft.DotNet.Interactive;
using Microsoft.SemanticKernel.ChatCompletion;
using System.ComponentModel;
using System.Diagnostics.CodeAnalysis;
using AutoGen.Core;
using AutoGen.OpenAI;
using AutoGen.OpenAI.Extension;
using Microsoft.SemanticKernel.Agents;
using Microsoft.SemanticKernel.Agents.Chat;
using Microsoft.SemanticKernel.Connectors.OpenAI;
using AutoGen.SemanticKernel;
using Azure.AI.OpenAI;
using Humanizer;
using Microsoft.CodeAnalysis.Elfie.Diagnostics;


namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
class Program
{

	static async Task Main(string[] args)
	{
		//await GuessingGame.RunGameAsync(_logger, InitSemanticKernel);
		var logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		var autoInvokeUpdater = new AutoInvokeSKAgentsNotebookUpdater(notebookPath,logger);
		autoInvokeUpdater.SetStartingNotebookFromTemplate(autoInvokeUpdater.NotebookTaskDescription);
		await autoInvokeUpdater.UpdateNotebookAsync();
	}
	

}



