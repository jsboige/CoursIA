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
using Newtonsoft.Json.Bson;


namespace MyIA.AI.Notebooks;

[Experimental("SKEXP0110")]
class Program
{

	private static string defaultPythonNotebookTaskInstruction = @"Créer un notebook Python permettant de requêter DBpedia (SPARQL) et d’afficher un graphique final avec rdflib ou SPARQLWrapper et plotly.  

**Résultat attendu** :
  
1. Une requête complexe sur DBpedia (avec agrégats) correctement exécutée.  
2. Un graphique plotly **pertinent** reflétant les données issues de DBpedia.";



	private static bool testPython = true;

	static async Task Main(string[] args)
	{
		//await GuessingGame.RunGameAsync(_logger, InitSemanticKernel);
		await TestNotebookUpdater().ConfigureAwait(false);
	}


	private static async Task TestNotebookUpdater()
	{
		var logger = new DisplayLogger("NotebookUpdater", LogLevel.Trace);
		var notebookPath = @$"./Workbooks/Workbook-{DateTime.Now.ToFileTime()}.ipynb";
		var autoInvokeUpdater = new AutoInvokeSKAgentsNotebookUpdater(notebookPath, logger);
		if (testPython)
		{
			autoInvokeUpdater.NotebookTemplatePath = "./Semantic-Kernel/Workbook-Template-Python.ipynb";
			autoInvokeUpdater.SetStartingNotebookFromTemplate(defaultPythonNotebookTaskInstruction);
		}
		else
		{
			autoInvokeUpdater.SetStartingNotebookFromTemplate(autoInvokeUpdater.NotebookTaskDescription);
		}

		await autoInvokeUpdater.UpdateNotebookAsync().ConfigureAwait(false);
	}


}



