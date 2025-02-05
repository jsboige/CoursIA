using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Logging;
using MyNotebookLib;


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