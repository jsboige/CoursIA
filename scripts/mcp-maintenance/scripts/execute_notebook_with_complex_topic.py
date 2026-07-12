#!/usr/bin/env python3
"""
Script de démonstration pour l'outil MCP spécialisé execute_notebook_with_complex_topic

Ce fichier montre comment l'outil MCP devrait être implémenté dans le serveur
jupyter-papermill-mcp-server pour injecter des sujets complexes via Papermill.

Utilisation depuis le serveur MCP :
- Ajouter cette fonction à execution_tools.py ou main_fastmcp.py
- L'outil utilise la méthode parameterize_notebook existante
- Injecte les paramètres dans la cellule "parameters" du notebook 05
"""

from typing import Dict, Any, Optional
from datetime import datetime


def execute_notebook_with_complex_topic(
    notebook_path: str,
    topic: str,
    complexity: str = "complex",
    framework: str = "python",
    additional_requirements: str = "",
    output_path: Optional[str] = None
) -> Dict[str, Any]:
    """
    Execute le notebook avec injection de sujet complexe via paramètres Papermill
    
    Args:
        notebook_path: Chemin vers le notebook (ex: "05-SemanticKernel-NotebookMaker-batch.ipynb")
        topic: Sujet complexe à injecter (ex: "Créer un notebook d'analyse de données avec pandas...")
        complexity: Niveau de complexité ("simple" | "complex")
        framework: Framework cible ("python" | "dotnet" | "hybrid")
        additional_requirements: Exigences supplémentaires
        output_path: Chemin de sortie optionnel
        
    Returns:
        Dict avec le résultat de l'exécution
        
    Example:
        result = execute_notebook_with_complex_topic(
            notebook_path="MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker-batch.ipynb",
            topic="Créer un notebook d'analyse de données avec pandas et visualisations interactives pour explorer un dataset de ventes e-commerce avec prédiction de tendances via machine learning",
            complexity="complex",
            framework="python",
            additional_requirements="Utiliser scikit-learn pour ML, plotly pour visualisations interactives"
        )
    """
    
    # Préparer les paramètres Papermill selon le format de la cellule parameters
    parameters = {
        # Nouveaux paramètres selon les spécifications de la mission
        "notebook_topic": topic,
        "notebook_complexity": complexity,
        "target_framework": framework,
        "additional_requirements": additional_requirements,
        
        # Paramètres de compatibilité avec l'ancienne logique
        "skip_widgets": True,  # Force le mode batch
        "task_description": topic,  # Map vers l'ancienne variable
        "config_mode": 2  # Force le mode Custom pour utiliser task_description
    }
    
    # Générer le chemin de sortie si non fourni
    if not output_path:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_path = notebook_path.replace(".ipynb", f"_output_{timestamp}.ipynb")
    
    print(f"🚀 Exécution du notebook avec sujet complexe...")
    print(f"📝 Notebook: {notebook_path}")
    print(f"🎯 Sujet: {topic[:100]}{'...' if len(topic) > 100 else ''}")
    print(f"⚙️  Complexité: {complexity}")
    print(f"🔧 Framework: {framework}")
    print(f"📂 Sortie: {output_path}")
    
    # Dans l'implémentation réelle MCP, ceci appellerait :
    # notebook_service, _ = get_services()
    # return await notebook_service.parameterize_notebook(
    #     input_path=notebook_path,
    #     parameters=parameters,
    #     output_path=output_path
    # )
    
    # Simulation pour la démonstration
    return {
        "success": True,
        "method": "papermill_parameterization",
        "input_path": notebook_path,
        "output_path": output_path,
        "parameters_injected": parameters,
        "message": f"Notebook exécuté avec succès avec le sujet complexe : {topic[:50]}...",
        "execution_time": "simulation",
        "status": "completed"
    }


# Code pour le serveur MCP (à ajouter dans main_fastmcp.py ou execution_tools.py)
"""
# Décorateur FastMCP pour le serveur jupyter-papermill-mcp-server
@mcp.tool()
async def execute_notebook_with_complex_topic(
    notebook_path: str = Field(description="Chemin du notebook à exécuter"),
    topic: str = Field(description="Sujet complexe à injecter dans le notebook"),
    complexity: str = Field(default="complex", description="Niveau de complexité (simple|complex)"),
    framework: str = Field(default="python", description="Framework cible (python|dotnet|hybrid)"),
    additional_requirements: str = Field(default="", description="Exigences supplémentaires"),
    output_path: str = Field(default="", description="Chemin de sortie optionnel")
) -> Dict[str, Any]:
    \"\"\"Execute le notebook avec injection de sujet complexe\"\"\"
    
    parameters = {
        "notebook_topic": topic,
        "notebook_complexity": complexity,
        "target_framework": framework,
        "additional_requirements": additional_requirements,
        "skip_widgets": True,
        "task_description": topic,
        "config_mode": 2
    }
    
    notebook_service, _ = get_services()
    return await notebook_service.parameterize_notebook(
        input_path=notebook_path,
        parameters=parameters,
        output_path=output_path if output_path else None
    )
"""


if __name__ == "__main__":
    # Test de démonstration
    result = execute_notebook_with_complex_topic(
        notebook_path="MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker-batch.ipynb",
        topic="Créer un notebook d'analyse de données avec pandas et visualisations interactives pour explorer un dataset de ventes e-commerce avec prédiction de tendances via machine learning",
        complexity="complex",
        framework="python",
        additional_requirements="Utiliser scikit-learn pour ML, plotly pour visualisations interactives"
    )
    
    print(f"\n✅ Résultat de la démonstration:")
    print(f"Success: {result['success']}")
    print(f"Message: {result['message']}")
    print(f"Paramètres injectés: {len(result['parameters_injected'])} paramètres")