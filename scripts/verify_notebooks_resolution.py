#!/usr/bin/env python3
"""
Script d'analyse exhaustive des 18 notebooks résolus
Compare les versions HEAD et 8ba0c42 pour détecter les modifications de code perdues
"""

import subprocess
import json
import sys
from pathlib import Path
from typing import Dict, List, Any

# Liste des 18 notebooks à vérifier
NOTEBOOKS = [
    "MyIA.AI.Notebooks/GenAI/1_OpenAI_Intro.ipynb",
    "MyIA.AI.Notebooks/GenAI/2_PromptEngineering.ipynb",
    "MyIA.AI.Notebooks/GenAI/3_RAG.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker.ipynb",
    "MyIA.AI.Notebooks/ML/ML-1-Introduction.ipynb",
    "MyIA.AI.Notebooks/Probas/Infer-101.ipynb",
    "MyIA.AI.Notebooks/Probas/Pyro_RSA_Hyperbole.ipynb",
    "MyIA.AI.Notebooks/RL/stable_baseline_3_experience_replay_dqn.ipynb",
    "MyIA.AI.Notebooks/Search/GeneticSharp-EdgeDetection.ipynb",
    "MyIA.AI.Notebooks/Search/Portfolio_Optimization_GeneticSharp.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-0-Environment.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-3-ORTools.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-4-Z3.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-6-Infer.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Linq2Z3.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Planners/Fast-Downward.ipynb",
]


def get_notebook_from_git(commit: str, path: str) -> Dict[str, Any]:
    """Récupère un notebook depuis git à un commit spécifique"""
    try:
        result = subprocess.run(
            ["git", "show", f"{commit}:{path}"],
            capture_output=True,
            text=True,
            check=True
        )
        return json.loads(result.stdout)
    except subprocess.CalledProcessError as e:
        print(f"Erreur lors de la récupération de {path} au commit {commit}")
        print(f"Stderr: {e.stderr}")
        return None
    except json.JSONDecodeError as e:
        print(f"Erreur de parsing JSON pour {path} au commit {commit}")
        print(f"Erreur: {e}")
        return None


def extract_code_cells(notebook: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Extrait les cellules de code avec leur source"""
    if not notebook:
        return []
    
    code_cells = []
    cells = notebook.get("cells", [])
    
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "code":
            source = cell.get("source", [])
            # Normaliser la source (liste ou string)
            if isinstance(source, list):
                source_text = "".join(source)
            else:
                source_text = source
            
            code_cells.append({
                "index": i,
                "source": source_text.strip()
            })
    
    return code_cells


def compare_notebooks(path: str) -> Dict[str, Any]:
    """Compare un notebook entre HEAD et 8ba0c42"""
    print(f"\n{'='*80}")
    print(f"Analyse: {path}")
    print(f"{'='*80}")
    
    # Récupérer les deux versions
    head_notebook = get_notebook_from_git("HEAD", path)
    commit_notebook = get_notebook_from_git("8ba0c42", path)
    
    if not head_notebook or not commit_notebook:
        return {
            "path": path,
            "status": "ERROR",
            "error": "Impossible de récupérer une ou les deux versions"
        }
    
    # Extraire les cellules de code
    head_cells = extract_code_cells(head_notebook)
    commit_cells = extract_code_cells(commit_notebook)
    
    print(f"HEAD: {len(head_cells)} cellules de code")
    print(f"8ba0c42: {len(commit_cells)} cellules de code")
    
    # Comparer le nombre de cellules
    if len(head_cells) != len(commit_cells):
        return {
            "path": path,
            "status": "PROBLÈME",
            "reason": f"Nombre de cellules différent: HEAD={len(head_cells)}, 8ba0c42={len(commit_cells)}",
            "head_count": len(head_cells),
            "commit_count": len(commit_cells)
        }
    
    # Comparer le contenu de chaque cellule
    differences = []
    for i, (head_cell, commit_cell) in enumerate(zip(head_cells, commit_cells)):
        if head_cell["source"] != commit_cell["source"]:
            differences.append({
                "cell_index": i,
                "head_length": len(head_cell["source"]),
                "commit_length": len(commit_cell["source"]),
                "head_preview": head_cell["source"][:100] if head_cell["source"] else "(vide)",
                "commit_preview": commit_cell["source"][:100] if commit_cell["source"] else "(vide)"
            })
    
    if differences:
        print(f"⚠️  DIFFÉRENCES DÉTECTÉES dans {len(differences)} cellule(s)")
        for diff in differences:
            print(f"  Cellule {diff['cell_index']}:")
            print(f"    HEAD: {diff['head_length']} chars - {diff['head_preview'][:50]}...")
            print(f"    8ba0c42: {diff['commit_length']} chars - {diff['commit_preview'][:50]}...")
        
        return {
            "path": path,
            "status": "PROBLÈME",
            "reason": f"{len(differences)} cellule(s) avec des différences de code",
            "differences": differences,
            "head_count": len(head_cells),
            "commit_count": len(commit_cells)
        }
    
    print("✅ OK - Aucune différence de code détectée")
    return {
        "path": path,
        "status": "OK",
        "cell_count": len(head_cells)
    }


def main():
    """Fonction principale"""
    print("="*80)
    print("VÉRIFICATION EXHAUSTIVE DES 18 NOTEBOOKS RÉSOLUS")
    print("="*80)
    print(f"Comparaison HEAD vs 8ba0c42")
    print(f"Total de notebooks à analyser: {len(NOTEBOOKS)}")
    
    results = []
    problems = []
    
    for notebook_path in NOTEBOOKS:
        result = compare_notebooks(notebook_path)
        results.append(result)
        
        if result["status"] != "OK":
            problems.append(result)
    
    # Rapport final
    print("\n" + "="*80)
    print("RAPPORT FINAL")
    print("="*80)
    
    ok_count = sum(1 for r in results if r["status"] == "OK")
    problem_count = sum(1 for r in results if r["status"] == "PROBLÈME")
    error_count = sum(1 for r in results if r["status"] == "ERROR")
    
    print(f"\n✅ OK: {ok_count}/{len(NOTEBOOKS)}")
    print(f"⚠️  PROBLÈMES: {problem_count}/{len(NOTEBOOKS)}")
    print(f"❌ ERREURS: {error_count}/{len(NOTEBOOKS)}")
    
    if problems:
        print("\n" + "="*80)
        print("NOTEBOOKS AVEC PROBLÈMES DÉTECTÉS:")
        print("="*80)
        for problem in problems:
            print(f"\n⚠️  {problem['path']}")
            print(f"   Raison: {problem['reason']}")
            if "differences" in problem:
                print(f"   Détails: {len(problem['differences'])} cellule(s) modifiée(s)")
    
    # Sauvegarder le rapport
    report_path = "docs/RAPPORT_VERIFICATION_NOTEBOOKS_RESOLUTION.json"
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump({
            "summary": {
                "total": len(NOTEBOOKS),
                "ok": ok_count,
                "problems": problem_count,
                "errors": error_count
            },
            "results": results
        }, f, indent=2, ensure_ascii=False)
    
    print(f"\n📄 Rapport détaillé sauvegardé: {report_path}")
    
    # Code de sortie
    if problems:
        print("\n❌ ATTENTION: Des problèmes ont été détectés!")
        print("   ACTION REQUISE: Annuler le commit et corriger les notebooks problématiques")
        sys.exit(1)
    else:
        print("\n✅ SUCCÈS: Tous les notebooks sont OK")
        print("   Vous pouvez finaliser le commit en toute sécurité")
        sys.exit(0)


if __name__ == "__main__":
    main()