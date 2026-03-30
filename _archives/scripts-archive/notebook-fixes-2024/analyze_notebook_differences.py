#!/usr/bin/env python3
"""
Script d'analyse détaillée des différences entre notebooks
Affiche les différences réelles de code pour évaluation humaine
"""

import subprocess
import json
import sys
from pathlib import Path
from typing import Dict, List, Any
import difflib

def get_notebook_from_git(commit: str, path: str) -> Dict[str, Any]:
    """Récupère un notebook depuis git"""
    try:
        result = subprocess.run(
            ["git", "show", f"{commit}:{path}"],
            capture_output=True,
            text=True,
            check=True
        )
        return json.loads(result.stdout)
    except Exception as e:
        print(f"Erreur: {e}")
        return None

def extract_code_cells(notebook: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Extrait les cellules de code"""
    if not notebook:
        return []
    
    code_cells = []
    cells = notebook.get("cells", [])
    
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "code":
            source = cell.get("source", [])
            if isinstance(source, list):
                source_text = "".join(source)
            else:
                source_text = source
            
            code_cells.append({
                "index": i,
                "source": source_text.strip()
            })
    
    return code_cells

def show_detailed_diff(path: str):
    """Affiche les différences détaillées pour un notebook"""
    print(f"\n{'='*100}")
    print(f"ANALYSE DÉTAILLÉE: {path}")
    print(f"{'='*100}\n")
    
    head = get_notebook_from_git("HEAD", path)
    commit = get_notebook_from_git("8ba0c42", path)
    
    head_cells = extract_code_cells(head)
    commit_cells = extract_code_cells(commit)
    
    print(f"HEAD: {len(head_cells)} cellules")
    print(f"8ba0c42: {len(commit_cells)} cellules")
    
    if len(head_cells) != len(commit_cells):
        print(f"\n⚠️ NOMBRE DE CELLULES DIFFÉRENT!")
        print(f"HEAD a {len(head_cells) - len(commit_cells):+d} cellules")
        
        # Si HEAD a plus de cellules, ce sont de NOUVELLES cellules (pas de perte)
        if len(head_cells) > len(commit_cells):
            print("\n✅ HEAD contient PLUS de cellules → Pas de perte de code")
            print("   Nouvelles cellules dans HEAD:")
            # Afficher les cellules supplémentaires
            for i in range(len(commit_cells), len(head_cells)):
                print(f"\n   Cellule {i} (NOUVELLE dans HEAD):")
                print(f"   {head_cells[i]['source'][:200]}...")
        else:
            print("\n❌ HEAD contient MOINS de cellules → PERTE POTENTIELLE!")
        return
    
    # Comparer cellule par cellule
    print("\n" + "-"*100)
    print("DIFFÉRENCES DE CONTENU:")
    print("-"*100)
    
    for i, (head_cell, commit_cell) in enumerate(zip(head_cells, commit_cells)):
        if head_cell["source"] != commit_cell["source"]:
            print(f"\n{'='*100}")
            print(f"CELLULE {i}:")
            print(f"{'='*100}")
            
            # Calculer le diff
            head_lines = head_cell["source"].split('\n')
            commit_lines = commit_cell["source"].split('\n')
            
            diff = list(difflib.unified_diff(
                commit_lines, 
                head_lines,
                fromfile=f'8ba0c42 (cellule {i})',
                tofile=f'HEAD (cellule {i})',
                lineterm=''
            ))
            
            if diff:
                print('\n'.join(diff[:50]))  # Limiter à 50 lignes
                if len(diff) > 50:
                    print(f"\n... ({len(diff) - 50} lignes supplémentaires)")

# Notebooks à analyser en détail (ceux avec problèmes significatifs)
CRITICAL_NOTEBOOKS = [
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker.ipynb",
    "MyIA.AI.Notebooks/Search/Portfolio_Optimization_GeneticSharp.ipynb",
    "MyIA.AI.Notebooks/Sudoku/Sudoku-0-Environment.ipynb",
]

if __name__ == "__main__":
    print("="*100)
    print("ANALYSE DÉTAILLÉE DES NOTEBOOKS CRITIQUES")
    print("="*100)
    
    for notebook in CRITICAL_NOTEBOOKS:
        show_detailed_diff(notebook)
    
    print("\n" + "="*100)
    print("FIN DE L'ANALYSE")
    print("="*100)