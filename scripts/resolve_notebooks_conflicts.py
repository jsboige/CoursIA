#!/usr/bin/env python3
"""
Script de résolution batch des 18 notebooks en conflit (commit "MAJ Notebooks")

STRATÉGIE:
- Tous les conflits suivent le pattern: HEAD = sans outputs, 8ba0c42 = avec outputs
- Pour le versioning Git, on préfère TOUJOURS les notebooks sans outputs
- Solution: git checkout --ours (prendre HEAD) pour tous les notebooks

FICHIERS CONCERNÉS:
1. MyIA.AI.Notebooks/GenAI/1_OpenAI_Intro.ipynb
2. MyIA.AI.Notebooks/GenAI/2_PromptEngineering.ipynb
3. MyIA.AI.Notebooks/GenAI/3_RAG.ipynb
4. MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb
5. MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker.ipynb
6. MyIA.AI.Notebooks/ML/ML-1-Introduction.ipynb
7. MyIA.AI.Notebooks/Probas/Infer-101.ipynb
8. MyIA.AI.Notebooks/Probas/Pyro_RSA_Hyperbole.ipynb
9. MyIA.AI.Notebooks/RL/stable_baseline_3_experience_replay_dqn.ipynb
10. MyIA.AI.Notebooks/Search/GeneticSharp-EdgeDetection.ipynb
11. MyIA.AI.Notebooks/Search/Portfolio_Optimization_GeneticSharp.ipynb
12. MyIA.AI.Notebooks/Sudoku/Sudoku-0-Environment.ipynb
13. MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb
14. MyIA.AI.Notebooks/Sudoku/Sudoku-3-ORTools.ipynb
15. MyIA.AI.Notebooks/Sudoku/Sudoku-4-Z3.ipynb
16. MyIA.AI.Notebooks/Sudoku/Sudoku-6-Infer.ipynb
17. MyIA.AI.Notebooks/SymbolicAI/Linq2Z3.ipynb
18. MyIA.AI.Notebooks/SymbolicAI/Planners/Fast-Downward.ipynb
"""

import subprocess
import sys
from pathlib import Path

# Liste des notebooks en conflit
CONFLICTED_NOTEBOOKS = [
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
    "MyIA.AI.Notebooks/SymbolicAI/Planners/Fast-Downward.ipynb"
]

def verify_conflicts():
    """Vérifie que tous les fichiers sont bien en conflit"""
    print("🔍 Vérification des conflits...")
    
    result = subprocess.run(
        ["git", "status", "--short"],
        capture_output=True,
        text=True,
        check=True
    )
    
    conflicted = []
    for line in result.stdout.splitlines():
        if line.startswith("UU "):  # Unmerged, both modified
            filepath = line[3:].strip()
            conflicted.append(filepath)
    
    # Vérifier que tous nos notebooks sont présents
    missing = set(CONFLICTED_NOTEBOOKS) - set(conflicted)
    extra = set(conflicted) - set(CONFLICTED_NOTEBOOKS)
    
    if missing:
        print(f"⚠️  Fichiers attendus mais non en conflit: {missing}")
    
    if extra:
        print(f"⚠️  Fichiers en conflit non attendus: {extra}")
    
    print(f"✅ Trouvé {len(conflicted)} fichiers en conflit")
    return conflicted

def verify_conflict_pattern(filepath):
    """Vérifie que le conflit suit le pattern attendu (HEAD sans outputs)"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Vérifier la présence des marqueurs de conflit
        has_head = '<<<<<<< HEAD' in content
        has_separator = '=======' in content
        has_merge = '>>>>>>>' in content
        
        if not (has_head and has_separator and has_merge):
            print(f"⚠️  {filepath}: Pattern de conflit inhabituel")
            return False
        
        return True
    except Exception as e:
        print(f"❌ Erreur lors de la vérification de {filepath}: {e}")
        return False

def resolve_conflicts():
    """Résout tous les conflits en prenant HEAD (version sans outputs)"""
    
    print("\n" + "="*70)
    print("RÉSOLUTION BATCH DES CONFLITS DE NOTEBOOKS")
    print("="*70)
    print("\nSTRATÉGIE: Prendre HEAD (notebooks sans outputs)")
    print("RAISON: Bonne pratique Git - ne pas versionner les outputs\n")
    
    # Vérifier les conflits
    conflicted_files = verify_conflicts()
    
    if not conflicted_files:
        print("❌ Aucun fichier en conflit trouvé!")
        return False
    
    # Vérifier le pattern de conflit sur quelques échantillons
    print("\n🔍 Vérification du pattern de conflit sur 3 échantillons...")
    samples = conflicted_files[:3]
    for sample in samples:
        if not verify_conflict_pattern(sample):
            print(f"❌ Pattern inhabituel détecté dans {sample}")
            response = input("Continuer quand même? (o/N): ")
            if response.lower() != 'o':
                return False
    
    print("✅ Pattern de conflit vérifié\n")
    
    # Résoudre tous les conflits
    print(f"📝 Résolution de {len(conflicted_files)} notebooks...\n")
    
    resolved = []
    failed = []
    
    for filepath in conflicted_files:
        try:
            # Prendre la version HEAD (ours)
            result = subprocess.run(
                ["git", "checkout", "--ours", filepath],
                capture_output=True,
                text=True,
                check=True
            )
            
            # Stager le fichier résolu
            subprocess.run(
                ["git", "add", filepath],
                check=True
            )
            
            resolved.append(filepath)
            print(f"✅ {filepath}")
            
        except subprocess.CalledProcessError as e:
            failed.append(filepath)
            print(f"❌ {filepath}: {e.stderr}")
    
    # Résumé
    print("\n" + "="*70)
    print("RÉSUMÉ")
    print("="*70)
    print(f"✅ Résolus: {len(resolved)}/{len(conflicted_files)}")
    
    if failed:
        print(f"❌ Échecs: {len(failed)}")
        for f in failed:
            print(f"   - {f}")
        return False
    
    print("\n✅ Tous les conflits ont été résolus avec succès!")
    print("\nStratégie appliquée:")
    print("  - Pris HEAD (version sans outputs) pour tous les notebooks")
    print("  - Fichiers automatiquement stagés")
    print("\nProchaine étape:")
    print("  git rebase --continue")
    
    return True

if __name__ == "__main__":
    try:
        success = resolve_conflicts()
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n\n⚠️  Opération annulée par l'utilisateur")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Erreur inattendue: {e}")
        sys.exit(1)