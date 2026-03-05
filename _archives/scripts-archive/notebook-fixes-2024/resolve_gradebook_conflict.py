#!/usr/bin/env python3
"""
Script de résolution intelligente du conflit dans GradeBook.ipynb
Combine le meilleur des deux versions :
- La CORRECTION de a54caf6 : Constructeur ProjectEvaluation(studentRecords, professorEmail)
- La gestion d'erreurs de HEAD : Collection puis affichage via errorMessages
"""

import json
import sys
from pathlib import Path

def resolve_conflict():
    notebook_path = Path("MyIA.AI.Notebooks/GradeBook.ipynb")
    
    if not notebook_path.exists():
        print(f"Erreur: {notebook_path} n'existe pas")
        return False
    
    # Lire le fichier
    with open(notebook_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Vérifier qu'il y a des conflits
    if '<<<<<<< HEAD' not in content:
        print("Aucun conflit détecté dans le fichier")
        return True
    
    print(f"Conflits détectés: {content.count('<<<<<<< HEAD')}")
    
    # Résolution conflit 1: Constructeur ProjectEvaluation
    # On garde: errorMessages de HEAD + correction constructeur de a54caf6
    content = content.replace(
        '''<<<<<<< HEAD
     "\n",
     "var projectEvaluations = new List<ProjectEvaluation>();\n",
     "var errorMessages = new List<string>();\n",
     "\n",
     "for (int i = 0; i < evaluations.Count; i++)\n",
     "{\n",
     "    var projectEvaluation = new ProjectEvaluation() { ProfessorEmail = professorEmail };\n",
=======
     "var projectEvaluations = new List<ProjectEvaluation>();  \n",
     "\n",
     "for (int i = 0; i < evaluations.Count; i++)\n",
     "{\n",
     "    // CORRECTION : On passe la liste des étudiants et l'email du prof au constructeur\n",
     "    var projectEvaluation = new ProjectEvaluation(studentRecords, professorEmail);\n",
>>>>>>> a54caf6 (Notebook recup #2)''',
        '''     "\n",
     "var projectEvaluations = new List<ProjectEvaluation>();\n",
     "var errorMessages = new List<string>();\n",
     "\n",
     "for (int i = 0; i < evaluations.Count; i++)\n",
     "{\n",
     "    // CORRECTION : On passe la liste des étudiants et l'email du prof au constructeur\n",
     "    var projectEvaluation = new ProjectEvaluation(studentRecords, professorEmail);\n",'''
    )
    
    # Résolution conflit 2: Gestion d'erreur groupe sans membre
    # On garde la collection d'erreurs de HEAD (pas le throw)
    content = content.replace(
        '''<<<<<<< HEAD
     "\n",
     "        // Vérifier que chaque groupe a au moins un membre\n",
     "        bool hasMember = gEval.GroupMembers.Count > 0;\n",
     "        if (!hasMember)\n",
     "        {\n",
     "            errorMessages.Add($\"Le groupe '{gEval.Groupe}' n'a pas de membre. Veuillez compléter avant de continuer.\");\n",
=======
     "        //Vérifier que chaque groupe a au moins un membre\n",
     "        bool hasMember = gEval.GroupMembers.Count > 0;\n",
     "        if (!hasMember)\n",
     "        {\n",
     "            throw new Exception($\"Le groupe '{gEval.Groupe}' n'a pas de membre. Veuillez compléter avant de continuer.\");\n",
>>>>>>> a54caf6 (Notebook recup #2)''',
        '''     "\n",
     "        // Vérifier que chaque groupe a au moins un membre\n",
     "        bool hasMember = gEval.GroupMembers.Count > 0;\n",
     "        if (!hasMember)\n",
     "        {\n",
     "            errorMessages.Add($\"Le groupe '{gEval.Groupe}' n'a pas de membre. Veuillez compléter avant de continuer.\");\n",'''
    )
    
    # Résolution conflit 3: Fin du bloc + nouvelle cellule de a54caf6
    # On garde tout de HEAD + on ajoute la cellule de debugging de a54caf6
    content = content.replace(
        '''<<<<<<< HEAD
     "}\n",
     "\n",
     "// Si des erreurs ont été collectées, les afficher et arrêter l'exécution\n",
     "if (errorMessages.Any())\n",
     "{\n",
     "    foreach (var errorMessage in errorMessages)\n",
     "    {\n",
     "        display(errorMessage);\n",
     "    }\n",
     "    throw new Exception(\"Des erreurs ont été détectées lors de l'appariement des élèves. Veuillez corriger les erreurs ci-dessus avant de continuer.\");\n",
=======
     "}\n"''',
        '''     "}\n",
     "\n",
     "// Si des erreurs ont été collectées, les afficher et arrêter l'exécution\n",
     "if (errorMessages.Any())\n",
     "{\n",
     "    foreach (var errorMessage in errorMessages)\n",
     "    {\n",
     "        display(errorMessage);\n",
     "    }\n",
     "    throw new Exception(\"Des erreurs ont été détectées lors de l'appariement des élèves. Veuillez corriger les erreurs ci-dessus avant de continuer.\");\n",
     "}\n"'''
    )
    
    # Supprimer les restes de marqueurs de conflit
    remaining_conflicts = content.count('<<<<<<< HEAD')
    if remaining_conflicts > 0:
        print(f"ATTENTION: {remaining_conflicts} conflits non résolus restants!")
        # Afficher contexte des conflits restants
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if '<<<<<<< HEAD' in line:
                print(f"\nConflit ligne {i}:")
                print('\n'.join(lines[max(0, i-2):min(len(lines), i+15)]))
        return False
    
    # Écrire le fichier résolu
    with open(notebook_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print("✅ Conflits résolus avec succès!")
    print("Stratégie appliquée:")
    print("  - Constructeur corrigé de a54caf6 avec studentRecords")
    print("  - Gestion d'erreurs améliorée de HEAD (collection + affichage)")
    print("  - Code de debugging/logging de a54caf6 préservé")
    
    return True

if __name__ == "__main__":
    success = resolve_conflict()
    sys.exit(0 if success else 1)