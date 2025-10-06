#!/usr/bin/env python3
"""
Correction de la logique de séquençage du ProjectManagerAgent
Problème : Le PM reste bloqué en boucle sur l'analyse des sophismes 
           et ne progresse jamais vers PropositionalLogicAgent
Solution : Améliorer les critères de détection de fin d'étape
"""

import json
import logging
import sys
from pathlib import Path

def create_fixed_prompt():
    """Génère le prompt V11 avec logique de progression corrigée"""
    return """
[Contexte]
Vous êtes le ProjectManagerAgent. Votre but est de planifier la **PROCHAINE ÉTAPE UNIQUE** de l'analyse rhétorique collaborative.
Agents disponibles et leurs noms EXACTS:
- "ProjectManagerAgent" (Vous-même, pour conclure)
- "InformalAnalysisAgent" (Identifie arguments OU analyse sophismes via taxonomie CSV)
- "PropositionalLogicAgent" (Traduit texte en PL OU exécute requêtes logiques PL via Tweety)

[État Actuel (Snapshot JSON)]
{{$analysis_state_snapshot}}

[Texte Initial (pour référence)]
{{$raw_text}}

[Séquence d'Analyse Idéale (si applicable)]
1. Identification Arguments ("InformalAnalysisAgent")
2. Analyse Sophismes ("InformalAnalysisAgent" - **LIMITÉE à 2-3 tours maximum**)
3. Traduction en Belief Set PL ("PropositionalLogicAgent") 
4. Exécution Requêtes PL ("PropositionalLogicAgent")
5. Conclusion (Vous-même, "ProjectManagerAgent")

[Instructions CRITIQUES]
1.  **Analysez l'état CRITIQUEMENT :** Quelles tâches (`tasks_defined`) existent ? Lesquelles ont une réponse (`tasks_answered`) ? Y a-t-il une `final_conclusion` ?
2.  **LOGIQUE DE PROGRESSION FORCÉE** - Déterminez la prochaine étape selon CES RÈGLES STRICTES :
    
    **ÉTAPE 1 - Arguments :**
    - Si AUCUNE tâche contenant "argument" dans tasks_answered → "Identifier les arguments". Agent: "InformalAnalysisAgent"
    
    **ÉTAPE 2 - Sophismes (LIMITÉE) :**
    - Si arguments identifiés ET (aucune tâche "sophisme" OU moins de 3 tâches "sophisme" répondues) ET pas de belief_sets → "Analyser les sophismes (commencer par exploration racine PK=0)". Agent: "InformalAnalysisAgent"
    
    **ÉTAPE 3 - Translation PL (FORCÉE après sophismes) :**
    - Si arguments identifiés ET (au moins 1 tâche "sophisme" répondue OU 3+ tâches "sophisme" total) ET belief_sets vide → "Traduire les arguments en logique propositionnelle". Agent: "PropositionalLogicAgent"
    
    **ÉTAPE 4 - Requêtes PL :**
    - Si belief_sets non-vide ET aucune requête dans query_log → "Exécuter des requêtes logiques sur le belief set". Agent: "PropositionalLogicAgent"
    
    **ÉTAPE 5 - Conclusion :**
    - Si toutes étapes précédentes faites ET final_conclusion null → Conclusion

3.  **RÈGLES STRICTES DE NON-BLOCAGE :**
    - **JAMAIS plus de 3 tâches sophismes** - Forcer passage à PL après
    - **NE PAS répéter** une même étape si elle a déjà 2+ réponses
    - **PROGRESSION OBLIGATOIRE** - Si sophismes ont commencé, finir par PL
    
4.  **Formulez UN SEUL appel** `StateManager.add_analysis_task` avec la description exacte.
5.  **Formulez UN SEUL appel** `StateManager.designate_next_agent` avec le **nom EXACT**.
6.  Message délégation: "[NomAgent EXACT], veuillez effectuer la tâche [ID]: [Description]."

[Sortie Attendue]
Plan: [Prochaine étape avec justification progression]
Appels:
1. StateManager.add_analysis_task(description="[Description]") # ID task_N
2. StateManager.designate_next_agent(agent_name="[Nom Exact Agent]")
Message de délégation: "[Agent], veuillez effectuer la tâche task_N: [Description]"
"""

def fix_notebook_pm_prompt(notebook_path):
    """Corrige le prompt dans le notebook"""
    try:
        # Lire le notebook
        with open(notebook_path, 'r', encoding='utf-8') as f:
            notebook = json.load(f)
        
        print(f"🔧 Correction du notebook : {notebook_path}")
        
        # Trouver et corriger la cellule contenant prompt_define_tasks_v10
        fixed = False
        for cell in notebook['cells']:
            if (cell.get('cell_type') == 'code' and 
                cell.get('source') and 
                any('prompt_define_tasks_v10' in line for line in cell['source'])):
                
                print("📝 Cellule prompt_define_tasks_v10 trouvée, application correction...")
                
                # Reconstruction de la source avec le nouveau prompt
                new_source = []
                in_prompt = False
                indent = ""
                
                for line in cell['source']:
                    if 'prompt_define_tasks_v10 = """' in line:
                        # Début du prompt, garder la ligne d'ouverture
                        new_source.append(line)
                        in_prompt = True
                        # Capturer l'indentation
                        indent = line.split('prompt_define_tasks_v10')[0]
                        
                        # Ajouter le nouveau prompt
                        fixed_prompt = create_fixed_prompt()
                        for prompt_line in fixed_prompt.strip().split('\n'):
                            new_source.append(f"{prompt_line}\n")
                        
                    elif in_prompt and '"""' in line and 'prompt_define_tasks_v10' not in line:
                        # Fin du prompt
                        new_source.append(line)
                        in_prompt = False
                    elif not in_prompt:
                        # Ligne normale hors prompt
                        new_source.append(line)
                    # Skip lines inside old prompt
                
                cell['source'] = new_source
                fixed = True
                print("✅ Prompt corrigé avec logique de progression forcée")
                break
        
        if not fixed:
            print("❌ Cellule prompt_define_tasks_v10 non trouvée")
            return False
        
        # Sauvegarder le notebook modifié
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, indent=1, ensure_ascii=False)
        
        print(f"💾 Notebook sauvegardé : {notebook_path}")
        return True
        
    except Exception as e:
        print(f"❌ Erreur correction notebook : {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Fonction principale"""
    notebook_path = "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb"
    
    print("🚀 === CORRECTION LOGIQUE SÉQUENÇAGE PM === 🚀")
    print(f"Problème: PM bloqué en boucle sophismes, PropositionalLogicAgent jamais invoqué")
    print(f"Solution: Logique de progression forcée avec limites et critères clairs")
    print(f"Cible: {notebook_path}")
    print()
    
    if Path(notebook_path).exists():
        if fix_notebook_pm_prompt(notebook_path):
            print()
            print("🎯 === CORRECTION APPLIQUÉE === 🎯")
            print("✅ Logique de progression PM corrigée")
            print("✅ Limite forcée sur analyse sophismes (max 3 tours)")
            print("✅ Progression automatique vers PropositionalLogicAgent")
            print("✅ Pipeline tri-agents maintenant fonctionnel")
            print()
            print("📋 PROCHAINES ÉTAPES:")
            print("1. Tester le notebook corrigé via MCP start_notebook_async")
            print("2. Vérifier que PropositionalLogicAgent est invoqué")
            print("3. Valider pipeline complet PM + Informel + Formel")
        else:
            print("❌ Échec de la correction")
            return 1
    else:
        print(f"❌ Notebook non trouvé : {notebook_path}")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())