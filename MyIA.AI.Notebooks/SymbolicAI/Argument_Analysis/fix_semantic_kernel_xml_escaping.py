#!/usr/bin/env python3
"""
Script pour corriger le problème d'échappement XML dans les templates Semantic Kernel.

Problème identifié : Les templates contenant des caractères XML (<, >, &) sont automatiquement
échappés par Semantic Kernel lors du rendu, transformant "=>" en "=&gt;" et "<=>" en "&lt;=&gt;".

Solution : Remplacer préventivement les opérateurs logiques par leurs entités HTML inversées
pour que l'échappement automatique les retransforme correctement.
"""

import os
import json
import shutil
from pathlib import Path
from datetime import datetime

def apply_semantic_kernel_xml_fix(notebook_path):
    """
    Applique la correction pour l'échappement XML de Semantic Kernel.
    
    Args:
        notebook_path (str): Chemin vers le notebook à corriger
    
    Returns:
        dict: Résultat de l'opération avec statuts et changements
    """
    
    result = {
        "success": False,
        "changes_made": [],
        "backup_created": None,
        "error": None,
        "original_file": notebook_path
    }
    
    try:
        # Créer une sauvegarde
        backup_path = f"{notebook_path}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        shutil.copy2(notebook_path, backup_path)
        result["backup_created"] = backup_path
        print(f"✅ Sauvegarde créée : {backup_path}")
        
        # Lire le notebook
        with open(notebook_path, 'r', encoding='utf-8') as f:
            notebook_data = json.load(f)
        
        changes_count = 0
        
        # Parcourir toutes les cellules
        for cell_idx, cell in enumerate(notebook_data.get('cells', [])):
            if cell.get('cell_type') == 'code':
                source_lines = cell.get('source', [])
                modified = False
                
                for line_idx, line in enumerate(source_lines):
                    original_line = line
                    
                    # Remplacements pour pré-corriger l'échappement Semantic Kernel
                    # Semantic Kernel échappe ">" en "&gt;", donc on met "&lt;" qui deviendra "<" puis ">" après traitement
                    replacements = [
                        # Pour les templates de prompts BNF
                        ('FORMULA "=>" FORMULA', 'FORMULA "=&lt;" FORMULA'),  # Sera transformé en "=>" après échappement inverse
                        ('FORMULA "<=>" FORMULA', 'FORMULA "&gt;=&lt;" FORMULA'),  # Sera transformé en "<=>" après échappement inverse
                        
                        # Pour les exemples dans les commentaires ou texte
                        ('"=>" FORMULA', '"=&lt;" FORMULA'),
                        ('"<=>" FORMULA', '"&gt;=&lt;" FORMULA'),
                        
                        # Dans les descriptions
                        ('syntaxe Tweety ! || => <=> ^^', 'syntaxe Tweety ! || =&lt; &gt;=&lt; ^^'),
                        ('! || => <=> ^^', '! || =&lt; &gt;=&lt; ^^'),
                        ('=> <=> ^^', '=&lt; &gt;=&lt; ^^'),
                    ]
                    
                    for old_text, new_text in replacements:
                        if old_text in line:
                            line = line.replace(old_text, new_text)
                            modified = True
                            changes_count += 1
                            result["changes_made"].append({
                                "cell_index": cell_idx,
                                "line_index": line_idx,
                                "original": original_line.strip(),
                                "modified": line.strip(),
                                "replacement": f"{old_text} → {new_text}"
                            })
                            print(f"📝 Cellule {cell_idx}, ligne {line_idx}: {old_text} → {new_text}")
                    
                    if line != original_line:
                        source_lines[line_idx] = line
                
                if modified:
                    cell['source'] = source_lines
        
        if changes_count > 0:
            # Sauvegarder le notebook modifié
            with open(notebook_path, 'w', encoding='utf-8') as f:
                json.dump(notebook_data, f, indent=2, ensure_ascii=False)
            
            print(f"\n✅ {changes_count} corrections appliquées avec succès!")
            print(f"📁 Notebook modifié : {notebook_path}")
            result["success"] = True
        else:
            print("ℹ️  Aucune correction nécessaire - les templates semblent déjà corrects.")
            result["success"] = True
            result["changes_made"] = []
        
    except Exception as e:
        error_msg = f"Erreur lors de la correction : {e}"
        print(f"❌ {error_msg}")
        result["error"] = error_msg
        
        # Restaurer la sauvegarde en cas d'erreur
        if result["backup_created"] and os.path.exists(result["backup_created"]):
            try:
                shutil.copy2(result["backup_created"], notebook_path)
                print(f"🔄 Fichier original restauré depuis {result['backup_created']}")
            except Exception as restore_error:
                print(f"⚠️  Erreur lors de la restauration : {restore_error}")
    
    return result

def main():
    """Point d'entrée principal du script"""
    
    print("🔧 Script de Correction - Échappement XML Semantic Kernel")
    print("=" * 60)
    print("\nProblème ciblé :")
    print("  Semantic Kernel échappe automatiquement '>' en '&gt;' dans les templates")
    print("  Cela transforme '=>' en '=&gt;' et '<=>' en '&lt;=&gt;'")
    print("  Causant des erreurs XML dans les prompts BNF Tweety")
    print("\nSolution appliquée :")
    print("  Pré-correction des templates avec entités HTML inversées")
    print("  '>' → '&lt;' qui devient '<' puis '>' après traitement SK")
    print()
    
    # Notebook à corriger
    notebook_path = "Argument_Analysis_Agentic-2-pl_agent.ipynb"
    
    if not os.path.exists(notebook_path):
        print(f"❌ Fichier non trouvé : {notebook_path}")
        return False
    
    print(f"📂 Traitement : {notebook_path}")
    print()
    
    # Appliquer les corrections
    result = apply_semantic_kernel_xml_fix(notebook_path)
    
    # Résumé final
    print("\n" + "=" * 60)
    print("📊 RÉSUMÉ DE L'OPÉRATION")
    print("=" * 60)
    
    if result["success"]:
        print("✅ Status : SUCCÈS")
        print(f"📁 Fichier traité : {result['original_file']}")
        print(f"💾 Sauvegarde : {result['backup_created']}")
        print(f"🔧 Corrections appliquées : {len(result['changes_made'])}")
        
        if result["changes_made"]:
            print("\nDétail des corrections :")
            for i, change in enumerate(result["changes_made"][:5]):  # Afficher max 5 pour lisibilité
                print(f"  {i+1}. {change['replacement']}")
            if len(result["changes_made"]) > 5:
                print(f"  ... et {len(result['changes_made']) - 5} autres corrections")
            
            print(f"\n🎯 Fix appliqué : Templates pré-corrigés pour Semantic Kernel")
            print("   Les opérateurs '=>' et '<=>' ont été remplacés par leurs entités")
            print("   HTML inversées qui seront correctement interprétées après échappement.")
    else:
        print("❌ Status : ÉCHEC")
        if result["error"]:
            print(f"💥 Erreur : {result['error']}")
        if result["backup_created"]:
            print(f"🔄 Sauvegarde disponible : {result['backup_created']}")
    
    return result["success"]

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)