#!/usr/bin/env python3
"""
Script pour corriger les liens du workflow Qwen

Le workflow utilise un format de liens incorrect (chaînes au lieu de tableaux).
Ce script corrige ce problème.
"""

import json
import sys
from pathlib import Path

def fix_workflow_links(workflow_path: str) -> bool:
    """Corrige les liens du workflow"""
    try:
        # Charger le workflow
        with open(workflow_path, 'r', encoding='utf-8') as f:
            workflow = json.load(f)
        
        print(f"🔧 Correction des liens dans: {workflow_path}")
        
        # Corriger les liens
        if 'links' in workflow:
            original_links = workflow['links']
            fixed_links = []
            
            for i, link in enumerate(original_links):
                if isinstance(link, str):
                    # Extraire les nombres de la chaîne
                    import re
                    numbers = re.findall(r'\d+', link)
                    if len(numbers) >= 5:
                        try:
                            # Format: [source_id, source_slot, target_id, target_slot, "TYPE"]
                            source_id = int(numbers[0])
                            source_slot = int(numbers[1])
                            target_id = int(numbers[2])
                            target_slot = int(numbers[3])
                            fixed_links.append([source_id, source_slot, target_id, target_slot])
                            print(f"  ✅ Lien {i}: {link} → [{source_id}, {source_slot}, {target_id}, {target_slot}]")
                        except ValueError as e:
                            print(f"  ❌ Lien {i}: impossible de parser {link} - {e}")
                            fixed_links.append(link)  # Garder l'original si erreur
                    else:
                        print(f"  ❌ Lien {i}: format invalide {link}")
                        fixed_links.append(link)  # Garder l'original
                else:
                    fixed_links.append(link)
            
            workflow['links'] = fixed_links
            
            # Ajouter les sections manquantes
            if 'groups' not in workflow:
                workflow['groups'] = []
            if 'config' not in workflow:
                workflow['config'] = {}
            if 'extra' not in workflow:
                workflow['extra'] = {}
            if 'version' not in workflow:
                workflow['version'] = 0.4
            
            # Sauvegarder le workflow corrigé
            fixed_path = workflow_path.replace('.json', '_fixed.json')
            with open(fixed_path, 'w', encoding='utf-8') as f:
                json.dump(workflow, f, indent=2)
            
            print(f"✅ Workflow corrigé sauvegardé: {fixed_path}")
            print(f"   Liens corrigés: {len([l for l in original_links if isinstance(l, str)])}")
            return True
        
        return False
        
    except Exception as e:
        print(f"❌ Erreur lors de la correction: {e}")
        return False

def main():
    """Fonction principale"""
    if len(sys.argv) != 2:
        print("Usage: python fix_workflow_links.py <workflow.json>")
        sys.exit(1)
    
    workflow_path = sys.argv[1]
    
    if not Path(workflow_path).exists():
        print(f"❌ Fichier introuvable: {workflow_path}")
        sys.exit(1)
    
    success = fix_workflow_links(workflow_path)
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()