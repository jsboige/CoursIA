#!/usr/bin/env python3
"""
Script d'inspection du workflow ComfyUI Qwen WanBridge
Pour identifier les erreurs de connexion et validation
"""

import json
import sys
import os
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from shared.helpers.comfyui_client import ComfyUIClient

def main():
    """Inspection du workflow pour diagnostic"""
    
    print("=" * 80)
    print("INSPECTION WORKFLOW COMFYUI QWEN WANBRIDGE")
    print("=" * 80)
    
    # Créer client avec token depuis .env
    client = ComfyUIClient('http://localhost:8188')
    
    # Générer workflow en utilisant la méthode publique qui contient le workflow WanBridge
    workflow = client.generate_text2image('test prompt')
    
    print("\n📋 WORKFLOW COMPLET:")
    print(json.dumps(workflow, indent=2))
    
    print("\n🔍 ANALYSE DES CONNEXIONS:")
    
    # Analyser chaque nœud
    for node_id, node in workflow.items():
        print(f"\nNœud {node_id} ({node['class_type']}):")
        
        # Analyser les inputs
        if 'inputs' in node:
            for input_name, input_value in node['inputs'].items():
                if isinstance(input_value, list) and len(input_value) == 2:
                    source_node, output_index = input_value
                    print(f"  Input '{input_name}' -> [{source_node}, {output_index}]")
                    
                    # Vérifier si le nœud source existe
                    if source_node not in workflow:
                        print(f"    ❌ ERREUR: Nœud source {source_node} n'existe pas!")
                    else:
                        source_node_data = workflow[source_node]
                        class_type = source_node_data.get('class_type', 'Unknown')
                        print(f"    ✅ Connecté à {class_type}[{output_index}]")
                else:
                    print(f"  Input '{input_name}': {input_value}")
    
    print("\n" + "=" * 80)
    print("FIN D'INSPECTION")
    print("=" * 80)

if __name__ == "__main__":
    main()