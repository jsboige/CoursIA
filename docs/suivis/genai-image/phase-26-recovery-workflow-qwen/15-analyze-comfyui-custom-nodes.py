#!/usr/bin/env python3
"""
Script d'analyse des custom nodes ComfyUI utilisés dans le workflow de référence.
Permet d'extraire la structure du workflow et de comparer avec l'implémentation actuelle.
"""

import json
from pathlib import Path
from typing import Dict, List

def analyze_workflow(workflow_path: str) -> None:
    """Analyse le workflow JSON et affiche les nodes Qwen utilisés."""
    
    with open(workflow_path, 'r', encoding='utf-8') as f:
        workflow = json.load(f)
    
    print("=" * 80)
    print("ANALYSE DU WORKFLOW DE RÉFÉRENCE COMFYUI-QWEN")
    print("=" * 80)
    print()
    
    # 1. Extraire tous les nodes Qwen
    qwen_nodes = [
        node for node in workflow['nodes'] 
        if 'Qwen' in node['type']
    ]
    
    print(f"1. NODES QWEN TROUVÉS ({len(qwen_nodes)}):")
    print("-" * 80)
    for node in qwen_nodes:
        print(f"  ID {node['id']}: {node['type']}")
        if 'inputs' in node and node['inputs']:
            print(f"    Inputs: {list(node['inputs'][0].keys()) if node['inputs'] else 'None'}")
    print()
    
    # 2. Analyser spécifiquement QwenVLCLIPLoader et QwenVLTextEncoder
    print("2. ANALYSE DÉTAILLÉE DES NODES CRITIQUES:")
    print("-" * 80)
    
    for node in qwen_nodes:
        if node['type'] == 'QwenVLCLIPLoader':
            print(f"\n  QwenVLCLIPLoader (ID {node['id']}):")
            print(f"    Widgets: {node.get('widgets_values', [])}")
            if 'outputs' in node:
                for i, output in enumerate(node['outputs']):
                    print(f"    Output {i}: {output['name']} (type: {output['type']})")
                    print(f"      Links: {output.get('links', [])}")
        
        elif node['type'] == 'QwenVLTextEncoder':
            print(f"\n  QwenVLTextEncoder (ID {node['id']}):")
            print(f"    Inputs:")
            for input_spec in node.get('inputs', []):
                link_id = input_spec.get('link')
                print(f"      - {input_spec['name']} (type: {input_spec['type']}, link: {link_id})")
    
    # 3. Construire le graphe de connexions pour les nodes Qwen
    print("\n3. GRAPHE DE CONNEXIONS (NODES QWEN):")
    print("-" * 80)
    
    # Créer un mapping link_id -> (source_node_id, source_output_index)
    link_map = {}
    for node in workflow['nodes']:
        if 'outputs' in node:
            for output_idx, output in enumerate(node['outputs']):
                if 'links' in output and output['links']:
                    for link_id in output['links']:
                        link_map[link_id] = (node['id'], output_idx, output['name'])
    
    for node in qwen_nodes:
        print(f"\n  Node {node['id']} ({node['type']}):")
        if 'inputs' in node and node['inputs']:
            for input_spec in node['inputs']:
                link_id = input_spec.get('link')
                if link_id and link_id in link_map:
                    source_id, source_idx, source_name = link_map[link_id]
                    print(f"    <- Input '{input_spec['name']}' from Node {source_id} output '{source_name}'")
    
    # 4. Générer un workflow simplifié pour Python
    print("\n4. STRUCTURE WORKFLOW SIMPLIFIÉE POUR PYTHON:")
    print("-" * 80)
    print("\nworkflow = {")
    for node in qwen_nodes:
        print(f"    \"{node['id']}\": {{")
        print(f"        \"class_type\": \"{node['type']}\",")
        print(f"        \"inputs\": {{")
        
        # Pour QwenVLCLIPLoader
        if node['type'] == 'QwenVLCLIPLoader':
            if 'widgets_values' in node and node['widgets_values']:
                print(f"            \"clip_name\": \"{node['widgets_values'][0]}\"")
        
        # Pour QwenVLTextEncoder
        elif node['type'] == 'QwenVLTextEncoder':
            for input_spec in node.get('inputs', []):
                link_id = input_spec.get('link')
                if link_id and link_id in link_map:
                    source_id, source_idx, source_name = link_map[link_id]
                    print(f"            \"{input_spec['name']}\": [\"{source_id}\", {source_idx}],")
        
        print(f"        }}")
        print(f"    }},")
    print("}")
    
    # 5. Résumé des découvertes
    print("\n5. RÉSUMÉ DES DÉCOUVERTES CRITIQUES:")
    print("-" * 80)
    print("\n  ✅ Le workflow de référence utilise QwenVLCLIPLoader pour générer le CLIP")
    print("  ✅ QwenVLTextEncoder requiert 3 inputs: clip, text, mode")
    print("  ❌ Mon workflow actuel utilisait QwenModelManagerWrapper (incorrect)")
    print("  ❌ Mon workflow fournissait text_encoder et processor (n'existent pas)")
    print()
    print("  SOLUTION:")
    print("    1. Remplacer QwenModelManagerWrapper par QwenVLCLIPLoader")
    print("    2. Ajuster les inputs de QwenVLTextEncoder pour utiliser clip, text, mode")
    print()

if __name__ == '__main__':
    workflow_path = Path(__file__).parent / 'workflow-reference-qwen-edit.json'
    analyze_workflow(str(workflow_path))