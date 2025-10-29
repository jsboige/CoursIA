#!/usr/bin/env python3
"""
Script simple d'inspection des nœuds ComfyUI Qwen WanBridge
Pour identifier les signatures correctes des nœuds sans envoyer de workflow
"""

import json
import sys
import os
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from shared.helpers.comfyui_client import ComfyUIClient

def main():
    """Inspection des nœuds pour diagnostic"""
    
    print("=" * 80)
    print("INSPECTION DES NŒUDS COMFYUI QWEN WANBRIDGE")
    print("=" * 80)
    
    # Créer client avec token depuis .env
    client = ComfyUIClient('http://localhost:8188')
    
    # Récupérer les informations des nœuds disponibles
    try:
        # Appeler l'endpoint system_stats pour avoir les infos
        response = client._make_request("/system_stats", method="GET")
        
        if response and 'object_info' in response:
            object_info = response['object_info']
            
            print("\n📋 NŒUDS DISPONIBLES:")
            
            # Chercher les nœuds Qwen spécifiques
            qwen_nodes = {}
            for node_name, node_info in object_info.items():
                if 'qwen' in node_name.lower() or 'wan' in node_name.lower():
                    qwen_nodes[node_name] = node_info
            
            # Afficher les nœuds Qwen trouvés
            for node_name, node_info in qwen_nodes.items():
                print(f"\n🔧 Nœud: {node_name}")
                print(f"   Type: {node_info.get('display_name', node_name)}")
                
                if 'input' in node_info:
                    print("   Inputs:")
                    for input_name, input_info in node_info['input'].items():
                        input_type = input_info.get('type', 'unknown')
                        input_default = input_info.get('default', None)
                        print(f"     - {input_name}: {input_type} (default: {input_default})")
                
                if 'output' in node_info:
                    print("   Outputs:")
                    for output_name, output_info in node_info['output'].items():
                        output_type = output_info.get('type', 'unknown')
                        print(f"     - {output_name}: {output_type}")
            
            print(f"\n✅ Total nœuds Qwen/Wan trouvés: {len(qwen_nodes)}")
            
        else:
            print("❌ Impossible de récupérer les informations des nœuds")
            
    except Exception as e:
        print(f"❌ Erreur lors de l'inspection: {e}")
    
    print("\n" + "=" * 80)
    print("FIN D'INSPECTION")
    print("=" * 80)

if __name__ == "__main__":
    main()