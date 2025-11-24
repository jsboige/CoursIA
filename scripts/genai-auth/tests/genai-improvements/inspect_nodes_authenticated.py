#!/usr/bin/env python3
"""
Script d'inspection des nœuds ComfyUI avec authentification via ComfyUIClient
Utilise le client existant pour bénéficier de l'authentification automatique
"""

import sys
import os
import json
from pathlib import Path

# Ajouter le répertoire shared au path
sys.path.append(str(Path(__file__).parent / "shared"))

from helpers.comfyui_client import ComfyUIClient

def inspect_qwen_nodes():
    """Inspecte les nœuds Qwen pour comprendre leurs signatures I/O"""
    
    print("🔍 INSPECTION DES NŒUDS QWEN AVEC AUTHENTIFICATION")
    print("=" * 60)
    
    try:
        # Initialiser le client avec authentification automatique
        # URL du serveur ComfyUI (adapter selon votre configuration)
        server_url = "http://localhost:8188"
        client = ComfyUIClient(server_url=server_url)
        
        print("✅ Client ComfyUI initialisé avec authentification")
        
        # Appeler l'endpoint system_stats pour obtenir la liste des nœuds
        print("📋 Récupération des nœuds disponibles...")
        response = client._make_request("GET", "/system_stats")
        
        if response.status_code == 200:
            data = response.json()
            nodes = data.get("nodes", {})
            
            print(f"📊 {len(nodes)} nœuds trouvés")
            
            # Chercher les nœuds Qwen spécifiques
            qwen_nodes = {}
            for node_id, node_info in nodes.items():
                node_name = node_info.get("display_name", "") or node_info.get("name", "")
                if "qwen" in node_name.lower() or "wan" in node_name.lower():
                    qwen_nodes[node_id] = node_info
            
            print(f"🎯 {len(qwen_nodes)} nœuds Qwen/Wan trouvés:")
            
            # Analyser les nœuds clés
            key_nodes = [
                "QwenVLCLIPLoader",
                "TextEncodeQwenImageEdit", 
                "QwenVLEmptyLatent",
                "QwenImageSamplerNode",
                "VAEDecode"
            ]
            
            for node_name in key_nodes:
                found = False
                for node_id, node_info in qwen_nodes.items():
                    display_name = node_info.get("display_name", "")
                    if display_name == node_name:
                        found = True
                        print(f"\n🔧 {node_name}:")
                        print(f"   ID: {node_id}")
                        print(f"   Display Name: {display_name}")
                        
                        # Analyser les inputs
                        inputs = node_info.get("input", {})
                        if inputs:
                            print(f"   Inputs ({len(inputs)}):")
                            for input_name, input_info in inputs.items():
                                input_type = input_info.get("type", "unknown")
                                input_default = input_info.get("default", None)
                                print(f"     - {input_name}: {input_type}" + 
                                      (f" (default: {input_default})" if input_default is not None else ""))
                        
                        # Analyser les outputs
                        outputs = node_info.get("output", {})
                        if outputs:
                            print(f"   Outputs ({len(outputs)}):")
                            for output_name, output_info in outputs.items():
                                output_type = output_info.get("type", "unknown")
                                print(f"     - {output_name}: {output_type}")
                        break
                
                if not found:
                    print(f"\n❌ {node_name}: NON TROUVÉ")
            
            return qwen_nodes
            
        else:
            print(f"❌ Erreur HTTP {response.status_code}: {response.text}")
            return None
            
    except Exception as e:
        print(f"❌ Erreur lors de l'inspection: {e}")
        return None

if __name__ == "__main__":
    qwen_nodes = inspect_qwen_nodes()
    
    if qwen_nodes:
        print(f"\n🎯 INSPECTION RÉUSSIE: {len(qwen_nodes)} nœuds Qwen analysés")
        
        # Sauvegarder les résultats pour analyse
        output_file = Path(__file__).parent / "qwen_nodes_analysis.json"
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(qwen_nodes, f, indent=2, ensure_ascii=False)
        
        print(f"💾 Résultats sauvegardés dans: {output_file}")
    else:
        print("\n❌ INSPECTION ÉCHOUÉE")