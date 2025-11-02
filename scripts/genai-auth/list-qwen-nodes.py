#!/usr/bin/env python3
"""
Liste les nodes Qwen disponibles dans ComfyUI
"""

import requests
import json
from pathlib import Path

TOKEN_FILE = Path(".secrets/qwen-api-user.token")
COMFYUI_URL = "http://localhost:8188"

def load_token():
    with open(TOKEN_FILE, 'r') as f:
        return f.read().strip()

def list_qwen_nodes():
    token = load_token()
    headers = {"Authorization": f"Bearer {token}"}
    
    response = requests.get(f"{COMFYUI_URL}/object_info", headers=headers)
    
    if response.status_code == 200:
        all_nodes = response.json()
        qwen_nodes = {k: v for k, v in all_nodes.items() if 'qwen' in k.lower()}
        
        print(f"Nodes Qwen disponibles: {len(qwen_nodes)}")
        print("\n" + "=" * 80)
        
        for node_name in sorted(qwen_nodes.keys()):
            print(f"- {node_name}")
        
        print("=" * 80)
        
        # Sauvegarder dans un fichier pour analyse
        with open("qwen_nodes_available.json", 'w') as f:
            json.dump(qwen_nodes, f, indent=2)
        
        print(f"\nDétails sauvegardés dans: qwen_nodes_available.json")
        
    else:
        print(f"Erreur HTTP {response.status_code}")

if __name__ == "__main__":
    list_qwen_nodes()