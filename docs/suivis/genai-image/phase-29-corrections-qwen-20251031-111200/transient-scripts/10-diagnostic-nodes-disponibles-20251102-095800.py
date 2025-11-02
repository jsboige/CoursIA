#!/usr/bin/env python3
"""
Diagnostic Nodes Qwen Disponibles - Phase 29
==============================================
Date: 2025-11-02 09:58:00 UTC+1
Objectif: Lister les custom nodes Qwen réellement disponibles dans ComfyUI

Ce script interroge l'API ComfyUI /object_info pour obtenir la liste complète
des nodes disponibles et identifier ceux liés à Qwen.
"""

import requests
import json
from pathlib import Path

# Configuration
COMFYUI_URL = "http://localhost:8188"
HASH_FILE = Path(".secrets/qwen-api-user.token")

def load_token() -> str:
    """Charge token depuis fichier"""
    if not HASH_FILE.exists():
        raise FileNotFoundError(f"Token non trouvé: {HASH_FILE}")
    return HASH_FILE.read_text().strip()

def get_available_nodes(token: str) -> dict:
    """Récupère liste complète des nodes disponibles"""
    headers = {"Authorization": f"Bearer {token}"}
    
    response = requests.get(
        f"{COMFYUI_URL}/object_info",
        headers=headers,
        timeout=30
    )
    
    if response.status_code != 200:
        raise RuntimeError(f"Échec récupération nodes: HTTP {response.status_code}")
    
    return response.json()

def filter_qwen_nodes(all_nodes: dict) -> dict:
    """Filtre nodes Qwen"""
    qwen_nodes = {}
    
    for node_name, node_info in all_nodes.items():
        if 'qwen' in node_name.lower():
            qwen_nodes[node_name] = node_info
    
    return qwen_nodes

def analyze_node_outputs(node_name: str, node_info: dict):
    """Analyse outputs d'un node"""
    outputs = node_info.get('output', [])
    output_name = node_info.get('output_name', [])
    
    print(f"\n  Node: {node_name}")
    print(f"  Catégorie: {node_info.get('category', 'N/A')}")
    print(f"  Outputs: {len(outputs)} sortie(s)")
    
    for i, (out_type, out_name) in enumerate(zip(outputs, output_name)):
        print(f"    [{i}] {out_name}: {out_type}")

def main():
    print("=" * 70)
    print("  Diagnostic Nodes Qwen Disponibles")
    print("=" * 70)
    
    try:
        # 1. Chargement token
        print("\n1️⃣ Chargement token...")
        token = load_token()
        print(f"✅ Token chargé ({len(token)} caractères)")
        
        # 2. Récupération nodes
        print("\n2️⃣ Récupération liste nodes ComfyUI...")
        all_nodes = get_available_nodes(token)
        print(f"✅ Total nodes: {len(all_nodes)}")
        
        # 3. Filtrage Qwen
        print("\n3️⃣ Filtrage nodes Qwen...")
        qwen_nodes = filter_qwen_nodes(all_nodes)
        print(f"✅ Nodes Qwen trouvés: {len(qwen_nodes)}")
        
        # 4. Analyse détaillée
        print("\n4️⃣ Analyse détaillée des nodes Qwen:")
        print("-" * 70)
        
        for node_name in sorted(qwen_nodes.keys()):
            analyze_node_outputs(node_name, qwen_nodes[node_name])
        
        # 5. Focus QwenVLCLIPLoader
        print("\n" + "=" * 70)
        print("  FOCUS: QwenVLCLIPLoader (Node 1 du workflow)")
        print("=" * 70)
        
        if 'QwenVLCLIPLoader' in qwen_nodes:
            node_info = qwen_nodes['QwenVLCLIPLoader']
            outputs = node_info.get('output', [])
            output_names = node_info.get('output_name', [])
            
            print("\nSorties disponibles:")
            for i, (out_type, out_name) in enumerate(zip(outputs, output_names)):
                print(f"  Index {i}: {out_name} ({out_type})")
            
            print("\n⚠️ CONCLUSION:")
            print(f"   Le node QwenVLCLIPLoader a {len(outputs)} sortie(s)")
            print(f"   Workflow utilise vae:[\"1\", X] où X doit être < {len(outputs)}")
        else:
            print("\n❌ QwenVLCLIPLoader NON TROUVÉ!")
            print("   Le workflow ne peut pas fonctionner sans ce node.")
        
        # 6. Sauvegarde rapport
        print("\n5️⃣ Sauvegarde rapport JSON...")
        report_file = Path("docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports") / "diagnostic-nodes-qwen-20251102-095800.json"
        report_file.parent.mkdir(parents=True, exist_ok=True)
        
        report_file.write_text(json.dumps({
            'total_nodes': len(all_nodes),
            'qwen_nodes_count': len(qwen_nodes),
            'qwen_nodes': {
                name: {
                    'category': info.get('category'),
                    'outputs': info.get('output', []),
                    'output_names': info.get('output_name', [])
                }
                for name, info in qwen_nodes.items()
            }
        }, indent=2))
        
        print(f"✅ Rapport sauvegardé: {report_file}")
        
        print("\n" + "=" * 70)
        print("✅ DIAGNOSTIC TERMINÉ")
        print("=" * 70)
        
        return 0
        
    except Exception as e:
        print(f"\n❌ ERREUR: {type(e).__name__}: {e}")
        import traceback
        traceback.print_exc()
        return 1

if __name__ == '__main__':
    import sys
    sys.exit(main())