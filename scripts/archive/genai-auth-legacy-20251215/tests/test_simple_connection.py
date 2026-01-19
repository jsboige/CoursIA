#!/usr/bin/env python3
"""
Script de test simple pour vérifier la connexion à l'API ComfyUI
"""

import sys
from pathlib import Path

# Ajouter le répertoire utils au path
# Ajouter le répertoire parent au path Python
sys.path.append(str(Path(__file__).parent.parent))
sys.path.append(str(Path(__file__).parent.parent / "utils"))

from utils.comfyui_client_helper import ComfyUIClient

def test_connection():
    """Test simple de connexion à l'API ComfyUI"""
    
    print("🔧 TEST DE CONNEXION COMFYUI")
    print("=" * 50)
    
    try:
        # Initialiser le client avec la nouvelle configuration
        from utils.comfyui_client_helper import ComfyUIConfig
        config = ComfyUIConfig(host="localhost", port=8188)
        client = ComfyUIClient(config=config)
        
        print("✅ Client initialisé")
        
        # Test 1: Appeler /object_info (endpoint correct pour lister les nœuds)
        print("\n📋 Test 1: Appel /object_info")
        response = client._make_request("GET", "/object_info")
        print(f"   Status: {response}")
        
        # Test 2: Appeler /system_stats
        print("\n📋 Test 2: Appel /system_stats")
        response = client._make_request("GET", "/system_stats")
        print(f"   Status: {response}")
        
        print("\n✅ Tests de connexion réussis")
        
    except Exception as e:
        print(f"\n❌ Erreur: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_connection()