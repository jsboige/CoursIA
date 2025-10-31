#!/usr/bin/env python3
"""
Script simple pour tester la soumission du workflow Qwen
"""

import json
import requests
import sys

def main():
    # Charger le workflow
    workflow_file = "temp_official_workflow_qwen_t2i_fixed.json"
    
    try:
        with open(workflow_file, 'r', encoding='utf-8') as f:
            workflow = json.load(f)
        
        # Préparer le payload
        payload = {
            'prompt': workflow
        }
        
        # Soumettre à ComfyUI
        response = requests.post(
            'http://localhost:8188/prompt',
            json=payload,
            headers={'Content-Type': 'application/json'}
        )
        
        print(f"Status code: {response.status_code}")
        print(f"Response: {response.text}")
        
        if response.status_code == 200:
            result = response.json()
            if 'prompt_id' in result:
                print(f"✅ Workflow soumis avec ID: {result['prompt_id']}")
                return True
            else:
                print("❌ Réponse inattendue")
                return False
        else:
            print(f"❌ Erreur HTTP {response.status_code}: {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur: {e}")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)