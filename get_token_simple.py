#!/usr/bin/env python3
"""Script simple pour récupérer le token ComfyUI depuis l'environnement."""

import os
import sys

def main():
    """Essayer plusieurs méthodes pour obtenir le token ComfyUI."""
    
    # Méthode 1: Variable d'environnement directe
    token = os.environ.get('COMFYUI_API_TOKEN')
    if token:
        print(f"TOKEN_FOUND:{token}")
        return
    
    # Méthode 2: Lire depuis .env dans /workspace/ComfyUI
    try:
        env_file = '/workspace/ComfyUI/.env'
        if os.path.exists(env_file):
            with open(env_file, 'r') as f:
                for line in f:
                    if line.strip().startswith('COMFYUI_API_TOKEN='):
                        token = line.strip().split('=', 1)[1]
                        print(f"TOKEN_FOUND:{token}")
                        return
    except Exception as e:
        print(f"ERROR_READING_ENV:{e}")
    
    # Méthode 3: Chercher dans les variables d'environnement ComfyUI
    comfy_env_vars = [k for k in os.environ.keys() if 'COMFY' in k.upper() or 'API' in k.upper()]
    print(f"AVAILABLE_ENV_VARS:{comfy_env_vars}")
    
    # Méthode 4: Vérifier configuration auth
    auth_file = '/workspace/ComfyUI/web/auth.py'
    if os.path.exists(auth_file):
        print(f"AUTH_FILE_EXISTS:{auth_file}")
        try:
            # Lire le fichier pour comprendre la structure
            with open(auth_file, 'r') as f:
                content = f.read()
                print(f"AUTH_FILE_SIZE:{len(content)}")
                print(f"AUTH_FILE_PREVIEW:{content[:200]}...")
        except Exception as e:
            print(f"ERROR_READING_AUTH:{e}")
    
    print("NO_TOKEN_FOUND")
    sys.exit(1)

if __name__ == "__main__":
    main()