#!/usr/bin/env python3
"""
validate_tokens_simple.py - Validation simple des tokens ComfyUI-Login
"""

import os
from pathlib import Path

def main():
    print("🔍 VALIDATION SIMPLE DES TOKENS COMFYUI-LOGIN")
    print("=" * 60)
    
    # Lire les tokens depuis les emplacements
    root_dir = Path(__file__).parent.parent.parent.parent
    
    # Token depuis .secrets/qwen-api-user.token
    secrets_token_path = root_dir / ".secrets" / "qwen-api-user.token"
    secrets_token = None
    if secrets_token_path.exists():
        with open(secrets_token_path, 'r') as f:
            secrets_token = f.read().strip()
    
    # Token depuis .env
    env_path = root_dir / ".env"
    env_token = None
    if env_path.exists():
        with open(env_path, 'r') as f:
            content = f.read()
            for line in content.split('\n'):
                if line.startswith('COMFYUI_API_TOKEN='):
                    env_token = line.split('=')[1].strip()
                    break
    
    # Token depuis docker .env
    docker_env_path = root_dir / "docker-configurations" / "comfyui-qwen" / ".env"
    docker_token = None
    if docker_env_path.exists():
        with open(docker_env_path, 'r') as f:
            content = f.read()
            for line in content.split('\n'):
                if line.startswith('COMFYUI_BEARER_TOKEN='):
                    docker_token = line.split('=')[1].strip()
                    break
    
    # Afficher les résultats
    print(f"\n📍 Token depuis .secrets/qwen-api-user.token:")
    print(f"   {secrets_token[:30] if secrets_token else 'MANQUANT'}...")
    
    print(f"\n📍 Token depuis .env (COMFYUI_API_TOKEN):")
    print(f"   {env_token[:30] if env_token else 'MANQUANT'}...")
    
    print(f"\n📍 Token depuis docker/.env (COMFYUI_BEARER_TOKEN):")
    print(f"   {docker_token[:30] if docker_token else 'MANQUANT'}...")
    
    # Vérifier la cohérence
    tokens = [secrets_token, env_token, docker_token]
    tokens = [t for t in tokens if t]  # Filtrer les None
    
    print(f"\n🔍 ANALYSE DE COHÉRENCE:")
    if len(tokens) == 0:
        print("   ❌ Aucun token trouvé")
        return False
    elif len(set(tokens)) == 1:
        print("   ✅ TOUS LES TOKENS SONT IDENTIQUES")
        print(f"   🎯 Token unique: {tokens[0][:30]}...")
        return True
    else:
        print(f"   ❌ {len(set(tokens))} TOKENS DIFFÉRENTS TROUVÉS")
        for i, token in enumerate(set(tokens), 1):
            source = ""
            if token == secrets_token:
                source += ".secrets "
            if token == env_token:
                source += ".env "
            if token == docker_token:
                source += "docker "
            print(f"   {i}. {source}: {token[:30]}...")
        return False

if __name__ == "__main__":
    main()