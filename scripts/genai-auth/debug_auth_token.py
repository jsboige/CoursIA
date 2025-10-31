#!/usr/bin/env python3
"""
Script de diagnostic pour comprendre le problème d'authentification ComfyUI
Hypothèse : Le token dans PASSWORD est hashé (bcrypt) mais le code attend un token brut
"""

import sys
import os
import requests
import json

# Ajouter le chemin du plugin ComfyUI-Login
sys.path.append('/workspace/ComfyUI/custom_nodes/ComfyUI-Login')

def test_token_loading():
    """Test comment le token est chargé par le plugin"""
    try:
        from password import load_token, TOKEN
        
        print("=== DIAGNOSTIC TOKEN LOADING ===")
        print(f"Token brut chargé: {repr(TOKEN)}")
        print(f"Type du token: {type(TOKEN)}")
        print(f"Longueur du token: {len(TOKEN) if TOKEN else 'None'}")
        
        # Vérifier si le token ressemble à un hash bcrypt
        if TOKEN and TOKEN.startswith('$2'):
            print("⚠️  Le token chargé ressemble à un hash bcrypt!")
            print("   Cela explique pourquoi l'authentification échoue")
            print("   Le code attend un token brut, pas un hash")
            return False
        elif TOKEN:
            print("✅ Token brut détecté")
            return True
        else:
            print("❌ Aucun token chargé")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors du test: {e}")
        return False

def test_password_file_content():
    """Vérifier le contenu du fichier PASSWORD"""
    try:
        password_path = "/workspace/ComfyUI/login/PASSWORD"
        with open(password_path, 'r', encoding='utf-8') as f:
            content = f.read().strip()
            
        print("=== CONTENU FICHIER PASSWORD ===")
        print(f"Contenu: {repr(content)}")
        print(f"Longueur: {len(content)}")
        
        # Vérifier si c'est un hash bcrypt
        if content.startswith('$2'):
            print("⚠️  Le fichier contient un hash bcrypt!")
            return "hashed"
        else:
            print("✅ Le fichier contient un token brut")
            return "plain"
            
    except Exception as e:
        print(f"❌ Erreur lecture PASSWORD: {e}")
        return None

def test_api_with_different_tokens():
    """Tester l'API avec différents formats de token"""
    base_url = "http://localhost:8188"
    
    # Lire le contenu du fichier PASSWORD
    password_path = "/workspace/ComfyUI/login/PASSWORD"
    try:
        with open(password_path, 'r', encoding='utf-8') as f:
            password_content = f.read().strip()
    except:
        password_content = None
    
    print("\n=== TESTS API ===")
    
    # Test 1: Token tel quel (probablement hashé)
    if password_content:
        print(f"\n1. Test avec token du fichier PASSWORD: {password_content[:20]}...")
        headers = {'Authorization': f'Bearer {password_content}'}
        try:
            response = requests.get(f"{base_url}/system_stats", headers=headers, timeout=5)
            print(f"   Status: {response.status_code}")
            if response.status_code == 200:
                print("   ✅ SUCCÈS ! Le token du fichier fonctionne")
                return password_content
            else:
                print(f"   ❌ Échec: {response.text}")
        except Exception as e:
            print(f"   ❌ Erreur: {e}")
    
    # Test 2: Générer un token simple et le tester
    import secrets
    simple_token = secrets.token_urlsafe(32)
    print(f"\n2. Test avec token simple généré: {simple_token}")
    headers = {'Authorization': f'Bearer {simple_token}'}
    try:
        response = requests.get(f"{base_url}/system_stats", headers=headers, timeout=5)
        print(f"   Status: {response.status_code}")
        if response.status_code == 200:
            print("   ✅ SUCCÈS ! Un token simple fonctionne")
            return simple_token
        else:
            print(f"   ❌ Échec: {response.text}")
    except Exception as e:
        print(f"   ❌ Erreur: {e}")
    
    # Test 3: Essayer sans token (vérifier l'erreur)
    print(f"\n3. Test sans token (vérification erreur)")
    try:
        response = requests.get(f"{base_url}/system_stats", timeout=5)
        print(f"   Status: {response.status_code}")
        print(f"   Réponse: {response.text}")
    except Exception as e:
        print(f"   ❌ Erreur: {e}")
    
    return None

def main():
    print("🔍 DIAGNOSTIC AUTHENTIFICATION COMFYUI")
    print("=" * 50)
    
    # Test 1: Comment le token est chargé
    token_ok = test_token_loading()
    
    # Test 2: Contenu du fichier PASSWORD
    password_type = test_password_file_content()
    
    # Test 3: Tests API
    working_token = test_api_with_different_tokens()
    
    print("\n" + "=" * 50)
    print("📊 RÉSULTATS DU DIAGNOSTIC:")
    print(f"   Token loading: {'✅' if token_ok else '❌'}")
    print(f"   Type PASSWORD: {password_type}")
    
    if working_token:
        print(f"   ✅ TOKEN FONCTIONNEL TROUVÉ: {working_token[:20]}...")
        print("\n🔧 SOLUTION:")
        print("   Le problème est que le fichier PASSWORD contient un hash bcrypt")
        print("   mais le code s'attend à un token brut pour l'API Bearer")
        print("   Solution: remplacer le contenu par un token brut fonctionnel")
        
        # Sauvegarder la solution
        solution_file = "/tmp/solution_token.txt"
        with open(solution_file, 'w') as f:
            f.write(working_token)
        print(f"\n💾 Token solution sauvegardé dans: {solution_file}")
        
        return working_token
    else:
        print("   ❌ Aucun token fonctionnel trouvé")
        print("   Le problème peut être ailleurs dans la configuration")
        
        return None

if __name__ == "__main__":
    main()