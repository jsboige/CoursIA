#!/usr/bin/env python3
"""
Script pour corriger le token ComfyUI-Login tronqué
Génère un nouveau token bcrypt valide et s'assure qu'il est correctement formaté
"""

import bcrypt
import os
import sys
from pathlib import Path

def generate_bcrypt_token():
    """Génère un token bcrypt valide pour ComfyUI-Login"""
    # Utiliser un token très court pour garantir un hash bcrypt de 22 caractères
    token = "comfyui2025"  # 12 caractères seulement
    
    # Hash avec bcrypt (cost factor 12 recommandé)
    salt = bcrypt.gensalt(rounds=12)
    hashed_token = bcrypt.hashpw(token.encode('utf-8'), salt)
    
    return hashed_token.decode('utf-8'), token

def validate_bcrypt_format(token):
    """Valide que le token bcrypt est correctement formaté"""
    try:
        # Vérifier que le token commence par $2b$
        if not token.startswith('$2b$'):
            return False, "Le token doit commencer par $2b$"
        
        # Vérifier la structure complète
        parts = token.split('$')
        if len(parts) != 4:
            return False, f"Structure invalide: {len(parts)} parties au lieu de 4"
        
        # Vérifier le cost factor
        try:
            cost = int(parts[2])
            if cost < 10 or cost > 14:
                return False, f"Cost factor invalide: {cost}"
        except ValueError:
            return False, f"Cost factor non numérique: {parts[2]}"
        
        # Vérifier le hash (22 caractères base64)
        hash_part = parts[3]
        if len(hash_part) != 22:
            return False, f"Hash invalide: {len(hash_part)} caractères au lieu de 22"
        
        return True, "Token bcrypt valide"
    
    except Exception as e:
        return False, f"Erreur de validation: {str(e)}"

def main():
    print("🔧 Correction du token ComfyUI-Login")
    print("=" * 50)
    
    # Générer un nouveau token
    print("📝 Génération d'un nouveau token bcrypt...")
    hashed_token, original_token = generate_bcrypt_token()
    
    print(f"✅ Token généré avec succès:")
    print(f"   Hash: {hashed_token}")
    print(f"   Original: {original_token}")
    
    # Valider le format
    print("\n🔍 Validation du format bcrypt...")
    is_valid, message = validate_bcrypt_format(hashed_token)
    
    if is_valid:
        print(f"✅ {message}")
    else:
        print(f"❌ {message}")
        return False
    
    # Créer le répertoire custom_nodes s'il n'existe pas
    custom_nodes_path = Path("custom_nodes/ComfyUI-Login")
    custom_nodes_path.mkdir(parents=True, exist_ok=True)
    
    # Écrire le token dans le fichier PASSWORD
    password_file = custom_nodes_path / "PASSWORD"
    
    try:
        with open(password_file, 'w') as f:
            f.write(hashed_token)
        
        # Définir les permissions correctes
        os.chmod(password_file, 0o600)
        
        print(f"\n💾 Token écrit dans: {password_file}")
        print(f"🔒 Permissions définies: 600 (lecture/écriture propriétaire uniquement)")
        
        # Vérifier que le fichier a été correctement écrit
        with open(password_file, 'r') as f:
            written_token = f.read().strip()
        
        if written_token == hashed_token:
            print("✅ Vérification: Token correctement écrit")
        else:
            print("❌ Erreur: Token tronqué lors de l'écriture")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors de l'écriture du token: {str(e)}")
        return False
    
    # Mettre à jour le fichier .env avec le nouveau token
    env_file = Path(".env")
    
    if env_file.exists():
        print(f"\n📝 Mise à jour du fichier .env...")
        
        try:
            with open(env_file, 'r') as f:
                env_content = f.read()
            
            # Remplacer la ligne COMFYUI_BEARER_TOKEN
            lines = env_content.split('\n')
            updated_lines = []
            
            for line in lines:
                if line.startswith('COMFYUI_BEARER_TOKEN='):
                    updated_lines.append(f'COMFYUI_BEARER_TOKEN={hashed_token}')
                else:
                    updated_lines.append(line)
            
            with open(env_file, 'w') as f:
                f.write('\n'.join(updated_lines))
            
            print("✅ Fichier .env mis à jour avec le nouveau token")
            
        except Exception as e:
            print(f"❌ Erreur lors de la mise à jour du .env: {str(e)}")
            return False
    
    print("\n🎯 Résumé des corrections:")
    print(f"   ✅ Token bcrypt généré et validé")
    print(f"   ✅ Fichier PASSWORD créé avec permissions sécurisées")
    print(f"   ✅ Fichier .env mis à jour")
    print(f"   ✅ Prêt pour redémarrage du conteneur")
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)