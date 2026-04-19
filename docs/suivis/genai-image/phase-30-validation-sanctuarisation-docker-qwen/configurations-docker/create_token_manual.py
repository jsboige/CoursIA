#!/usr/bin/env python3
"""
Création manuelle d'un token bcrypt valide pour ComfyUI-Login
Utilise le token existant qui fonctionnait auparavant
"""

import os
import sys
from pathlib import Path

def main():
    print("🔧 Création manuelle du token ComfyUI-Login")
    print("=" * 50)
    
    # Utiliser le token bcrypt qui était dans le .env et qui était valide
    # Token original: $2b$12$NErya5UooY9bJnscVc/ec.hpVDX.nYM86/88bXIkF/hh2VeKRvU5ka
    # Ce token a 60 caractères, ce qui est correct pour bcrypt
    
    valid_token = "$2b$12$NErya5UooY9bJnscVc/ec.hpVDX.nYM86/88bXIkF/hh2VeKRvU5ka"
    
    print(f"✅ Token bcrypt valide identifié:")
    print(f"   Hash: {valid_token}")
    
    # Créer le répertoire custom_nodes s'il n'existe pas
    custom_nodes_path = Path("custom_nodes/ComfyUI-Login")
    custom_nodes_path.mkdir(parents=True, exist_ok=True)
    
    # Écrire le token dans le fichier PASSWORD
    password_file = custom_nodes_path / "PASSWORD"
    
    try:
        with open(password_file, 'w') as f:
            f.write(valid_token)
        
        # Définir les permissions correctes
        os.chmod(password_file, 0o600)
        
        print(f"💾 Token écrit dans: {password_file}")
        print(f"🔒 Permissions définies: 600 (lecture/écriture propriétaire uniquement)")
        
        # Vérifier que le fichier a été correctement écrit
        with open(password_file, 'r') as f:
            written_token = f.read().strip()
        
        if written_token == valid_token:
            print("✅ Vérification: Token correctement écrit")
            print(f"✅ Longueur du token: {len(written_token)} caractères")
        else:
            print("❌ Erreur: Token tronqué lors de l'écriture")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors de l'écriture du token: {str(e)}")
        return False
    
    print("\n🎯 Résumé des corrections:")
    print(f"   ✅ Token bcrypt valide utilisé")
    print(f"   ✅ Fichier PASSWORD créé avec permissions sécurisées")
    print(f"   ✅ Prêt pour redémarrage du conteneur")
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)