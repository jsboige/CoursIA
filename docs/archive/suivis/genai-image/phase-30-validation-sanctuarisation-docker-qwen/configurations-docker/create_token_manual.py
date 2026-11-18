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
    
    # Le hash bcrypt vient de l'environnement : aucun token n'est ecrit en clair
    # dans un fichier suivi (regle 2 de secrets-hygiene.md, cf. #21839). Le litteral
    # qui vivait ici etait mort : remplace par l'unification des tokens de phase-31,
    # et #21098 a mesure que le mot de passe ne correspondait plus au service.
    valid_token = os.getenv("COMFYUI_LOGIN_TOKEN_HASH")
    if not valid_token:
        raise RuntimeError(
            "COMFYUI_LOGIN_TOKEN_HASH absent : ce script n'ecrit plus de token par "
            "defaut (cf. #21839). Renseigner le hash bcrypt courant du service."
        )

    print("Token bcrypt lu depuis l'environnement :")
    print(f"   Hash de {len(valid_token)} caracteres (60 attendus pour bcrypt)")
    
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