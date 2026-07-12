#!/usr/bin/env python3
"""
Script de synchronisation des tokens ComfyUI-Login
Génère un hash bcrypt valide pour le token existant et synchronise tous les emplacements
"""

import bcrypt
import os
import sys
from pathlib import Path

def main():
    """Point d'entrée principal"""
    print("🔐 SYNCHRONISATION DES TOKENS COMFYUI-LOGIN")
    print("=" * 60)
    
    # Configuration des chemins
    project_root = Path(__file__).parent.parent.parent.parent
    secrets_dir = project_root / ".secrets"
    docker_config_dir = project_root / "docker-configurations" / "comfyui-qwen"
    
    # Fichiers à gérer
    env_generated_file = secrets_dir / ".env.generated"
    token_file = secrets_dir / "qwen-api-user.token"
    docker_env_file = docker_config_dir / ".env"
    
    print(f"📁 Racine du projet : {project_root}")
    print(f"📂 Répertoire .secrets : {secrets_dir}")
    print(f"📂 Configuration Docker : {docker_config_dir}")
    print()
    
    # 1. Lire le token brut existant
    try:
        with open(env_generated_file, 'r') as f:
            content = f.read().strip()
            token_brut = content.split('=')[1] if '=' in content else content
        print(f"🔑 Token brut lu : {token_brut}")
    except Exception as e:
        print(f"❌ Erreur lecture token brut : {e}")
        return False
    
    # 2. Générer le hash bcrypt
    print("🔧 Génération du hash bcrypt...")
    try:
        # Générer un sel et hasher le token
        salt = bcrypt.gensalt()
        hash_bcrypt = bcrypt.hashpw(token_brut.encode('utf-8'), salt)
        hash_str = hash_bcrypt.decode('utf-8')
        print(f"✅ Hash généré : {hash_str}")
    except Exception as e:
        print(f"❌ Erreur génération hash : {e}")
        return False
    
    # 3. Valider la correspondance
    print("🔍 Validation de la correspondance...")
    try:
        validation = bcrypt.checkpw(token_brut.encode('utf-8'), hash_bcrypt)
        print(f"✅ Validation bcrypt.checkpw() : {validation}")
        if not validation:
            print("❌ ERREUR CRITIQUE : Le hash ne correspond pas au token !")
            return False
    except Exception as e:
        print(f"❌ Erreur validation : {e}")
        return False
    
    # 4. Sauvegarder les fichiers existants
    print("💾 Sauvegarde des fichiers existants...")
    backup_suffix = ".backup"
    
    for file_path, description in [
        (token_file, "hash serveur"),
        (docker_env_file, "configuration Docker")
    ]:
        if file_path.exists():
            backup_path = file_path.with_suffix(file_path.suffix + backup_suffix)
            try:
                with open(file_path, 'r') as src, open(backup_path, 'w') as dst:
                    dst.write(src.read())
                print(f"✅ Sauvegardé {description} : {backup_path}")
            except Exception as e:
                print(f"⚠️ Erreur sauvegarde {description} : {e}")
    
    # 5. Mettre à jour le fichier de hash serveur
    print("📝 Mise à jour du hash serveur...")
    try:
        with open(token_file, 'w') as f:
            f.write(hash_str)
        print(f"✅ Fichier serveur mis à jour : {token_file}")
    except Exception as e:
        print(f"❌ Erreur mise à jour serveur : {e}")
        return False
    
    # 6. Mettre à jour la configuration Docker
    print("📝 Mise à jour de la configuration Docker...")
    try:
        with open(docker_env_file, 'r') as f:
            docker_content = f.read()
        
        # Remplacer la ligne COMFYUI_BEARER_TOKEN
        lines = docker_content.split('\n')
        updated_lines = []
        for line in lines:
            if line.startswith('COMFYUI_BEARER_TOKEN='):
                updated_lines.append(f'COMFYUI_BEARER_TOKEN={hash_str}')
            else:
                updated_lines.append(line)
        
        with open(docker_env_file, 'w') as f:
            f.write('\n'.join(updated_lines))
        print(f"✅ Configuration Docker mise à jour : {docker_env_file}")
    except Exception as e:
        print(f"❌ Erreur mise à jour Docker : {e}")
        return False
    
    # 7. Résumé des modifications
    print()
    print("📋 RÉSUMÉ DES MODIFICATIONS")
    print("=" * 40)
    print(f"🔑 Token brut (inchangé) : {token_brut}")
    print(f"🔐 Nouveau hash bcrypt : {hash_str}")
    print(f"📄 Fichier serveur : {token_file}")
    print(f"🐳 Configuration Docker : {docker_env_file}")
    print(f"📄 Fichier token brut : {env_generated_file} (inchangé)")
    print()
    
    # 8. Validation finale
    print("🔍 Validation finale de tous les emplacements...")
    try:
        # Vérifier le hash serveur
        with open(token_file, 'r') as f:
            serveur_hash = f.read().strip()
        serveur_ok = bcrypt.checkpw(token_brut.encode('utf-8'), serveur_hash.encode('utf-8'))
        print(f"✅ Hash serveur valide : {serveur_ok}")
        
        # Vérifier le hash Docker
        with open(docker_env_file, 'r') as f:
            docker_content = f.read()
        for line in docker_content.split('\n'):
            if line.startswith('COMFYUI_BEARER_TOKEN='):
                docker_hash = line.split('=')[1]
                docker_ok = bcrypt.checkpw(token_brut.encode('utf-8'), docker_hash.encode('utf-8'))
                print(f"✅ Hash Docker valide : {docker_ok}")
                break
        
        if serveur_ok and docker_ok:
            print("🎉 SYNCHRONISATION RÉUSSIE ! Tous les tokens sont cohérents")
            return True
        else:
            print("❌ ERREUR : La validation finale a échoué")
            return False
            
    except Exception as e:
        print(f"❌ Erreur validation finale : {e}")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)