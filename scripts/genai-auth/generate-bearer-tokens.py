#!/usr/bin/env python3
"""
Script Python alternatif pour générer des tokens Bearer pour ComfyUI-Login.
Utilise bcrypt pour hasher les mots de passe.
"""

import bcrypt
import secrets
import string
import sys
import os
from pathlib import Path
from datetime import datetime

def generate_secure_password(length=32):
    """Génère un mot de passe sécurisé aléatoire."""
    charset = string.ascii_letters + string.digits + "!@#$%^&*()_+"
    return ''.join(secrets.choice(charset) for _ in range(length))

def generate_bcrypt_hash(password, work_factor=12):
    """Génère un hash bcrypt du mot de passe."""
    salt = bcrypt.gensalt(rounds=work_factor)
    hashed = bcrypt.hashpw(password.encode('utf-8'), salt)
    return hashed.decode('utf-8')

def main():
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - [GENERATE-TOKENS] Démarrage de la génération de tokens Bearer...")
    
    # Configuration
    username = "qwen-api-user"
    output_dir = Path(".secrets")
    work_factor = 12
    password_length = 32
    
    # Créer le répertoire de sortie
    output_dir.mkdir(exist_ok=True)
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - [GENERATE-TOKENS] Répertoire de sortie: {output_dir.absolute()}")
    
    # Générer le mot de passe
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - [GENERATE-TOKENS] Génération du mot de passe pour '{username}'...")
    password = generate_secure_password(password_length)
    
    # Hasher le mot de passe
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - [GENERATE-TOKENS] Hachage avec bcrypt (work factor: {work_factor})...")
    hashed_password = generate_bcrypt_hash(password, work_factor)
    
    # Créer le fichier .token
    token_file = output_dir / f"{username}.token"
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - [GENERATE-TOKENS] Création du fichier token: {token_file}")
    token_file.write_text(hashed_password, encoding='utf-8')
    
    # Créer le fichier .env.generated
    env_file = output_dir / ".env.generated"
    env_var_name = username.replace('-', '_').upper() + "_TOKEN"
    env_content = f"{env_var_name}={password}\n"
    env_file.write_text(env_content, encoding='utf-8')
    
    # Afficher les résultats
    print("\n" + "="*60)
    print("🎉 GÉNÉRATION TERMINÉE AVEC SUCCÈS 🎉")
    print("="*60)
    print(f"Utilisateur : {username}")
    print(f"Mot de passe: {password}")
    print(f"Hash bcrypt : {hashed_password[:20]}...{hashed_password[-10:]}")
    print("-"*60)
    print(f"✅ Fichier token créé : {token_file}")
    print(f"✅ Fichier .env créé  : {env_file}")
    print("-"*60)
    print("\n⚠️  IMPORTANT: Stockez ce mot de passe en lieu sûr!")
    print(f"⚠️  Le fichier {env_file} contient le token.")
    print("\n")
    
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:
        print(f"\n❌ ERREUR: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)