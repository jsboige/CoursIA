#!/usr/bin/env python3
import bcrypt
import sys

# Utiliser le mot de passe du fichier .env
password = "rZDS3XQa/8!v9L"

# Générer le token bcrypt
token = bcrypt.hashpw(password.encode(), bcrypt.gensalt())

# Afficher le token au format Bearer
print(f"Bearer {token.decode()}")