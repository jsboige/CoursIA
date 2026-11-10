#!/usr/bin/env python3
import bcrypt
import os
import sys

# Utiliser le mot de passe du fichier .env
password = os.getenv("COMFYUI_PASSWORD")

# Générer le token bcrypt
token = bcrypt.hashpw(password.encode(), bcrypt.gensalt())

# Afficher le token au format Bearer
print(f"Bearer {token.decode()}")