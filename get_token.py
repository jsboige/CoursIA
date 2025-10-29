#!/usr/bin/env python3
"""Script pour récupérer le token d'authentification ComfyUI"""
import sys
import os

# Ajouter le chemin ComfyUI au Python path
sys.path.append('/workspace/ComfyUI')

try:
    from web import auth
    token = auth.get_token()
    if token:
        print(f"TOKEN_FOUND:{token}")
    else:
        print("TOKEN_NOT_FOUND")
except Exception as e:
    print(f"ERROR:{e}")