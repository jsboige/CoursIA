# Configuration Dual Auth : ComfyUI & Forge

## Contexte
Ce document décrit la coexistence des deux systèmes d'authentification pour les services GenAI :
- **ComfyUI (Qwen)** : Authentification Bearer Token (Standardisé)
- **Forge (SD XL Turbo)** : Authentification Gradio Basic Auth (Legacy/Natif)

## 1. ComfyUI (Qwen)
- **Méthode** : Bearer Token (Header `Authorization: Bearer <token>`)
- **Configuration** : Gérée par `scripts/genai-auth/utils/token_synchronizer.py`
- **Fichier** : `docker-configurations/services/comfyui-qwen/.env`
- **Variable** : `COMFYUI_API_TOKEN` (Hash bcrypt)

## 2. Forge (SD XL Turbo)
- **Méthode** : Basic Auth (User/Password)
- **Configuration** : Native Gradio via arguments CLI
- **Fichier** : `docker-configurations/services/forge-turbo/.env`
- **Variables** : 
  - `FORGE_USER`
  - `FORGE_PASSWORD`
- **Injection** : Via `docker-compose.yml` dans `CLI_ARGS` : `--gradio-auth ${FORGE_USER}:${FORGE_PASSWORD}`

## 3. Maintenance
Pour modifier les identifiants Forge :
1. Éditer `docker-configurations/services/forge-turbo/.env`
2. Redémarrer le service : `docker-compose -f docker-configurations/services/forge-turbo/docker-compose.yml up -d`

Pour modifier les tokens ComfyUI :
1. Utiliser le script de synchronisation : `python scripts/genai-auth/utils/token_synchronizer.py --unify`