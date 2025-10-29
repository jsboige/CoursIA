# Package helpers pour les utilitaires GenAI
# Ce fichier permet d'importer helpers comme un package Python

# __init__.py minimal - pas d'imports automatiques pour éviter les dépendances circulaires
# Les imports doivent être faits explicitement:
#   from helpers.comfyui_client import create_client, ComfyUIConfig
#   from helpers.genai_helpers import ...