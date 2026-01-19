import sys
from pathlib import Path

# Ajout du dossier courant au path pour trouver le module core local
current_dir = Path(__file__).resolve().parent
sys.path.append(str(current_dir))

from core.auth_manager import GenAIAuthManager
from core.comfyui_client import ComfyUIClient, ComfyUIConfig

def list_models():
    auth_manager = GenAIAuthManager()
    config = auth_manager.load_config()
    token = config.get('bcrypt_hash')
    
    client = ComfyUIClient(ComfyUIConfig(api_key=token))
    
    print("Récupération des Checkpoints...")
    info = client.get_object_info("CheckpointLoaderSimple")
    # L'info ne donne pas la liste des fichiers, mais les types d'inputs.
    # Pour avoir la liste des fichiers, il faut appeler /object_info/CheckpointLoaderSimple 
    # et regarder inputs -> ckpt_name -> 0 (la liste des choix)
    
    try:
        input_info = info['CheckpointLoaderSimple']['input']['required']['ckpt_name']
        models = input_info[0]
        print(f"Modèles trouvés ({len(models)}) :")
        for m in models:
            print(f" - {m}")
    except Exception as e:
        print(f"Erreur parsing: {e}")
        print(info)

if __name__ == "__main__":
    list_models()