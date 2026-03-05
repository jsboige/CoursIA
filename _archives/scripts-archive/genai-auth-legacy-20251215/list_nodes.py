import sys
from pathlib import Path
sys.path.append("scripts/genai-auth")
from core.auth_manager import GenAIAuthManager
from core.comfyui_client import ComfyUIClient, ComfyUIConfig

def list_nodes():
    auth_manager = GenAIAuthManager()
    config = auth_manager.load_config()
    token = config.get('bcrypt_hash')
    
    client = ComfyUIClient(ComfyUIConfig(api_key=token))
    
    print("Récupération des infos des nœuds...")
    info = client.get_object_info()
    
    qwen_nodes = [k for k in info.keys() if "Qwen" in k]
    print(f"Nœuds Qwen trouvés ({len(qwen_nodes)}) :")
    for node in qwen_nodes:
        print(f" - {node}")
        
    wrapper_nodes = [k for k in info.keys() if "Wrapper" in k]
    print(f"\nNœuds Wrapper trouvés ({len(wrapper_nodes)}) :")
    for node in wrapper_nodes:
        print(f" - {node}")

if __name__ == "__main__":
    list_nodes()