# ÉTAPE 1 : Installation Custom Node
Write-Host "Étape 1: Clonage de ComfyUI-Login..."
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes && git clone https://github.com/11cafe/ComfyUI-Login.git"

# ÉTAPE 2 : Installation Dépendances
Write-Host "Étape 2: Installation des dépendances..."
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ComfyUI-Login && source ../../venv/bin/activate && pip install -r requirements.txt"

Write-Host "Configuration manuelle requise pour config.yaml."
Write-Host "Veuillez créer le fichier config.yaml dans /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ComfyUI-Login/ avec le contenu approprié."
