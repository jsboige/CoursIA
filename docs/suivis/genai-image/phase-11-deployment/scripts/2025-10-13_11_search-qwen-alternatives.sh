#!/bin/bash
# Phase 11: Recherche alternatives custom nodes Qwen pour ComfyUI
# Date: 2025-10-13

echo "=== Recherche alternatives Qwen pour ComfyUI ==="
echo ""

# Recherche 1: Custom nodes Qwen
echo "▶ Recherche repositories ComfyUI + Qwen sur GitHub..."
curl -s 'https://api.github.com/search/repositories?q=comfyui+qwen&sort=stars&order=desc&per_page=10' | \
  grep -E '"full_name"|"description"|"html_url"' | \
  sed 's/^[ \t]*//' | \
  paste - - - | \
  head -10

echo ""
echo ""

# Recherche 2: Custom nodes diffusers
echo "▶ Recherche custom nodes diffusers pour ComfyUI..."
curl -s 'https://api.github.com/search/repositories?q=comfyui+diffusers&sort=stars&order=desc&per_page=5' | \
  grep -E '"full_name"|"html_url"' | \
  sed 's/^[ \t]*//' | \
  paste - - | \
  head -5

echo ""
echo ""

# Recherche 3: Vérifier si ComfyUI supporte nativement les modèles diffusers
echo "▶ Vérification support natif diffusers dans ComfyUI..."
COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
if [ -d "$COMFYUI_DIR" ]; then
    cd "$COMFYUI_DIR"
    echo "Recherche de 'diffusers' dans le code ComfyUI:"
    grep -r "diffusers" --include="*.py" . | head -5 || echo "Aucune référence trouvée"
fi

echo ""
echo "=== Fin de la recherche ==="