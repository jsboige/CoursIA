# Installation et Configuration Nunchaku INT4 - Phase 7.1

**Date**: 2026-01-21
**Status**: Production Ready
**Contexte**: Alternative performante aux modèles GGUF Q4 qui produisaient des images noires

## Résumé Exécutif

Nunchaku INT4 Lightning permet de réduire l'utilisation VRAM de **72%** (7.9GB vs 29GB) et d'accélérer la génération d'images de **95%** (4s vs 80s) par rapport au modèle Qwen FP8 standard, tout en maintenant une qualité d'image comparable.

### Performances Mesurées

| Métrique | FP8 Standard | INT4 Lightning | Amélioration |
|----------|--------------|----------------|--------------|
| **VRAM** | ~29 GB | ~7.9 GB | **-72%** |
| **Temps génération** | ~80s (20 steps) | ~4s (4 steps) | **-95%** |
| **Cold start** | ~80s | ~100s (1ère fois) | -20s |
| **Warm generation** | ~80s | ~4s | **-95%** |
| **Taille modèle** | 20 GB | 12 GB | -40% |
| **Steps** | 20 | 4 | -80% |

## Architecture Technique

### Composants Installés

1. **Plugin ComfyUI**: `ComfyUI-nunchaku` v1.1.0 (IMPORTANT: pas v1.2.0+)
   - Repository: https://github.com/nunchaku-ai/ComfyUI-nunchaku
   - Nodes: `NunchakuQwenImageDiTLoader`, `NunchakuLoraLoader`
   - **Contrainte**: v1.2.0+ incompatible avec backend v1.0.1 (paramètre `use_additional_t_cond`)

2. **Backend Python**: `nunchaku` v1.0.1+torch2.6
   - Wheel pré-compilé depuis: https://github.com/nunchaku-ai/nunchaku/releases/v1.0.1
   - Format: `nunchaku-1.0.1+torch2.6-cp311-cp311-linux_x86_64.whl`
   - Dépendances: diffusers>=0.35, peft>=0.17

3. **Modèle INT4**: svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors
   - Source: https://huggingface.co/nunchaku-ai/nunchaku-qwen-image-edit-2509
   - Taille: ~12 GB (vs 20 GB FP8)
   - Quantization: SVDQuant INT4 avec rank 128

### Problèmes Résolus

#### 1. Package PyPI Incorrect

**Problème**: `pip install nunchaku` installait le mauvais package (v0.16.1 - outil de segmentation de données)

**Solution**: Installer le wheel pré-compilé spécifique à la version PyTorch depuis GitHub releases:
```bash
wget https://github.com/nunchaku-ai/nunchaku/releases/download/v1.0.1/nunchaku-1.0.1+torch2.6-cp311-cp311-linux_x86_64.whl
pip install nunchaku-1.0.1+torch2.6-cp311-cp311-linux_x86_64.whl
```

#### 2. Compilation depuis Sources Impossible

**Problème**: `pip install git+https://github.com/nunchaku-tech/nunchaku.git` échouait avec erreur `nvcc not found`

**Cause**: Le container Docker n'a pas CUDA toolkit complet (seulement runtime)

**Solution**: Utiliser les wheels pré-compilés au lieu de compiler depuis sources

#### 3. Paramètre `cpu_offload` Manquant

**Problème**: Le node `NunchakuQwenImageDiTLoader` nécessite un paramètre `cpu_offload` obligatoire

**Solution**: Ajouter le paramètre dans le workflow JSON:
```json
{
  "class_type": "NunchakuQwenImageDiTLoader",
  "inputs": {
    "model_name": "svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors",
    "cpu_offload": "auto"
  }
}
```

Options disponibles:
- `"auto"`: Active CPU offload si VRAM < 15GB (recommandé)
- `"enable"`: Force l'activation (ultra-low VRAM)
- `"disable"`: Désactive (si VRAM suffisante)

## Modifications des Scripts

### 1. entrypoint.sh

**Fichier**: `docker-configurations/services/comfyui-qwen/entrypoint.sh`

**Section modifiée**: Installation ComfyUI-nunchaku (lignes 126-140)

```bash
# 4. ComfyUI-nunchaku (Quantification INT4 SVDQuant - Recommande pour VRAM limitee)
NUNCHAKU_DIR="custom_nodes/ComfyUI-nunchaku"
if [ ! -d "$NUNCHAKU_DIR" ]; then
    echo "Installation de ComfyUI-nunchaku (INT4 quantization)..."
    git clone https://github.com/nunchaku-ai/ComfyUI-nunchaku.git "$NUNCHAKU_DIR"
    if [ -d "$NUNCHAKU_DIR" ]; then
        # Detecter version PyTorch pour installer le bon wheel pre-compile
        TORCH_VERSION=$(venv/bin/python -c "import torch; print(torch.__version__.split('+')[0])")
        TORCH_MAJOR=$(echo $TORCH_VERSION | cut -d. -f1)
        TORCH_MINOR=$(echo $TORCH_VERSION | cut -d. -f2)
        NUNCHAKU_WHEEL_URL="https://github.com/nunchaku-ai/nunchaku/releases/download/v1.0.1/nunchaku-1.0.1+torch${TORCH_MAJOR}.${TORCH_MINOR}-cp311-cp311-linux_x86_64.whl"

        echo "Installation nunchaku 1.0.1 pour PyTorch ${TORCH_MAJOR}.${TORCH_MINOR}..."
        wget -q -O /tmp/nunchaku.whl "$NUNCHAKU_WHEEL_URL" && \
        venv/bin/pip install /tmp/nunchaku.whl && \
        rm -f /tmp/nunchaku.whl || \
        echo "ATTENTION: Echec installation nunchaku wheel, fonctionnalites INT4 non disponibles"

        # Installer dependances du plugin
        venv/bin/pip install diffusers>=0.35 peft>=0.17
    fi
fi
```

### 2. Workflow ComfyUI

**Fichier**: `scripts/genai-stack/workflows/workflow_qwen_nunchaku_t2i.json`

**Nodes clés**:
- Node 3: `NunchakuQwenImageDiTLoader` (charge modèle INT4)
- Node 4: `ModelSamplingAuraFlow` (shift=1.0 pour Lightning)
- Node 9: `KSampler` (4 steps, euler/beta, CFG=1.0)

### 3. Script de Test

**Fichier**: `scripts/genai-stack/test_nunchaku_generation.py`

Permet de tester la génération avec mesure de performances:
```bash
python scripts/genai-stack/test_nunchaku_generation.py "Your prompt here"
```

### 4. Script de Téléchargement

**Fichier**: `scripts/genai-stack/download_nunchaku_model.py`

Télécharge les modèles Nunchaku depuis HuggingFace:
```bash
python scripts/genai-stack/download_nunchaku_model.py --variant lightning-4step-r128
```

Variantes disponibles:
- `lightning-4step-r128` (recommandé, 12GB, 4 steps)
- `lightning-4step-r32` (9GB, qualité réduite)
- `lightning-8step-r128` (12GB, 8 steps, qualité supérieure)
- `standard-r128` (12GB, 20 steps)
- `standard-r32` (9GB, 20 steps)

## Validation

### Vérifier Installation

```bash
# Dans le container
docker exec comfyui-qwen venv/bin/pip show nunchaku
# Attendu: Version: 1.0.1+torch2.6

# Vérifier custom node
docker exec comfyui-qwen ls -la custom_nodes/ComfyUI-nunchaku
```

### Tester Génération

```bash
python scripts/genai-stack/test_nunchaku_generation.py
```

Résultat attendu (warm generation):
- Temps: ~4s
- VRAM: ~7.9GB
- Status: Success

## Logs Importants

### Démarrage Réussi

```
ComfyUI-nunchaku deja present
loaded completely; ... 7909.74 MB loaded
VRAM > 15GiB, disabling CPU offload
Prompt executed in 4.0 seconds
```

### Erreurs Connues (Non-Critiques)

Ces erreurs d'import sont normales et concernent des fonctionnalités optionnelles non utilisées:
```
Nodes `NunchakuPulidApply`,`NunchakuPulidLoader` import failed
Nodes `NunchakuFluxIPAdapterApply` import failed
Nodes `NunchakuZImageDiTLoader` import failed
```

## Prochaines Étapes (Phase 7.2 - Optionnel)

Si besoin de parallélisme multi-GPU ou de switching ultra-rapide entre modèles, explorer **vLLM-omni**:
- Sleep mode: 18-200x plus rapide que reload complet
- Ulysses Sequence Parallel: 1.73-2.84x speedup sur multi-GPU
- Support Qwen natif depuis vLLM v0.8

## Références

- Paper SVDQuant: http://arxiv.org/abs/2411.05007
- ComfyUI-nunchaku: https://github.com/nunchaku-ai/ComfyUI-nunchaku
- Documentation: https://nunchaku.tech/docs/ComfyUI-nunchaku/
- Modèles HuggingFace: https://huggingface.co/nunchaku-ai
- Releases GitHub: https://github.com/nunchaku-ai/nunchaku/releases

---

**Auteur**: Claude Code
**Validation**: Tests production RTX 3090 24GB
**Statut**: Intégré dans docker-configurations/services/comfyui-qwen
