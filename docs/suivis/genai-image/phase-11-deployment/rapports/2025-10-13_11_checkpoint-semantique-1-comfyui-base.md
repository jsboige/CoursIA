# Checkpoint Sémantique 1: ComfyUI Base Installé

**Date:** 2025-10-13  
**Phase:** Phase 11 - Déploiement ComfyUI + Qwen Image-Edit  
**Status:** ✅ ComfyUI base installé et validé

---

## 📊 État Actuel

### Installation ComfyUI

**Workspace:** `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI`

**Version ComfyUI:**
- Repository: `https://github.com/comfyanonymous/ComfyUI.git`
- Clone: ✅ Complété
- Environnement virtuel Python: ✅ Créé (`venv/`)

**Dependencies Installées:**
```bash
PyTorch: 2.6.0+cu124
CUDA: 12.4
Python: 3.12
```

**Packages ComfyUI Installés:**
- comfyui-frontend-package: 1.27.10
- comfyui-workflow-templates: 0.1.94
- comfyui-embedded-docs: 0.2.6
- torch, torchvision, torchaudio (CUDA 12.4)
- transformers: 4.57.0
- safetensors: 0.6.2
- aiohttp: 3.13.0
- kornia: 0.8.1
- spandrel: 0.4.1
- pydantic: 2.12.0
- scipy: 1.16.2
- SQLAlchemy: 2.0.44
- et 30+ autres dépendances

---

## 🎮 Configuration GPU - IMPORTANT

### Architecture GPU Détectée (WSL)

```
GPU 0: NVIDIA GeForce RTX 3090
├─ VRAM: 24.00 GB
├─ Allocation: ComfyUI + Qwen Image-Edit (GPU 0)
└─ Device ID: 0

GPU 1: NVIDIA GeForce RTX 3080 Ti Laptop GPU
├─ VRAM: 16.00 GB  
├─ Allocation: Forge SD XL Turbo (GPU 1)
└─ Device ID: 1
```

### ⚠️ CORRECTION ARCHITECTURE

**Architecture Initiale (Prévue):**
```
GPU 0 (RTX 3080): Forge ❌
GPU 1 (RTX 3090): ComfyUI ❌
```

**Architecture Réelle (Détectée):**
```
GPU 0 (RTX 3090): ComfyUI ✅
GPU 1 (RTX 3080 Ti): Forge ✅
```

**Impact sur Déploiement:**
- `CUDA_VISIBLE_DEVICES=0` pour ComfyUI (au lieu de 1)
- `device_ids: ['0']` dans docker-compose (au lieu de ['1'])
- URL reste inchangée: `https://qwen-image-edit.myia.io`

---

## ✅ Validations Effectuées

### 1. Python Environment
```bash
✅ Python 3.12 disponible
✅ venv créé et activé
✅ pip upgrade réussi
```

### 2. PyTorch + CUDA
```python
✅ PyTorch 2.6.0+cu124 installé
✅ CUDA disponible: True
✅ CUDA version: 12.4
✅ GPU count: 2 (3090 + 3080 Ti)
```

### 3. ComfyUI Dependencies
```bash
✅ requirements.txt installé (46 packages)
✅ Transformers 4.57.0 (support Qwen)
✅ Safetensors 0.6.2 (support FP8)
✅ Kornia + custom nodes support
```

---

## 📂 Structure Actuelle

```
/home/jesse/SD/workspace/comfyui-qwen/
└── ComfyUI/
    ├── venv/                    # Environnement Python isolé
    ├── requirements.txt         # Dependencies installées
    ├── main.py                  # Point d'entrée
    ├── models/                  # Répertoire modèles (à peupler)
    │   ├── checkpoints/         # Pour Qwen-Image-Edit-2509
    │   ├── loras/
    │   ├── vae/
    │   └── controlnet/
    ├── custom_nodes/            # Custom nodes (à installer)
    │   └── (vide pour l'instant)
    ├── input/                   # Images input
    ├── output/                  # Images générées
    └── temp/                    # Fichiers temporaires
```

---

## 🔄 Prochaines Étapes

### Phase 4: Installation Qwen Image-Edit

**Étape 4.1: Téléchargement Modèle**
```bash
# Modèle cible: Qwen/Qwen-Image-Edit-2509 FP8
# Taille: ~12GB
# Destination: models/checkpoints/Qwen-Image-Edit-2509-FP8/
```

**Étape 4.2: Custom Node ComfyUI-QwenImageWanBridge**
```bash
# Clone: https://github.com/qwenImage/ComfyUI-QwenImageWanBridge
# Installation dans: custom_nodes/ComfyUI-QwenImageWanBridge/
```

**Étape 4.3: Tests Standalone**
```bash
# Lancement avec GPU 0 (3090):
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188

# Validation:
# - GPU 0 (RTX 3090) utilisé
# - Qwen-Image-Edit-2509 chargé
# - Web UI accessible sur :8188
```

---

## 📋 Métriques Installation

| Métrique | Valeur |
|----------|--------|
| **Temps Installation** | ~5 min |
| **Taille Dependencies** | ~800 MB |
| **GPU Détectés** | 2 (3090 + 3080 Ti) |
| **VRAM Disponible GPU 0** | 24 GB |
| **Workspace Total** | 215 GB (modèles existants) |
| **Python Version** | 3.12 |
| **CUDA Version** | 12.4 |
| **PyTorch Version** | 2.6.0+cu124 |

---

## ⚠️ Points d'Attention

### 1. GPU Allocation Inversée
- Adapter tous les scripts/configs pour GPU 0 au lieu de GPU 1
- Vérifier que Forge reste sur GPU 1 (ne pas perturber)

### 2. Modèles Partagés
- 215GB de modèles existants déjà disponibles
- Vérifier compatibilité modèles FLUX/SDXL avec ComfyUI
- Éviter doublons de modèles

### 3. VRAM Management
- GPU 0 (24GB) suffisant pour Qwen FP8 (~12GB)
- Marge confortable pour multi-images editing

---

## 🎯 Checkpoint Validation

**Critères de Succès:**
- [x] ComfyUI cloné depuis GitHub officiel
- [x] Environnement Python 3.12 + venv créé
- [x] PyTorch 2.6.0+cu124 installé avec support CUDA
- [x] 46 packages dependencies installés
- [x] GPU 0 (RTX 3090 24GB) détecté et prêt
- [x] Structure répertoires modèles préparée

**Status:** ✅ **VALIDÉ - Prêt pour Phase 4 (Qwen Installation)**

---

## 📝 Notes Techniques

### Scripts Créés
- `docs/suivis/genai-image/2025-10-13_11_install-comfyui-requirements.sh`
  - Installation automatisée des requirements
  - Validation PyTorch + CUDA
  - Détection GPUs disponibles

### Commandes Utiles
```bash
# Activer environnement
source /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv/bin/activate

# Vérifier GPU
nvidia-smi

# Vérifier PyTorch
python -c "import torch; print(torch.cuda.is_available())"

# Lancer ComfyUI (après installation Qwen)
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188
```

---

## 🔗 Références

- **ComfyUI GitHub:** https://github.com/comfyanonymous/ComfyUI
- **PyTorch CUDA 12.4:** https://pytorch.org/get-started/locally/
- **Qwen Image-Edit:** https://huggingface.co/Qwen/Qwen-Image-Edit-2509
- **Custom Node Bridge:** https://github.com/qwenImage/ComfyUI-QwenImageWanBridge

---

**Prochaine Étape:** Téléchargement Qwen-Image-Edit-2509 FP8 (~12GB)