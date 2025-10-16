# Checkpoint Sémantique 2: ComfyUI + Qwen Standalone Validé

**Date**: 2025-10-13  
**Phase**: 11 - Déploiement ComfyUI + Qwen Image-Edit  
**Statut**: ✅ STANDALONE OPÉRATIONNEL

---

## Résolution Mapping GPU (CRITIQUE)

### Problème Initial
```
PyTorch voit:
  GPU 0: RTX 3090 (24GB)
  GPU 1: RTX 3080 Ti (16GB)

nvidia-smi voit:
  GPU 0: RTX 3080 Ti (16GB)
  GPU 1: RTX 3090 (24GB)
```

### Solution Trouvée
**Mapping inversé entre PyTorch et nvidia-smi:**
- nvidia-smi GPU 1 = PyTorch GPU 0 (RTX 3090)
- nvidia-smi GPU 0 = PyTorch GPU 1 (RTX 3080 Ti)

**Configuration Validée:**
```bash
CUDA_VISIBLE_DEVICES=0  # Pour utiliser la RTX 3090 en PyTorch
```

### Tests de Validation
```bash
# Test 1: CUDA_VISIBLE_DEVICES=0
- GPU détectée: NVIDIA GeForce RTX 3090
- Mémoire: 25.8 GB
- Compute Capability: 8.6
- Test allocation 1GB: ✅ SUCCÈS

# Test 2: CUDA_VISIBLE_DEVICES=1  
- GPU détectée: NVIDIA GeForce RTX 3080 Ti
- Mémoire: 17.2 GB
- Compute Capability: 8.6
```

**RÉSULTAT FINAL:** `CUDA_VISIBLE_DEVICES=0` utilise bien la RTX 3090 (24GB)

---

## Configuration ComfyUI

### Installation
- **Workspace**: `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI`
- **Version ComfyUI**: 0.3.664
- **Version PyTorch**: 2.6.0+cu124
- **CUDA Version**: 12.4
- **Python**: 3.12.3

### Modèle Qwen Image-Edit
- **Nom**: Qwen-Image-Edit-2509-FP8
- **Emplacement**: `models/checkpoints/Qwen-Image-Edit-2509-FP8/`
- **Taille**: ~54GB (quantifié FP8)
- **Fichiers principaux**:
  - `README.md`
  - `model_index.json`
  - `processor/`
  - `scheduler/`
  - `text_encoder/`
  - `transformer/`
  - `vae/`

### Custom Node
- **Nom**: ComfyUI-QwenImageWanBridge
- **Emplacement**: `custom_nodes/ComfyUI-QwenImageWanBridge/`
- **Statut**: ✅ Installé et reconnu

---

## Tests Standalone

### Démarrage ComfyUI
```bash
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188 --preview-method auto
```

### Résultats Tests
- ✅ **ComfyUI démarré** sur port 8188 (temps: ~10s)
- ✅ **GPU 3090 détectée**: 
  - Total VRAM: 24576 MB
  - VRAM utilisée au démarrage: 1009 MB (~1GB)
- ✅ **Port 8188 accessible**: HTTP OK
- ✅ **API system_stats**: Réponse JSON valide
- ✅ **Interface Web**: Chargée avec succès
- ✅ **Modèle Qwen**: Disponible dans liste checkpoints

### Métriques Performance
```
GPU 1 (RTX 3090):
- Mémoire utilisée: 1009 MiB / 24576 MiB (4.1%)
- Utilization GPU: 0% (idle)
- Temps démarrage: ~10 secondes
- Temps chargement modèle: Lazy loading (à la première utilisation)
```

### API system_stats (extrait)
```json
{
  "system": {
    "os": "posix",
    "ram_total": 33494831104,
    "ram_free": 21102628864,
    "comfyui_version": "0.3.664",
    "required_frontend_version": "1.27.10",
    "python_version": "3.12.3",
    "pytorch_version": "2.6.0+cu124",
    "embedded_python": false
  }
}
```

---

## Workflows Disponibles

### Interface ComfyUI
- **URL**: http://localhost:8188
- **Frontend Version**: 1.27.10
- **Templates Version**: 0.1.94

### Exemples Intégrés
Catégories visibles dans l'interface:
- Getting Started
- Image Generation
- Image to Image
- Video
- Audio
- 3D Model
- API d'image
- API vidéo
- 3D API
- Audio API

### Custom Nodes Qwen
- Custom node `ComfyUI-QwenImageWanBridge` chargé
- Nodes disponibles pour workflows Qwen Image-Edit
- Compatible avec modèle Qwen-Image-Edit-2509-FP8

---

## Architecture Validée

### Configuration GPU
```
GPU physique 0 (RTX 3080 Ti 16GB):
├─ nvidia-smi index: 0
├─ PyTorch index: 1
└─ Usage: Forge SD XL Turbo (ne pas toucher)

GPU physique 1 (RTX 3090 24GB):
├─ nvidia-smi index: 1
├─ PyTorch index: 0  ← UTILISÉ PAR COMFYUI
└─ Usage: ComfyUI + Qwen Image-Edit
```

### Commande Validée
```bash
# Lancement ComfyUI avec GPU 3090
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188 --preview-method auto
```

---

## Prochaines Étapes

### Phase Dockerisation
1. ✅ Mapping GPU résolu: `CUDA_VISIBLE_DEVICES=0`
2. ✅ ComfyUI standalone validé
3. ⏭️ Créer `docker-compose-comfyui.yaml` (GPU device_ids: ['0'])
4. ⏭️ Tester container Docker avec GPU 3090
5. ⏭️ Configurer reverse proxy IIS (qwen-image-edit.myia.io)
6. ⏭️ Tests génération production

### Volumes Docker Requis
```yaml
volumes:
  - type: bind
    source: \\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI
    target: /workspace/ComfyUI
```

### Variables Environnement Docker
```yaml
environment:
  - CUDA_VISIBLE_DEVICES=0
  - NVIDIA_VISIBLE_DEVICES=0
  - PYTHONUNBUFFERED=1
```

---

## Logs et Debugging

### Logs Démarrage
```
Total VRAM 24576 MB, total RAM 31943 MB
To see the GUI go to: http://0.0.0.0:8188
```

### Fichier Logs
- **Emplacement**: `logs/comfyui-standalone.log`
- **Commande suivi**: `tail -f logs/comfyui-standalone.log`

### Arrêt Processus
```bash
# Trouver PID
ps aux | grep "python.*main.py.*8188"

# Arrêter
pkill -f "python.*main.py.*8188"
```

---

## Validation Complète

### Checklist Standalone
- [x] ComfyUI installé et configuré
- [x] PyTorch 2.6.0+cu124 avec CUDA 12.4
- [x] Mapping GPU résolu (CUDA_VISIBLE_DEVICES=0)
- [x] RTX 3090 détectée et utilisée
- [x] Modèle Qwen-Image-Edit-2509-FP8 disponible
- [x] Custom node ComfyUI-QwenImageWanBridge chargé
- [x] Port 8188 accessible
- [x] Interface Web fonctionnelle
- [x] API system_stats opérationnelle
- [x] VRAM gérée correctement (~1GB idle)

### État Production-Ready
**STANDALONE: READY FOR DOCKERIZATION ✅**

---

## Références Scripts

### Scripts Créés
1. `2025-10-13_11_resolve-gpu-mapping.sh` - Résolution mapping GPU
2. `2025-10-13_11_launch-comfyui-standalone.sh` - Lancement standalone
3. `2025-10-13_11_test-comfyui-background.sh` - Test background + validation

### Scripts Utilisés
- Installation requirements
- Téléchargement modèle Qwen
- Installation custom node

---

## Notes Importantes

### Mapping GPU Critique
⚠️ **TOUJOURS** utiliser `CUDA_VISIBLE_DEVICES=0` pour la RTX 3090  
⚠️ Ne **JAMAIS** utiliser `CUDA_VISIBLE_DEVICES=1` (RTX 3080 Ti - Forge)

### Isolation GPU
- GPU 0 (3080 Ti): Forge SD XL Turbo (Port 7860)
- GPU 1 (3090): ComfyUI + Qwen (Port 8188)
- Aucune interférence entre les services

### Performance
- Démarrage rapide (~10s)
- VRAM idle faible (~1GB)
- Chargement modèle lazy (à la demande)
- Prêt pour production

---

**CHECKPOINT VALIDÉ** ✅  
**Date**: 2025-10-13 22:52 UTC  
**Prêt pour**: Phase Dockerisation (Checkpoint 3)