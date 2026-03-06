# Models Directory - GenAI Ecosystem

Répertoire partagé pour tous les modèles GenAI utilisés par les différents services de l'écosystème.

## 📁 Structure Recommandée

```
models/
├── checkpoints/              (modèles principaux - Stable Diffusion, Qwen, etc.)
│   ├── Qwen-Image-Edit-2509-FP8/
│   ├── stable-diffusion-3.5-large/
│   └── flux-1-dev/
├── vae/                     (VAE models)
│   ├── qwen_image_vae.safetensors
│   └── sdxl_vae.safetensors
├── unet/                    (UNET models)
│   └── qwen_image_edit_2509_fp8_e4m3fn.safetensors
├── clip/                     (CLIP models)
│   └── qwen_2.5_vl_7b_fp8_scaled.safetensors
├── lora/                    (LoRA adapters)
├── embeddings/              (textual embeddings)
├── controlnet/              (ControlNet models)
└── upscale/                 (upscaling models)
```

## 🚀 Modèles Principaux

### Qwen Image-Edit 2509 FP8

**Modèle principal pour ComfyUI Qwen** :

- **Nom** : `Qwen-Image-Edit-2509-FP8`
- **Taille** : ~54GB (quantifié FP8)
- **Architecture** : 3 composants séparés
- **Emplacement** : `checkpoints/Qwen-Image-Edit-2509-FP8/`

**Composants** :
- **UNET** : `qwen_image_edit_2509_fp8_e4m3fn.safetensors` (20GB)
- **CLIP** : `qwen_2.5_vl_7b_fp8_scaled.safetensors` (8.8GB)
- **VAE** : `qwen_image_vae.safetensors` (243MB)

### Installation Automatisée

Les modèles Qwen sont installés automatiquement par :
```bash
python scripts/genai-auth/core/setup_complete_qwen.py
```

## 🔧 Configuration Docker

### Volumes dans Docker Compose

Les modèles sont montés en lecture seule pour la sécurité :

```yaml
volumes:
  - genai-models:/app/models:ro
```

### Permissions

- **Lecture seule** : Les conteneurs ne peuvent pas modifier les modèles
- **Partage** : Accessible par tous les services GenAI
- **Backup** : Inclu dans les sauvegardes système

## 📊 Gestion des Modèles

### Téléchargement

**Via scripts genai-auth** :
```bash
# Installation complète Qwen
python scripts/genai-auth/core/setup_complete_qwen.py

# Validation des modèles
python scripts/genai-auth/core/validate_genai_ecosystem.py
```

**Via HuggingFace CLI** :
```bash
# Téléchargement manuel
huggingface-cli download Qwen/Qwen-Image-Edit-2509 --local-dir checkpoints/Qwen-Image-Edit-2509-FP8
```

### Validation

**Vérification intégrité** :
```bash
# Validation complète écosystème
python scripts/genai-auth/core/validate_genai_ecosystem.py --models

# Diagnostic modèles spécifiques
python scripts/genai-auth/utils/diagnostic_utils.py --check-models
```

## 💾 Stockage et Performance

### Espace Requis

- **Qwen complet** : ~54GB
- **Stable Diffusion 3.5** : ~12GB
- **FLUX.1-dev** : ~35GB
- **Total recommandé** : 200GB+

### Optimisations

- **Quantification FP8** : Réduction taille sans perte significative
- **Lazy loading** : Chargement à la demande dans ComfyUI
- **Cache GPU** : Optimisation VRAM avec modèles partagés

## 🔒 Sécurité

### Isolation

- **Read-only mounts** : Protection contre les modifications
- **Permissions restreintes** : Accès uniquement aux services autorisés
- **Backup automatique** : Inclusion dans les sauvegardes système

### Tokens et Authentification

Les tokens pour les téléchargements sont gérés via :
- `.secrets/.env.huggingface` : Token HuggingFace
- `.secrets/.env.civitai` : Token CivitAI
- Variables d'environnement sécurisées

## 🚨 Dépannage

### Problèmes Communs

1. **Modèles non trouvés** :
   ```bash
   # Vérifier la structure
   ls -la models/checkpoints/
   
   # Valider avec scripts
   python scripts/genai-auth/core/validate_genai_ecosystem.py
   ```

2. **Espace insuffisant** :
   ```bash
   # Vérifier l'espace disponible
   df -h models/
   
   # Nettoyer les anciens modèles
   python scripts/genai-auth/utils/cleanup_models.py
   ```

3. **Permissions incorrectes** :
   ```bash
   # Corriger les permissions
   chmod -R 755 models/
   chown -R $USER:$USER models/
   ```

### Diagnostic Complet

```bash
# Validation complète du système
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose --models

# Diagnostic détaillé
python scripts/genai-auth/utils/diagnostic_utils.py --full-scan
```

## 📚 Références

### Documentation

- **Scripts GenAI-Auth** : `../scripts/genai-auth/README.md`
- **Configuration ComfyUI** : `../comfyui-qwen/README.md`
- **Architecture GenAI** : `../../docs/genai/`

### Modèles Supportés

- **Qwen Image-Edit** : https://huggingface.co/Qwen/Qwen-Image-Edit-2509
- **Stable Diffusion 3.5** : https://huggingface.co/stabilityai/stable-diffusion-3.5-large
- **FLUX.1-dev** : https://huggingface.co/black-forest-labs/FLUX.1-dev

---

**Dernière mise à jour** : 2025-11-25  
**Version** : 2.0.0  
**Statut** : Production Ready ✅  
**Compatibilité** : Scripts genai-auth Phase 29+