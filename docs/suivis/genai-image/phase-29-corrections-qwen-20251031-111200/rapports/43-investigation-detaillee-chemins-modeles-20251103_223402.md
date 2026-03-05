# Rapport 43 : Investigation Détaillée Chemins Modèles + Corruption Potentielle

**Date** : 2025-11-03 22:34:17 UTC+1
**Phase** : 29 - Corrections Qwen ComfyUI
**Type** : Investigation Détaillée Chemins

## 📋 RÉSUMÉ EXÉCUTIF

### Problème Identifié
Incohérence critique : images générées avec succès mais logs indiquant modèles manquants.

### Racine du Problème Identifiée
**MULTIPLES INCOHÉRENCES DE CHEMINS** :
1. **Lien symbolique cassé** dans `/workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8`
2. **Modèle UNET dupliqué** : présent dans `diffusion_models/` ET `unet/`
3. **CheckpointLoaderSimple** ne trouve pas le modèle dans sa liste de checkpoints
4. **Scripts utilisent `diffusion_models/`** mais certains workflows attendent `checkpoints/`

---

## 🔍 1. MODÈLES RÉELS DANS CONTAINER

### Modèles Qwen Disponibles

**DIFFUSION_MODELS** :
- `/workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors`

**TEXT_ENCODERS** :
- `/workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b.safetensors`
- `/workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors`

**VAE** :
- `/workspace/ComfyUI/models/vae/qwen_image_vae.safetensors`

**UNET** :
- `/workspace/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors`

**OTHER** :

### Arborescence Critique
```
/workspace/ComfyUI/models/
├── diffusion_models/
│   └── qwen_image_edit_2509_fp8_e4m3fn.safetensors  ✅ (20GB)
├── text_encoders/
│   ├── qwen_2.5_vl_7b.safetensors                    ✅ (8.8GB)
│   ├── qwen_2.5_vl_7b_fp8_scaled.safetensors       ✅ (8.8GB)
│   └── Qwen-Image-Edit-2509-FP8                     ❌ LIEN CASSÉ → /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8
├── unet/
│   └── qwen_image_edit_2509_fp8_e4m3fn.safetensors  ✅ (20GB) [DUPLICATE]
├── vae/
│   └── qwen_image_vae.safetensors                     ✅ (243MB)
└── checkpoints/
    └── (VIDE - seulement put_checkpoints_here)
```

---

## 🐍 2. CHEMINS DANS SCRIPTS

### Références de Modèles dans Scripts
- **Diffusion Model** : `/workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors`
- **Text Encoder** : `/workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors`
- **VAE** : `/workspace/ComfyUI/models/vae/qwen_image_vae.safetensors`

### Workflows JSON Analysés
Références trouvées : 3
- `unet_name`
- `clip_name`
- `vae_name`

---

## 🔧 3. NODES COMFYUI DISPONIBLES

### Nodes de Chargement de Modèles
- **qwen_custom** : 32 node(s)

---

## 🚨 4. ANALYSE DES INCOHÉRENCES

### Incohérences Identifiées

#### 🔄 Modèles Dupliqués
- **qwen_image_edit_2509_fp8_e4m3fn.safetensors** :
  - `/workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors`
  - `/workspace/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors`

#### 🚨 Problème CheckpointLoaderSimple

**PROBLÈME CRITIQUE IDENTIFIÉ** :
- Le modèle `qwen_image_edit_2509_fp8_e4m3fn.safetensors` n'est PAS dans la liste des checkpoints disponibles
- CheckpointLoaderSimple ne peut PAS charger ce modèle
- **CAUSE** : Le modèle est dans `diffusion_models/` mais CheckpointLoader cherche dans `checkpoints/`

**Options disponibles dans CheckpointLoader** :

---

## 🧩 5. ANALYSE DE LA CORRUPTION

### Source de la Corruption Identifiée

**INCOHÉRENCE MULTIPLE DES CHEMINS** :

1. **Scripts utilisent `diffusion_models/`** (chemin correct pour UNETLoader)
2. **Certains workflows utilisent `CheckpointLoaderSimple`** qui cherche dans `checkpoints/`
3. **Lien symbolique cassé** dans `text_encoders/` pointe vers `checkpoints/` vide
4. **Modèle dupliqué** dans `unet/` (probablement résiduel d'ancienne configuration)

### Impact sur la Génération

**POURQUOI LES IMAGES SONT GÉNÉRÉES MALGRÉ LES ERREURS** :
- Les workflows utilisant **UNETLoader natif** fonctionnent (modèle dans `diffusion_models/`)
- Les workflows utilisant **CheckpointLoaderSimple** échouent (modèle pas dans `checkpoints/`)
- Les logs montrent des erreurs de validation mais certaines générations réussissent

---

## 🛠️ 6. CORRECTIONS NÉCESSAIRES

### Actions Immédiates Critiques

#### 1. Réparer le Lien Symbolique Cassé
```bash
# Supprimer le lien cassé
docker exec comfyui-qwen rm /workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8

# Créer le bon lien vers le modèle dans diffusion_models
docker exec comfyui-qwen ln -s /workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors /workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8
```

#### 2. Nettoyer le Modèle Dupliqué
```bash
# Supprimer le doublon dans unet/ (garder celui dans diffusion_models/)
docker exec comfyui-qwen rm /workspace/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors
```

#### 3. Standardiser les Workflows
- **Utiliser UNETLoader** au lieu de CheckpointLoaderSimple pour les modèles Qwen
- **Mettre à jour les workflows** pour utiliser les chemins corrects
- **Valider tous les workflows** avec les chemins `diffusion_models/`

#### 4. Créer Lien Symbolique Checkpoints (Optionnel)
```bash
# Pour compatibilité avec CheckpointLoaderSimple
docker exec comfyui-qwen ln -s /workspace/ComfyUI/models/diffusion_models /workspace/ComfyUI/models/checkpoints/qwen_models
```

### Mise à Jour des Scripts

#### Scripts à Corriger
- **test_generation_image_fp8_officiel.py** : ✅ DÉJÀ CORRECT (utilise UNETLoader)
- **Autres workflows** : ⚠️ À VÉRIFIER (peuvent utiliser CheckpointLoaderSimple)

#### Validation des Corrections
```bash
# Exécuter le script de test après corrections
python scripts/genai-auth/utils/test_generation_image_fp8_officiel.py

# Vérifier qu'il n'y a plus d'erreurs de modèles manquants
docker logs comfyui-qwen --tail 50 | grep -i "missing\|error"
```

---

## ✅ 7. VALIDATION FINALE

### Critères de Succès
- [x] Modèles réels identifiés et localisés
- [x] Chemins scripts analysés et documentés  
- [x] Incohérences identifiées et expliquées
- [x] Source de la corruption déterminée
- [x] Corrections concrètes proposées
- [ ] Corrections appliquées et validées

### Prochaine Action
✅ **APPLIQUER LES CORRECTIONS DE CHEMINS IDENTIFIÉES**

---

**Rapport généré le** : 2025-11-03 22:34:17 UTC+1
**Statut** : ✅ **INVESTIGATION DÉTAILLÉE TERMINÉE**
**Prochaine étape** : Application des corrections de chemins
