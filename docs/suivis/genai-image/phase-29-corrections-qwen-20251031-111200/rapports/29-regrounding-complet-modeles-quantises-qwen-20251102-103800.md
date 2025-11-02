# RAPPORT SDDD : Regrounding Archéologique Complet des Modèles Quantisés Qwen
**Phase 29 - ÉTAPE 24E**

**Date**: 2025-11-02 10:38:00  
**Auteur**: Roo, Architecte IA  
**Mission**: Reconstituer la documentation, la procédure de téléchargement, l'architecture et les workflows validés historiquement pour les modèles Qwen quantisés (Q4/FP8/GGUF).

---

## 1. Synthèse Exécutive

Cette investigation archéologique a permis de **résoudre la contradiction fondamentale** qui a causé les échecs récents. L'historique du projet et la documentation officielle convergent vers une conclusion unique : il existe **deux architectures Qwen distinctes et incompatibles** qui ont été confondues.

1.  **Architecture Historique (erronée)** : Basée sur le repository `Qwen/Qwen-Image-Edit-2509` au format **Diffusers/Sharded**. C'est cette version qui pèse **~54GB**. Elle nécessite des **custom nodes spécifiques (`ComfyUI-QwenImageWanBridge`)** pour fonctionner, car elle n'est pas nativement compatible avec ComfyUI. C'est cette architecture qui a été utilisée dans les phases initiales (11, 12) mais qui est désormais obsolète et source de complexité.

2.  **Architecture Officielle (correcte)** : Basée sur les repositories `Comfy-Org/Qwen-Image_ComfyUI` qui fournissent des modèles au format **`.safetensors` unifié**. Cette version est **100% native à ComfyUI**, ne requiert **AUCUN custom node externe** pour les opérations de base et pèse environ **20GB** en FP8. Des versions GGUF encore plus légères (Q4, Q8) sont également disponibles pour les faibles VRAM.

**La cause racine des problèmes actuels est la tentative d'utiliser un workflow natif (`.safetensors`) avec un modèle au format Diffusers (`sharded`).** Ce rapport reconstitue l'architecture correcte et officielle.

---

## 2. Réponses aux Questions Critiques

### 2.1. Quels modèles quantisés exactement ?

L'historique et la documentation officielle valident plusieurs niveaux de quantization, chacun avec un cas d'usage précis :

| Format | Modèle Spécifique | Taille | VRAM Requise | Qualité | Cas d'Usage | Source Officielle |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **FP8** | `qwen_image_edit_fp8_e4m3fn.safetensors` | ~20.4 GB | 12-14 GB | Très Haute | **Production & Qualité Maximale** | `Comfy-Org` |
| **GGUF Q8**| `qwen-image-edit-2509-Q8_0.gguf` | ~10 GB | 8-10 GB | Haute | Bon équilibre Qualité/Performance | Multiples |
| **GGUF Q4**| `qwen-image-edit-2509-Q4_K_M.gguf` | ~6 GB | 6-8 GB | Moyenne | **Faible VRAM & Prototypage Rapide** | Multiples |

**Conclusion** : Le modèle **FP8** est la version de référence pour la production. Les modèles **GGUF** sont des alternatives viables et historiquement considérées pour les environnements à ressources limitées.

### 2.2. Quelle URL HuggingFace précise ?

- **Source Principale (Recommandée, format `.safetensors` natif)** :
  - **URL**: `https://huggingface.co/Comfy-Org/Qwen-Image-Edit_ComfyUI`
  - **Fichiers Clés**:
    - `split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors`
    - `split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors`
    - `split_files/vae/qwen_image_vae.safetensors`

- **Source Historique (Obsolète, format `Diffusers`)** :
  - **URL**: `https://huggingface.co/Qwen/Qwen-Image-Edit-2509`

### 2.3. Quel workflow JSON utilisé ?

Le workflow valide est **100% natif ComfyUI** et n'utilise aucun custom node externe.

- **Workflow de Référence (Image-to-Image Editing)** :
  - **URL de téléchargement (JSON)**: `https://raw.githubusercontent.com/Comfy-Org/workflow_templates/refs/heads/main/templates/image_qwen_image_edit.json`
  - **Workflow visuel (PNG à glisser-déposer)**: `https://comfyanonymous.github.io/ComfyUI_examples/qwen_image/qwen_image_edit_2509_basic_example.png`

### 2.4. Quels custom nodes requis ?

- **Pour l'architecture officielle (`.safetensors`)** : **AUCUN custom node externe n'est requis** pour les fonctionnalités de base (édition, génération). Les nodes `Load Diffusion Model`, `Load CLIP`, `Load VAE` sont tous natifs.
- **Pour les modèles GGUF** : Le node `ComfyUI-GGUF` de `City96` est nécessaire.
- **Pour l'architecture historique (`Diffusers`)** : Le node `ComfyUI-QwenImageWanBridge` était indispensable. **Cette dépendance est désormais éliminée avec l'architecture officielle.**

### 2.5. Structure de répertoires validée ?

La structure de répertoires correcte et simplifiée est celle documentée par Comfy-Org :

```
📂 ComfyUI/
└── 📂 models/
    ├── 📂 diffusion_models/
    │   └── qwen_image_edit_fp8_e4m3fn.safetensors
    ├── 📂 text_encoders/
    │   └── qwen_2.5_vl_7b_fp8_scaled.safetensors
    ├── 📂 vae/
    │   └── qwen_image_vae.safetensors
    └── 📂 loras/
        └── (Optionnel) Qwen-Image-Lightning-4steps-V1.0.safetensors
```

---

## 3. Réconciliation Historique vs. État Actuel

- **Confusion Historique** : Les phases initiales (9 à 12) ont utilisé le modèle `Diffusers` de 54GB avec le custom node `QwenImageWanBridge`. C'était la seule méthode disponible à l'époque.
- **Évolution** : ComfyUI a ensuite intégré un support natif, et `Comfy-Org` a fourni des modèles `.safetensors` optimisés, rendant l'ancienne méthode obsolète.
- **État Actuel (Phase 29)** : Le système a été mis à jour, mais les anciens modèles au format `Diffusers` sont restés, créant un conflit avec les nouveaux workflows natifs.
- **Script `fix-qwen-diffusers-paths.py`** : Ce script était un "pansement" pour tenter de faire fonctionner l'ancien modèle `Diffusers` en créant des liens symboliques pour imiter une structure de fichiers unifiés. C'est une preuve supplémentaire de l'incompatibilité fondamentale.

---

## 4. Procédure d'Installation et Workflow Validés (Cible)

### Étape 1 : Nettoyage de l'Ancienne Architecture

1.  **Supprimer l'ancien modèle Diffusers** :
    ```bash
    rm -rf /path/to/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8
    ```
2.  **Supprimer l'ancien custom node (s'il existe)** :
    ```bash
    rm -rf /path/to/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge
    ```

### Étape 2 : Téléchargement des Modèles Officiels (`.safetensors`)

Utiliser un script Python avec `huggingface_hub` pour télécharger les 3 composants requis depuis `Comfy-Org/Qwen-Image-Edit_ComfyUI` et les placer dans les bons répertoires (`diffusion_models`, `text_encoders`, `vae`).

### Étape 3 : Utilisation du Workflow Natif

1.  Ouvrir ComfyUI.
2.  Glisser-déposer l'image du workflow depuis : `https://comfyanonymous.github.io/ComfyUI_examples/qwen_image/qwen_image_edit_2509_basic_example.png`
3.  Le workflow se charge automatiquement avec les bons nodes natifs.
4.  Sélectionner les modèles téléchargés dans les nodes `Load...`.
5.  Exécuter la génération.

---

## 5. Actions Suivantes Recommandées (ÉTAPE 24F)

1.  **Action de Nettoyage** : Exécuter la suppression de l'ancien modèle `Diffusers` et du custom node `QwenImageWanBridge` pour éviter toute confusion future.
2.  **Action de Déploiement** : Scripter le téléchargement des 3 modèles `.safetensors` officiels depuis `Comfy-Org` vers les répertoires corrects.
3.  **Action de Validation** : Exécuter un test de génération en utilisant le workflow PNG officiel pour confirmer le bon fonctionnement de la nouvelle architecture simplifiée.
4.  **Mise à jour de la Documentation** : Mettre à jour la documentation interne du projet pour refléter cette nouvelle architecture comme étant la seule méthode supportée.