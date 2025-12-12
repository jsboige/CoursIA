# Rapport d'Intégration - Phase 33 : Z-Image (Lumina-2)

**Date :** 11 Décembre 2025
**Statut :** ✅ Succès
**Responsable :** Roo

---

## 1. Objectif Atteint
L'intégration technique de Z-Image (Lumina-2) dans l'environnement Docker `comfyui-qwen` est **opérationnelle et validée**. La génération d'image fonctionne de bout en bout.

### Réalisations :
*   **Modèle CLIP :** Téléchargement et intégration de `gemma-3-4b-it-Q4_K_M.gguf` (Unsloth).
*   **Tokenizer :** Téléchargement du `tokenizer.model` externe car l'extraction depuis le GGUF échouait.
*   **Patch ComfyUI-GGUF :** 
    *   Ajout du support de l'architecture `gemma3`.
    *   Correction du mapping des clés (`ffn_norm` -> `post_feedforward_layernorm`) pour une détection correcte du modèle.
    *   Support du chargement d'un tokenizer externe (`tokenizer.model`) en fallback.
*   **Patch ComfyUI Core (`sd.py`) :** 
    *   Correction du calcul de la mémoire VAE pour supporter les latents 4D (image) avec un VAE détecté comme vidéo (WanVAE).
*   **Workflow :**
    *   Utilisation du VAE `qwen_image_vae.safetensors` (qui est un VAE 16 canaux type Wan/Qwen2-VL).
    *   Création et utilisation d'un noeud custom `LatentUnsqueeze` pour adapter la latente image (4D) au VAE vidéo (5D).
*   **Validation :** Génération réussie d'une image de test (`Z-Image-Test_00001_.png`).

## 2. Solutions Techniques Implémentées

### Problème 1 : Text Encoder Gemma 3 manquant et non supporté
*   **Symptôme :** `ValueError: Unexpected text model architecture type in GGUF file: 'gemma3'`.
*   **Solution :**
    1.  Patch de `ComfyUI-GGUF/loader.py` pour ajouter `gemma3` à la liste des architectures et utiliser le mapping `GEMMA_SD_MAP`.
    2.  Téléchargement du fichier `tokenizer.model` depuis le repo Hugging Face `unsloth/gemma-3-4b-it` et placement dans `models/clip/`.
    3.  Patch de `loader.py` pour charger ce fichier externe si présent.

### Problème 2 : Incompatibilité VAE (Image vs Vidéo)
*   **Symptôme :**
    *   `IndexError: tuple index out of range` dans `memory_used_decode` (attend 5 dimensions).
    *   `RuntimeError: Expected 3D (unbatched) or 4D (batched) input to conv2d, but got input of size: [1, 16, 1, 128, 128]` avec `sdxl_vae` (confirmant que Z-Image sort 16 canaux).
    *   `RuntimeError: Given groups=1, ... expected input... to have 16 channels, but got 1 channels` avec `qwen_image_vae` (problème de dimension mal interprétée).
*   **Analyse :** Z-Image produit des latents image (4D, 16 canaux). Le VAE `qwen_image_vae` est un VAE vidéo (5D, 16 canaux).
*   **Solution :**
    1.  Patch de `comfy/sd.py` pour gérer les shapes 4D dans l'estimation mémoire du WanVAE.
    2.  Création d'un noeud `LatentUnsqueeze` (`ComfyUI-ZImage-Fix`) qui transforme `(B, C, H, W)` en `(B, C, 1, H, W)`.

## 3. Workflow Validé
Le workflow final `workflow_z_image.json` contient :
1.  **UnetLoaderGGUF** : `z_image_turbo-Q5_K_M.gguf`.
2.  **CLIPLoaderGGUF** : `gemma-3-4b-it-Q4_K_M.gguf` (type `lumina2`).
3.  **KSampler** : Génère la latente.
4.  **LatentUnsqueeze** : Ajoute la dimension temporelle (T=1).
5.  **VAEDecode** : Utilise `qwen_image_vae.safetensors` pour décoder la latente 5D.
6.  **SaveImage** : Sauvegarde le résultat.

## 4. Prochaines Étapes
*   Intégrer proprement les patchs dans le codebase (via des PRs ou des forks maintenus).
*   Nettoyer les fichiers temporaires et scripts de téléchargement.
*   Documenter l'usage du noeud `LatentUnsqueeze` pour les futurs workflows Z-Image.

## 5. Conclusion
Mission accomplie. Z-Image est fonctionnel.
