# Rapport d'Étude - Phase 32 : Intégration Z-Image (Turbo GGUF)

**Date :** 10 Décembre 2025
**Statut :** ✅ Validé
**Cible :** `jayn7/Z-Image-Turbo-GGUF`
**Stratégie :** Extension du service `comfyui-qwen`

---

## 1. Objectif
Intégrer le modèle "Z-Image-Turbo" (format GGUF) dans l'infrastructure Docker existante pour permettre une génération d'images haute performance avec une empreinte VRAM réduite, sans multiplier les conteneurs.

## 2. Analyse du Modèle (Z-Image-Turbo)

### 2.1 Identité
- **Nom :** Z-Image-Turbo-GGUF
- **Auteur :** jayn7
- **Format :** GGUF (Quantized)
- **Architecture de base :** **Lumina2** (Base model: `Tongyi-MAI/Z-Image-Turbo`)
- **Dépendance Critique :** Nécessite un encodeur de texte externe **Qwen2-VL** ou **Qwen3-4B-GGUF** (à valider lors du POC).

### 2.2 Paramètres Recommandés
- **Steps :** 9 (correspondant à 8 DiT forwards)
- **CFG Scale :** 0.0 (Turbo model)
- **Sampler :** Euler / Standard
- **Résolution optimale :** 1024x1024
- **Dtype :** `bfloat16` (ou `float16` selon support GPU)

---

## 3. Architecture Technique Validée

### 3.1 Stratégie d'Intégration : "Extension Unifiée"
Nous avons choisi d'étendre le conteneur de production existant `comfyui-qwen` plutôt que de créer un nouveau service.

*   **Justification :**
    *   **Ressources :** Évite de réserver de la VRAM pour un deuxième conteneur "dormant".
    *   **Maintenance :** Un seul environnement Python/CUDA à maintenir.
    *   **Interopérabilité :** Permet de mixer des workflows Qwen et Z-Image (ex: Image-to-Image avec Qwen puis Upscale/Refine avec Z-Image).

### 3.2 Configuration Docker (ComfyUI-Qwen)
*   **Validation Infrastructure :** L'analyse du `docker-compose.yml` confirme que le volume `/workspace/ComfyUI` est persistant (bind mount vers `./workspace`). L'installation des custom nodes sera donc conservée sans modification du fichier Compose.
*   **Image Base :** `python:3.11` (Runtime installation)
*   **GPU :** RTX 3090 (Primary)
*   **Custom Nodes Requis :**
    *   `city96/ComfyUI-GGUF` : Support GGUF générique (incluant Lumina2).
*   **Dépendances Python :**
    *   `llama-cpp-python` (sera installé automatiquement par le custom node ou manuellement si échec de compilation).
    *   `huggingface_hub` (déjà présent).

### 3.3 Gestion des Modèles (Volumes Partagés)
Les modèles seront stockés dans le volume partagé `shared/models` pour être accessibles par tous les services :

1.  **Modèle Principal (UNET/Diffusion) :**
    *   Source : `jayn7/Z-Image-Turbo-GGUF`
    *   Fichier : `z_image_turbo-Q5_K_M.gguf` (~5.5 GB)
    *   Destination : `shared/models/unet/` (ou `diffusion_models` selon le node)

2.  **Encodeur Texte (CLIP/LLM) :**
    *   Source : `unsloth/Qwen3-4B-GGUF` (ou équivalent recommandé)
    *   Destination : `shared/models/clip/`

---

## 4. Plan d'Action - Phase 33 (Implémentation)

Cette phase se déroulera en mode **Code** et **Debug**.

### Étape 1 : Préparation & Backup
- [ ] Snapshot de l'état actuel (si possible) ou vérification des backups `.secrets`.
- [ ] Vérification de l'espace disque disponible pour les modèles (~10GB).

### Étape 2 : Installation des Dépendances (POC)
- [ ] Démarrer `comfyui-qwen`.
- [ ] Installer `city96/ComfyUI-GGUF` via `git clone` dans `custom_nodes`.
- [ ] **Point Critique :** Vérifier la compilation de `llama-cpp-python` dans les logs du conteneur.
    - *Si échec :* Tenter installation manuelle via `pip install llama-cpp-python --extra-index-url ...` avec les flags CUDA corrects.

### Étape 3 : Téléchargement des Modèles
- [ ] Utiliser un script Python temporaire ou `huggingface-cli` pour télécharger les fichiers GGUF directement dans les bons dossiers `shared/models`.

### Étape 4 : Création du Workflow de Test
- [ ] Créer un workflow minimal JSON : `Load GGUF Model` -> `Load GGUF Clip` -> `Sampler` -> `Decode`.
- [ ] Tester la génération d'une image 1024x1024.

### Étape 5 : Benchmark & Validation
- [ ] Mesurer la VRAM Peak (via `nvidia-smi` pendant la génération).
- [ ] Mesurer le temps de génération (it/s).
- [ ] Comparer avec Qwen (qualitatif).

### Étape 6 : Documentation
- [ ] Mettre à jour `user-guide.md` avec le nouveau modèle disponible.
- [ ] Archiver le rapport de Phase 33.

---

*Rapport validé par l'Architecte Roo.*
