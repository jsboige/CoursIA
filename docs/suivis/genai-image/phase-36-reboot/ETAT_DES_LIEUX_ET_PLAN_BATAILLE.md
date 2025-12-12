# Phase 36 : État des Lieux et Plan de Bataille Z-Image (Reboot)

## 1. Contexte et Objectifs

Suite aux échecs d'intégration de Z-Image (Lumina-2) en Phase 33-35 (images noires, instabilité), nous avons opéré un "Grand Nettoyage" et une analyse sémantique approfondie pour repartir sur des bases saines.

**Objectif Final** : Faire fonctionner Z-Image Turbo (GGUF) dans l'écosystème ComfyUI existant (`comfyui-qwen`), avec une consommation VRAM optimisée et des résultats cohérents.

## 2. Actions Réalisées (Phase 36)

### 2.1 Nettoyage du Dépôt
*   Suppression des artefacts de tests jetables (`run_z_image_test.py`, scripts PowerShell temporaires).
*   Suppression du dossier `output_z_image/` contenant les échecs (images noires).
*   **Consolidation** :
    *   `validate_all_models.py` -> `scripts/genai-auth/utils/validate_genai_stack.py` (Outil de référence pour validation E2E).
    *   `verify_image_content.py` -> `scripts/genai-auth/utils/verify_image_content.py` (Outil d'analyse d'image pour détection automatique d'échecs).
*   Mise à jour du `.gitignore` pour exclure `models/`, `output_z_image/` et les logs.

### 2.2 Grounding Sémantique (Interne)
*   **Configuration Docker** : `comfyui-qwen` est configuré avec des volumes partagés pour les modèles (`../../shared/models`).
    *   Tout nouveau modèle (GGUF, VAE, CLIP) doit être placé dans ce répertoire partagé pour être visible par le conteneur.
    *   L'image Docker installe `pyyaml>=6.0`, essentiel pour les Custom Nodes.

### 2.3 Analyse de l'Échec "Images Noires" (Externe & Logs)
*   **Symptôme** : Images noires ou bruit noir.
*   **Erreur Log (Retrouvée)** : `RuntimeError: Given normalized_shape=[2560], expected input with shape [*, 2560], but got input of size [*, 2304]`.
*   **Interprétation** : Incompatibilité de dimension entre le Text Encoder utilisé et ce qu'attend le modèle Z-Image.
    *   Gemma-2-2B (utilisé précédemment) a une dimension de **2304**.
    *   Le modèle (ou le nœud Lumina-2) attend une dimension de **2560**.
*   **Pistes de Solution** :
    *   Certains workflows GGUF recommandent **Qwen2-VL** ou d'autres encodeurs.
    *   D'autres mentionnent une incompatibilité "Flash Attention" sur certaines cartes.
    *   **Hypothèse Principale** : Mauvais choix de Text Encoder ou mauvaise configuration du loader GGUF qui n'applique pas la projection correcte.

## 3. Plan de Bataille (Phase 37)

### Étape 1 : Préparation des Ressources ("Supply Drop")
1.  **Télécharger les Bons Modèles** (dans `docker-configurations/shared/models/`):
    *   **Unet** : `z_image_turbo-Q5_K_M.gguf` (Déjà présent ? À vérifier).
    *   **VAE** : `qwen_image_vae.safetensors` (Déjà présent, validé).
    *   **Text Encoder** : Télécharger les candidats probables pour résoudre le mismatch 2304 vs 2560.
        *   *Candidat A* : Gemma-2-2B-IT GGUF (Classic).
        *   *Candidat B* : Qwen2-VL GGUF (Mentionné dans certains guides).
        *   *Candidat C* : Un Text Encoder spécifique "Lumina-2" si disponible.

### Étape 2 : Configuration du Workflow (Correction)
1.  Créer un nouveau workflow JSON (`workflow_z_image_v2.json`) basé sur le "Simple Z-Image-Turbo GGUF Workflow" de Civitai (référence solide).
2.  S'assurer d'utiliser le Custom Node `ComfyUI-GGUF` à jour.

### Étape 3 : Test Isolé (Génération)
1.  Lancer un test avec `validate_genai_stack.py` modifié pour utiliser le nouveau workflow.
2.  Utiliser `verify_image_content.py` pour valider immédiatement si l'image est noire ou valide.

### Étape 4 : Validation Finale
1.  Si succès : Documenter la combinaison exacte (Unet + VAE + Text Encoder) dans `docs/genai/models_reference.md`.
2.  Si échec : Analyser les logs pour "Flash Attention" errors.

## 4. Recommandations Techniques
*   **Ne pas modifier le Dockerfile** pour l'instant. L'environnement Python 3.11 actuel est suffisant.
*   **Volumes** : Toujours passer par `../../shared/models`.
*   **Logs** : Surveiller `docker logs comfyui-qwen` en temps réel lors des tests.