# Rapport d'Incident Technique - Phase 38 (Validation Z-Image Turbo)

**Date:** 14 Décembre 2025
**Statut:** 🔴 ÉCHEC BLOQUANT
**Composant:** Génération d'Image (Z-Image Turbo / Lumina-Next-SFT)

## Résumé
La validation visuelle de Z-Image Turbo n'a pas pu aboutir. Bien que l'infrastructure (Docker, Authentification, API ComfyUI) soit fonctionnelle, le workflow de génération plante systématiquement lors de l'exécution du modèle avec une erreur de compatibilité de tenseurs (Shapes Mismatch).

## Détails de l'Erreur
Une `RuntimeError` est levée lors de l'inférence dans le module `comfy.ldm.lumina.model`:

```
RuntimeError: Given normalized_shape=[2560], expected input with shape [*, 2560], but got input of size[1, 118, 2304]
```

**Analyse :**
*   **Attendu (2560) :** Dimension attendue par la couche de normalisation du modèle (Lumina-Next-SFT probablement).
*   **Reçu (2304) :** Dimension de l'embedding fourni en entrée. Cette dimension (2304) correspond souvent aux embeddings de modèles type Gemma-2B ou certains encodeurs CLIP spécifiques utilisés par le workflow.
*   **Cause Probable :** Incompatibilité entre le `TextEncodeQwenImageEdit` (qui semble produire du 2304) et le modèle de diffusion `Lumina-Next-SFT` (qui attend du 2560). Le "mariage" des modèles dans ce workflow hybride est incorrect.

## Actions Effectuées
1.  **Vérification Infrastructure :** Conteneur `comfyui-qwen` actif (bien que "unhealthy", il répond aux requêtes API).
2.  **Vérification Auth :** Authentification par Token Bearer validée avec succès.
3.  **Tests de Génération :**
    *   `workflow_z_image_reboot.json` : Échec (RuntimeError).
    *   `workflow_z_image.json` (Fallback) : Échec (RuntimeError identique).
4.  **Outillage :** Création de `scripts/genai-auth/verify_image_content.py` pour validation future.

## Recommandations pour la Phase Suivante (Réparation Modèle)
1.  **Investigation Modèles :** Vérifier les spécifications exactes de `Lumina-Next-SFT`. Si c'est un modèle basé sur SDXL, il attend généralement du CLIP G/L (OpenCLIP). Si c'est une architecture propriétaire, il faut l'encodeur texte correspondant exact.
2.  **Correction Workflow :** Remplacer le nœud d'encodage texte (actuellement lié à Qwen/Gemma) par un encodeur compatible produisant des embeddings de dimension 2560, OU adapter le modèle de diffusion via un adaptateur (si disponible).
3.  **Abandon Temporaire Z-Image :** Si la réparation est trop coûteuse, se concentrer sur l'usage de Qwen2.5-VL pour la *vision* (analyse d'image) qui est la force principale de ce conteneur, et déléguer la génération pure à un service standard (SDXL classique) plutôt que ce montage hybride instable.

## Conclusion
Le système est opérationnel "sur le papier" (les tuyaux sont connectés), mais le "cerveau" (le modèle d'IA assemblé) est incohérent. La validation visuelle est impossible car aucune image n'est produite.