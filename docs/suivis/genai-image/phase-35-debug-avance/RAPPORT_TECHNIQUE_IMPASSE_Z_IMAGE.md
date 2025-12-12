# Rapport Technique Final : Impasse Z-Image GGUF

**Date :** 11 Décembre 2025
**Phase :** 35 (Debug Avancé)
**Statut :** 🛑 Échec Technique (Bloquant) / Clôture
**Auteur :** Roo (Architecte/Orchestrator)

---

## 1. Synthèse Exécutive

L'intégration du modèle **Z-Image-Turbo (GGUF)** dans l'infrastructure ComfyUI existante est **techniquement impossible** en l'état actuel des composants disponibles.
Une incompatibilité fondamentale de dimensions tensorielles entre le modèle de diffusion (qui attend des embeddings de taille **2560**) et les encodeurs Gemma disponibles (qui fournissent **2304** ou **3584**) rend le pipeline inopérant.

**Décision :** Abandon de l'intégration Z-Image pour cette mission.
**Recommandation :** Basculer les efforts sur **Qwen2.5-VL** qui est déjà partiellement intégré et dont l'architecture est maîtrisée.

---

## 2. Analyse Technique de l'Échec

### 2.1 Configuration Testée
*   **Modèle Diffusion :** `z_image_turbo-Q5_K_M.gguf` (Architecture Lumina-2)
*   **Encodeurs Testés :**
    1.  `gemma-3-4b-it` (Expérimental) -> Produit des NaNs/Noirs.
    2.  `gemma-2-2b-it` (Référence théorique) -> Produit une erreur de dimension.
*   **Framework :** ComfyUI avec `City96/ComfyUI-GGUF`.

### 2.2 Diagnostic Précis
Lors de l'injection des embeddings textuels dans le modèle de diffusion (U-Net/DiT), une erreur `RuntimeError` survient :

> `RuntimeError: Given normalized_shape=[2560], expected input with shape [*, 2560], but got input of size[1, 18, 2304]`

Ceci indique que :
1.  **Le modèle Z-Image** attend un vecteur d'entrée de taille **2560**.
2.  **L'encodeur Gemma-2-2B** produit un vecteur de taille **2304**.
3.  Aucune couche de projection (MLP) n'est présente ou active dans le loader GGUF pour faire la transition 2304 -> 2560.

### 2.3 Recherche de Solution
Nous avons tenté de modifier le type de chargement CLIP (`lumina2`, `sd3`, `qwen_image`, `gemma`) sans succès. Le chargeur GGUF ne dispose pas de la logique de mapping nécessaire pour cette variante spécifique de Lumina-2 (qui semble être une version modifiée ou fine-tunée avec une projection non-standard).

---

## 3. Conséquences et Plan de Repli

### 3.1 Impact
*   Z-Image ne peut pas être utilisé comme générateur d'images "léger" dans cette infrastructure.
*   L'investissement temps sur cette piste doit être stoppé pour préserver le budget temps de la mission.

### 3.2 Plan B : Qwen2.5-VL
L'infrastructure `comfyui-qwen` est déjà optimisée pour la famille Qwen.
*   **Action :** Utiliser **Qwen2.5-VL-7B** (ou version GGUF) pour les tâches de génération/édition.
*   **Avantages :** Compatibilité native, pas de problème de dimension CLIP, support VLM complet.

---

## 4. Conclusion
La piste Z-Image GGUF est close. Les ressources (scripts de téléchargement, workflows tests) sont archivées mais désactivées.
L'infrastructure est saine et prête pour d'autres modèles, mais Z-Image requiert des composants spécifiques (custom node dédié ou ré-entraînement) hors périmètre.