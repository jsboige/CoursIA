# Stratégie de Résolution : Problème d'Inférence Z-Image (Images Noires/NaN)

**Date :** 11 Décembre 2025
**Auteur :** Roo (Architecte)
**Contexte :** Phase 35 - Debug Avancé
**Cible :** `comfyui-qwen` / Modèle `Z-Image-Turbo-GGUF`

---

## 1. Diagnostic du Problème

L'intégration technique de Z-Image (Lumina-2) dans `comfyui-qwen` est fonctionnelle (chargement des modèles OK), mais le pipeline de génération produit systématiquement des images noires ou remplies de valeurs `NaN` (Not a Number).

### 1.1 Symptômes
*   Le workflow s'exécute sans erreur Python fatale.
*   L'image de sortie est valide en dimensions (1024x1024) mais totalement vide/noire.
*   Le modèle Latent contient probablement des NaNs dès les premières étapes du Denoising.

### 1.2 Analyse Causale (Hypothèses)

1.  **Hypothèse A (Principale) : Incompatibilité de l'Encodeur Texte**
    *   **Configuration Actuelle :** Utilisation de `gemma-3-4b-it-Q4_K_M.gguf`.
    *   **Problème :** Lumina-2 est nativement entraîné avec **Gemma-2-2B**. L'architecture Gemma-3 (plus récente) peut avoir des dimensions d'embeddings ou une structure d'attention différente que le node `CLIPLoaderGGUF` (type `lumina2`) ne gère pas correctement, produisant des conditionnements corrompus.
    *   **Probabilité :** Élevée (90%).

2.  **Hypothèse B : Problème de Précision (BF16 vs FP16)**
    *   **Problème :** Les modèles GGUF récents (notamment Gemma) peuvent être sensibles à la précision lors du déquantization "on-the-fly". Si le calcul se fait en FP16 sur une opération qui nécessite BF16 (ou inversement) et que les valeurs explosent (overflow), cela génère des NaNs.
    *   **Probabilité :** Moyenne (surtout si Gemma-3 est utilisé).

3.  **Hypothèse C : Incompatibilité du VAE**
    *   **Configuration Actuelle :** `qwen_image_vae.safetensors`.
    *   **Problème :** Bien que peu probable pour des NaNs (produirait plutôt du bruit coloré), un VAE incompatible avec les latents Lumina-2 pourrait échouer au décodage.

---

## 2. Plan de Résolution

Nous allons tester séquentiellement 3 solutions, de la plus probable à la plus radicale.

### 2.1 Solution 1 : Retour au Standard (Gemma-2-2B) - **PRIORITAIRE**
Remplacer l'encodeur expérimental Gemma-3 par l'encodeur de référence pour Lumina-2.

*   **Action :** Télécharger `gemma-2-2b-it-Q4_K_M.gguf` (ou Q6_K).
*   **Justification :** C'est la recommandation officielle pour Lumina-2.
*   **Implémentation :** Script de téléchargement `scripts/genai-auth/download_gemma2_ref.py`.

### 2.2 Solution 2 : Forçage de Précision (FP32)
Si Gemma-2 échoue aussi, forcer le calcul en FP32 pour éviter les instabilités numériques.

*   **Action :** Utiliser les arguments de lancement ComfyUI `--force-fp32` ou `--force-fp16` (selon le cas) pour voir si cela stabilise le calcul.
*   **Alternative :** Vérifier s'il existe une version GGUF "f32" de l'encodeur (trop lourd, peu probable).

### 2.3 Solution 3 : Pivot vers Qwen2.5-VL (Plan B)
Si Z-Image reste inutilisable, abandonner l'architecture Lumina-2 pour cette phase et utiliser les capacités de génération de Qwen2.5-VL (si disponibles via `ComfyUI-Qwen-VL-Chat` ou équivalent).

*   **Action :** Reconfigurer le workflow pour utiliser le pipeline natif Qwen2.5-VL pour la génération (si le modèle supporte le text-to-image, ce qui est à confirmer pour la version VL).
*   **Note :** Qwen2-VL est principalement un modèle VLM (Image-to-Text), ses capacités de génération (Text-to-Image) sont limitées ou inexistantes sans adaptateur spécifique. Cette option est donc risquée.

---

## 3. Protocole de Test (Phase 35)

1.  **Setup :**
    *   S'assurer que `comfyui-qwen` est UP.
    *   Vérifier la présence de `z_image_turbo-Q5_K_M.gguf`.

2.  **Test A (Gemma-2-2B) :**
    *   Télécharger Gemma-2-2B.
    *   Modifier `workflow_z_image.json` pour pointer vers ce modèle.
    *   Lancer la génération.
    *   *Succès si :* Image cohérente générée.

3.  **Test B (Gemma-2-9B) :**
    *   Si Test A échoue (image floue/mauvaise), tester avec Gemma-2-9B (plus puissant, peut-être requis par Z-Image Turbo).

---

## 4. Conclusion
L'erreur est presque certainement l'utilisation de **Gemma-3** au lieu de **Gemma-2**. La correction de cet encodeur devrait résoudre le problème des images noires.