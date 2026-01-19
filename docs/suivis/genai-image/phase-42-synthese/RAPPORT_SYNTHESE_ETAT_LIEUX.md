# Rapport de Synthèse & Grounding : État des Lieux Post-Reboot

**Date** : 15 Décembre 2025
**Phase** : 42 (Reboot Sémantique)
**Auteur** : Roo (Architecte)
**Statut** : ✅ VÉRITÉ TERRAIN ÉTABLIE

---

## 1. Objectif & Contexte
Ce document vise à corriger les confusions accumulées concernant les versions des modèles (Qwen3 vs Qwen2), l'architecture des conteneurs et les méthodes d'authentification. Il sert de **base de vérité absolue** pour les prochaines phases de consolidation (Scripts et Documentation).

## 2. La Vérité sur Qwen
**Correction Majeure** : Contrairement à certaines mentions erronées, il n'y a **PAS** de modèle "Qwen3" installé.

*   **Modèle Réel** : Qwen2-VL (Vision-Language).
*   **Fonctionnalité** : Image Edit & Generation.
*   **Implémentation** :
    *   **Native** : Via `comfy_extras/nodes_qwen.py` (Node `TextEncodeQwenImageEdit`).
    *   **Wrapper** : Via custom node `ComfyUI_QwenImageWanBridge` (pour les fonctionnalités étendues Wan/Video).
*   **Preuve Code** :
    *   `docker-configurations/services/comfyui-qwen/workspace/comfy_extras/nodes_qwen.py`
    *   Documentation officielle référencée dans les fichiers JSON de traduction : `https://docs.comfy.org/tutorials/image/qwen/qwen-image-edit`

## 3. Inventaire de l'Infrastructure
L'infrastructure GenAI Image repose sur **deux conteneurs principaux** actifs, se partageant les ressources GPU.

| Service | Conteneur Docker | Moteurs IA Hébergés | Port Externe | GPU ID | Authentification |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **ComfyUI Qwen** | `comfyui-qwen` | 1. **Qwen2-VL** (Edit)<br>2. **Z-Image Turbo** (Lumina-Next) | **8188** | `0` (RTX 3090) | **Hybride** :<br>- Web : User/Pass (`ComfyUI-Login`)<br>- API : Bearer Token (`QWEN_API_TOKEN`) |
| **Forge Turbo** | `forge-turbo` | 1. **SDXL Turbo** (Legacy/Rapide) | **17861** | `1` (RTX 3090) | **Basic** :<br>- Gradio Auth (`--gradio-auth`) |

### Détails Techniques ComfyUI Qwen
*   **Image Docker** : Base Python 3.11 / CUDA 12.4.
*   **Custom Nodes Critiques** :
    *   `ComfyUI-Login` : Sécurisation de l'accès.
    *   `ComfyUI-Lumina-Next-SFT-DiffusersWrapper` : Moteur Z-Image Turbo.
    *   `ComfyUI_QwenImageWanBridge` : Wrapper Qwen.
*   **Volumes** :
    *   `/workspace/ComfyUI/models` -> `shared/models` (Centralisé)
    *   `/workspace/ComfyUI/output` -> `shared/outputs` (Centralisé)

## 4. Correction des Plans Futurs
Sur la base de cet audit, les phases suivantes doivent être ajustées :

*   **Phase 43 (Scripts)** :
    *   Les scripts de validation ne doivent **plus chercher "Qwen3"**.
    *   Ils doivent valider la présence des nœuds `TextEncodeQwenImageEdit` et `LuminaText2ImgPipeline`.
    *   Ils doivent tester l'auth Hybride (Login pour session, Token pour API).

*   **Phase 44 (Documentation)** :
    *   Supprimer toute référence à Qwen3.
    *   Clarifier que "Z-Image" est une fonctionnalité de `comfyui-qwen` et non un conteneur à part.
    *   Documenter explicitement l'usage des ports 8188 (Comfy) vs 17861 (Forge).

---

**Conclusion** : Le brouillard est dissipé. Nous avons une architecture stable à 2 têtes (ComfyUI & Forge) sur 2 GPUs, sécurisée et fonctionnelle.