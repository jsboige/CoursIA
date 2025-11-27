# Archive Docker Configurations - 2025-11-25

Ce répertoire contient les configurations Docker obsolètes archivées lors du nettoyage du 25 novembre 2025.

## Contenu de l'archive

### Configurations complètes archivées
- `_legacy-root-configs/` : Anciennes configurations racines obsolètes
- `flux-1-dev/` : Configuration FLUX.1-dev incomplète/non fonctionnelle
- `stable-diffusion-35/` : Configuration Stable Diffusion 3.5 incomplète/non fonctionnelle
- `comfyui-workflows/` : Configuration workflows vide/non fonctionnelle

### Fichiers de configuration archivés
- `docker-compose.yml.obsolete` : Ancien docker-compose.yml multi-services obsolète
- `docker-compose-no-auth.yml` : Version sans authentification de comfyui-qwen
- `docker-compose.yml.backup-*` : Fichiers de backup obsolètes
- `.env.backup-*` : Fichiers de backup d'environnement obsolètes

## Raison de l'archivage

Ces configurations ont été archivées car :
1. **Obsolètes** : Remplacées par l'architecture consolidée comfyui-qwen
2. **Incomplètes** : Ne contenaient que des fichiers README/config sans implémentation
3. **Non fonctionnelles** : N'étaient pas intégrées avec les scripts genai-auth consolidés
4. **En double** : Multiples versions de docker-compose.yml pour le même service

## Configuration conservée

La configuration active et maintenue est :
- `../comfyui-qwen/` : Configuration principale ComfyUI + Qwen avec authentification

## Intégration avec scripts genai-auth

L'architecture consolidée utilise :
- Scripts : `../scripts/genai-auth/` (Phase 29 consolidée)
- Configuration : `../comfyui-qwen/` (authentification ComfyUI-Login)
- Modèles : `../models/` (partagé)
- Cache : `../cache/` (partagé)

---

**Date d'archivage** : 2025-11-25  
**Raison** : Nettoyage et organisation en cohérence avec scripts genai-auth consolidés  
**Statut** : Archive - Ne pas utiliser pour les nouveaux déploiements