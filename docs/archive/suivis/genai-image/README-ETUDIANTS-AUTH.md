# 🔐 Guide d'Authentification ComfyUI pour Étudiants

**Date de création**: 24 octobre 2025  
**Version**: 1.0.0  
**Contexte**: Module GenAI - Génération d'Images avec ComfyUI

---

## 📋 Introduction

Ce guide explique comment configurer l'authentification Bearer Token pour accéder aux services ComfyUI du module GenAI. L'authentification est **obligatoire** pour garantir la sécurité et le bon fonctionnement des services partagés.

### Pourquoi l'authentification est-elle requise ?

- **Sécurité** : Protéger l'accès aux ressources GPU coûteuses
- **Traçabilité** : Identifier les utilisations pour le support technique
- **Équité** : Garantir un accès équitable aux ressources pour tous les étudiants
- **Conformité** : Respecter les bonnes pratiques de sécurité des systèmes informatiques

---

## ⚡ Configuration Rapide (5 minutes)

### Étape 1 : Obtenir votre token d'authentification

**Votre token vous sera fourni par votre enseignant** via l'un des canaux suivants :

- 📧 Email personnel
- 💬 Message Teams
- 📝 Document partagé OneDrive/SharePoint
- 🎓 Plateforme pédagogique du cours

⚠️ **IMPORTANT** : **Ne partagez JAMAIS votre token** avec d'autres étudiants. Chaque token est personnel et traçable.

### Étape 2 : Créer le fichier `.env`

1. **Naviguez** vers le répertoire des notebooks GenAI :
   ```
   CoursIA/MyIA.AI.Notebooks/GenAI/
   ```

2. **Copiez** le fichier d'exemple :
   ```bash
   # Windows PowerShell
   Copy-Item .env.example .env
   
   # Linux/macOS/WSL
   cp .env.example .env
   ```

3. **Éditez** le fichier `.env` avec votre éditeur préféré (VS Code, Notepad++, nano, etc.)

4. **Remplacez** `YOUR_TOKEN_HERE` par votre token personnel :
   ```ini
   # Configuration ComfyUI
   COMFYUI_BASE_URL=http://localhost:8188
   COMFYUI_BEARER_TOKEN=votre_token_ici
   ```

5. **Sauvegardez** le fichier

### Étape 3 : Vérifier la configuration

Exécutez le notebook de test :

```
MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb
```

✅ **Si tout fonctionne**, vous verrez :
```
✅ ComfyUI accessible!
📊 Statistiques Système:
   - PyTorch: 2.9.0+cu128
   - ComfyUI: 0.3.64
   ...
```

❌ **Si vous voyez une erreur d'authentification** :
```
❌ ComfyUI non accessible!
   Erreur 401: Authentication required
```
→ Vérifiez que votre token est correct et sans espaces

---

## 🎯 Exemples d'Utilisation

### Exemple 1 : Connexion de base (Python)

```python
from helpers.comfyui_client import create_client

# Le client charge automatiquement le token depuis .env
client = create_client()
print("✅ Connecté à ComfyUI avec authentification")
```

### Exemple 2 : Test manuel avec curl (Débogage)

```bash
# Windows PowerShell
$token = "votre_token_ici"
curl.exe -H "Authorization: Bearer $token" http://localhost:8188/system_stats

# Linux/macOS
curl -H "Authorization: Bearer votre_token_ici" http://localhost:8188/system_stats
```

### Exemple 3 : Génération d'image avec authentification

```python
from helpers.comfyui_client import create_client

# Créer client (token chargé automatiquement)
client = create_client()

# Générer une image
prompt_id = client.generate_text2image(
    prompt="A beautiful sunset over mountains",
    width=512,
    height=512,
    steps=20
)

print(f"✅ Image générée : {prompt_id}")
```

---

## 🔧 Dépannage Fréquent

### Problème 1 : "ModuleNotFoundError: No module named 'dotenv'"

**Cause** : Package `python-dotenv` non installé

**Solution** :
```bash
pip install python-dotenv
```

### Problème 2 : "❌ ComfyUI non accessible - 401 Unauthorized"

**Causes possibles** :

1. **Token manquant ou invalide**
   - ✅ Vérifiez que le fichier `.env` existe
   - ✅ Vérifiez que `COMFYUI_BEARER_TOKEN` est rempli
   - ✅ Vérifiez qu'il n'y a pas d'espaces avant/après le token

2. **Fichier `.env` mal placé**
   - ✅ Le fichier `.env` doit être dans `MyIA.AI.Notebooks/GenAI/`
   - ✅ Pas dans un sous-dossier

3. **Token expiré ou révoqué**
   - ✅ Contactez votre enseignant pour un nouveau token

### Problème 3 : "❌ ComfyUI non accessible - Connection refused"

**Cause** : Service ComfyUI non démarré

**Solution** :
```bash
# Démarrer le container Docker
cd docker-configurations/services/comfyui-qwen
docker-compose up -d

# Vérifier les logs
docker logs --tail 50 comfyui-qwen
```

### Problème 4 : "400 Bad Request" lors de la génération

**Cause** : Workflow incompatible ou modèle non chargé

**Solution** :
1. Vérifiez que le modèle Qwen est chargé dans ComfyUI
2. Consultez les logs du container :
   ```bash
   docker logs --tail 100 comfyui-qwen
   ```
3. Redémarrez le container si nécessaire

---

## 📚 Ressources Complémentaires

### Documentation du Projet

- **Guide d'authentification complet** : `MyIA.AI.Notebooks/GenAI/README-AUTH.md`
- **Guide des APIs** : `docs/genai/api-reference.md`
- **Troubleshooting avancé** : `docs/genai/TROUBLESHOOTING.md`

### Scripts Utiles

- **Test connexion** : `scripts/genai-auth/test-comfyui-auth.ps1`
- **Configuration** : `scripts/genai-auth/configure-comfyui-auth.ps1`

### Notebooks de Référence

1. **00-5-ComfyUI-Local-Test.ipynb** : Test de connexion basique
2. **01-5-Qwen-Image-Edit.ipynb** : Édition d'images avancée
3. **02-1-Image-Generation-Basics.ipynb** : Génération d'images complète

---

## 🆘 Support et Assistance

### En cas de problème persistant

1. **Vérifiez d'abord** ce guide de dépannage
2. **Consultez** le fichier `README-AUTH.md` pour plus de détails techniques
3. **Contactez** votre enseignant avec :
   - Description précise du problème
   - Message d'erreur complet
   - Étapes déjà tentées
   - Capture d'écran si pertinent

### Informations à fournir pour le support

```
- OS : Windows 11 / Linux / macOS
- Python version : 3.10+
- Notebook testé : [nom du notebook]
- Erreur exacte : [message d'erreur complet]
- Token utilisé : [3 premiers caractères seulement, ex: $2b...]
```

---

## 🔒 Bonnes Pratiques de Sécurité

### À FAIRE ✅

- ✅ Conserver votre token dans le fichier `.env` uniquement
- ✅ Vérifier que `.env` est dans `.gitignore` (déjà configuré)
- ✅ Signaler immédiatement tout token compromis
- ✅ Ne jamais commiter le fichier `.env` dans Git

### À NE PAS FAIRE ❌

- ❌ Ne jamais partager votre token avec d'autres étudiants
- ❌ Ne jamais publier votre token sur GitHub, Discord, etc.
- ❌ Ne jamais coder le token en dur dans vos notebooks
- ❌ Ne jamais envoyer votre token par email/Teams non chiffré

---

## 📝 Changelog

### Version 1.0.0 (2025-10-24)

- ✅ Guide initial pour étudiants
- ✅ Configuration rapide en 3 étapes
- ✅ Exemples d'utilisation complets
- ✅ Dépannage des problèmes courants
- ✅ Bonnes pratiques de sécurité

---

**Dernière mise à jour** : 24 octobre 2025  
**Auteur** : Équipe pédagogique GenAI  
**Contact** : [Votre enseignant]