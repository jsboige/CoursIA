# 🔐 Guide d'Authentification ComfyUI pour Notebooks GenAI

## Vue d'ensemble

Ce guide explique comment configurer l'authentification Bearer pour les notebooks GenAI qui communiquent avec un serveur ComfyUI sécurisé via **ComfyUI-Login**.

## 🎯 Contexte

Les notebooks GenAI utilisent maintenant une **authentification optionnelle** (graceful degradation) :
- ✅ **Avec token** : Connexion sécurisée aux serveurs ComfyUI protégés
- ⚠️ **Sans token** : Fonctionne uniquement avec serveurs ComfyUI non sécurisés

## 📋 Prérequis

- Un serveur ComfyUI avec **ComfyUI-Login** installé
- Accès aux scripts d'authentification dans `scripts/genai-auth/`
- Python avec `python-dotenv` installé

## 🚀 Configuration Rapide

### Étape 1 : Générer votre token Bearer

Utilisez le script PowerShell fourni pour extraire votre token :

```powershell
# Depuis la racine du projet
.\scripts\genai-auth\extract-bearer-tokens.ps1
```

Le script vous guidera pour :
1. Vous connecter au serveur ComfyUI
2. Extraire automatiquement votre token Bearer
3. Sauvegarder le token de manière sécurisée

### Étape 2 : Créer le fichier .env

1. Copiez le fichier d'exemple :
```bash
cd MyIA.AI.Notebooks/GenAI
cp .env.example .env
```

2. Éditez `.env` et ajoutez votre token :
```bash
COMFYUI_API_TOKEN=votre_token_bearer_ici
```

### Étape 3 : Vérifier la configuration

Lancez un notebook qui utilise ComfyUI, par exemple :
- `00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb`
- `01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb`

Vous devriez voir :
```
✅ Configuration chargée
🔐 Token: eyJhbGciOiJIUz...xxxxx
✓ Authentification configurée
```

## 📚 Notebooks Modifiés

Les notebooks suivants supportent maintenant l'authentification Bearer :

### 1. **00-5-ComfyUI-Local-Test.ipynb**
- **Localisation** : `00-GenAI-Environment/`
- **Utilise** : Helper `comfyui_client.py`
- **Auth** : Automatique via helper

### 2. **01-5-Qwen-Image-Edit.ipynb**
- **Localisation** : `01-Images-Foundation/`
- **Utilise** : Client ComfyUI intégré
- **Auth** : Configuration manuelle dans cellule 1

## 🛠️ Architecture Technique

### Helper comfyui_client.py

Le helper partagé a été mis à jour pour supporter l'authentification :

```python
from helpers.comfyui_client import create_client, ComfyUIConfig

# Le client charge automatiquement COMFYUI_API_TOKEN depuis .env
client = create_client()  

# Ou configuration manuelle
config = ComfyUIConfig(
    base_url="http://localhost:8188",
    auth_token="votre_token_ici"  # Optionnel
)
client = ComfyUIClient(config)
```

### Graceful Degradation

Tous les notebooks fonctionnent en mode dégradé si aucun token n'est fourni :

```python
# Avec token
✓ Authentification configurée
→ Connexion sécurisée au serveur

# Sans token
⚠️  Aucun token - connexion sans authentification
→ Fonctionne uniquement si serveur non sécurisé
```

## 🔒 Sécurité

### Bonnes Pratiques

1. **Ne JAMAIS commiter le fichier `.env`**
   - Le `.gitignore` inclut automatiquement `*.env`
   - Utilisez toujours `.env.example` pour la documentation

2. **Rotation des tokens**
   - Régénérez vos tokens périodiquement
   - Révoquez les anciens tokens via l'interface ComfyUI-Login

3. **Permissions minimales**
   - Chaque token a des permissions spécifiques
   - Utilisez des tokens distincts pour développement/production

### Variables d'Environnement

| Variable | Description | Requis |
|----------|-------------|---------|
| `COMFYUI_API_TOKEN` | Token Bearer d'authentification | Optionnel* |

*Requis uniquement pour serveurs sécurisés

## 🐛 Dépannage

### Erreur : "COMFYUI_API_TOKEN non trouvé"

**Symptôme** :
```
⚠️  COMFYUI_API_TOKEN non trouvé - connexion sans authentification
```

**Solution** :
1. Vérifiez que le fichier `.env` existe dans `MyIA.AI.Notebooks/GenAI/`
2. Vérifiez le format : `COMFYUI_API_TOKEN=votre_token`
3. Pas d'espaces autour du `=`
4. Redémarrez le kernel Jupyter

### Erreur : 401 Unauthorized

**Symptôme** :
```
❌ ComfyUI status code: 401
```

**Solutions** :
1. Token expiré → Régénérez avec `extract-bearer-tokens.ps1`
2. Token invalide → Vérifiez copier-coller (pas d'espaces)
3. Token révoqué → Reconnectez-vous et obtenez un nouveau token

### Erreur : Connection Refused

**Symptôme** :
```
❌ Connexion échouée: Connection refused
```

**Solutions** :
1. Vérifiez que ComfyUI est démarré : `docker-compose up -d comfyui-qwen`
2. Vérifiez le port : `http://localhost:8188` (local) ou URL serveur
3. Testez la connexion : `curl http://localhost:8188/system_stats`

## 📖 Ressources Complémentaires

### Scripts d'Authentification

Tous les scripts sont dans `scripts/genai-auth/` :

- `extract-bearer-tokens.ps1` - Extraction automatique des tokens
- `test-comfyui-auth.ps1` - Test de connexion authentifiée
- `configure-comfyui-auth.ps1` - Configuration du serveur
- `deploy-auth-solution.ps1` - Déploiement complet

### Documentation Serveur

- **ComfyUI-Login** : [GitHub Repository](https://github.com/IDGallagher/ComfyUI-Login)
- **Architecture GenAI** : `docs/genai/architecture.md`
- **Guide Déploiement** : `docs/genai/deployment-guide.md`

## ✅ Checklist de Vérification

Avant d'exécuter un notebook :

- [ ] Fichier `.env` créé et configuré
- [ ] Token `COMFYUI_API_TOKEN` valide
- [ ] Serveur ComfyUI accessible (local ou distant)
- [ ] Kernel Jupyter redémarré après modification `.env`
- [ ] Message "✓ Authentification configurée" visible

## 🆘 Support

En cas de problème :

1. Consultez `TROUBLESHOOTING.md` dans ce répertoire
2. Vérifiez les logs du serveur ComfyUI
3. Testez avec `scripts/genai-auth/test-comfyui-auth.ps1`
4. Contactez l'équipe infrastructure GenAI

---

**Dernière mise à jour** : 2025-10-22  
**Version** : 1.0.0  
**Auteur** : Équipe CoursIA GenAI