# 🔐 Activation Authentification API ComfyUI Qwen - Instructions Étudiants

**Date**: 2025-10-21  
**Service concerné**: API Qwen Image Edit  
**Statut**: ✅ Authentification activée (Phase 23C)

---

## 📋 Résumé

L'API ComfyUI Qwen est maintenant protégée par authentification pour garantir la sécurité et la disponibilité du service GPU. Vous devez configurer votre token d'accès avant d'utiliser les notebooks.

---

## 🎫 Obtention de Votre Token d'Accès

### Méthode 1: Via l'Interface Web (Recommandée)

1. **Accédez à l'interface de login** : https://qwen-image-edit.myia.io/login
2. **Connectez-vous avec les credentials** :
   - **Username**: `etudiant`
   - **Password**: `CourIA2025!`
3. **Copiez votre token** affiché sur la page après connexion
4. **Conservez-le précieusement** dans votre fichier `.env`

### Méthode 2: Fourni par l'Enseignant

Si la méthode 1 ne fonctionne pas, contactez votre enseignant qui vous fournira directement votre token personnel.

---

## ⚙️ Configuration Rapide (3 Étapes)

### Étape 1: Créer le Fichier `.env`

Ouvrez un terminal dans le répertoire des notebooks :

```bash
cd MyIA.AI.Notebooks/GenAI/01-Images-Foundation/
cp .env.example .env
```

### Étape 2: Éditer le Fichier `.env`

Ouvrez le fichier `.env` avec votre éditeur préféré et remplacez `your_token_here` par votre token réel :

```env
QWEN_API_TOKEN=VOTRE_TOKEN_COPIE_ICI
```

**Exemple** :
```env
QWEN_API_TOKEN=$2b$12$N9qo8uLOickgx2ZMRZoMyeIjZAgcfl7p92ldGxad68LJZdL17lhWy
```

### Étape 3: Exécuter les Notebooks

Les notebooks chargeront automatiquement votre token depuis `.env`. Exécutez simplement les cellules comme d'habitude !

```python
# Cette cellule charge automatiquement le token
from dotenv import load_dotenv
import os

load_dotenv()
QWEN_API_TOKEN = os.getenv("QWEN_API_TOKEN")
```

---

## 🚨 Règles de Sécurité Importantes

### ❌ NE JAMAIS Faire

- ❌ **Partager votre token** avec d'autres étudiants
- ❌ **Commiter le fichier `.env`** dans Git (déjà protégé par `.gitignore`)
- ❌ **Copier-coller le token** dans des forums ou chats publics
- ❌ **Hardcoder le token** directement dans le code des notebooks

### ✅ TOUJOURS Faire

- ✅ **Utiliser le fichier `.env`** pour stocker votre token localement
- ✅ **Vérifier que `.env` est dans `.gitignore`** avant tout commit
- ✅ **Contacter l'enseignant** en cas de perte ou compromission du token
- ✅ **Suivre les instructions** du fichier `.env.example`

---

## 🛠️ Dépannage

### Erreur: `QWEN_API_TOKEN non trouvé`

**Cause**: Le fichier `.env` n'existe pas ou est mal configuré.

**Solution**:
1. Vérifier que le fichier `.env` existe dans `MyIA.AI.Notebooks/GenAI/01-Images-Foundation/`
2. Vérifier que la ligne `QWEN_API_TOKEN=...` est présente
3. Vérifier qu'il n'y a **pas d'espace** avant ou après le token

### Erreur: `401 Unauthorized`

**Cause**: Le token est invalide, expiré ou mal copié.

**Solution**:
1. Vérifier que vous avez copié le token **complet** (aucun caractère manquant)
2. Vérifier qu'il n'y a **pas d'espace ou de retour à la ligne** dans le token
3. Régénérer un nouveau token via https://qwen-image-edit.myia.io/login
4. Si le problème persiste, contacter l'enseignant

### Erreur: `python-dotenv` not found

**Cause**: Le package `python-dotenv` n'est pas installé.

**Solution**:
```bash
pip install python-dotenv
```

---

## 📚 Notebooks Concernés

### ✅ API Qwen (Authentification Requise)

**Notebook** : [`01-5-Qwen-Image-Edit.ipynb`](../../../MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb)

- 🔐 **Requiert authentification** via token Bearer
- 🎨 **Capacités** : Édition d'images avancée, workflows ComfyUI personnalisés
- ⚡ **Performance** : ~14s pour génération 512×512
- 📖 **Guide** : Voir [GUIDE-APIS-ETUDIANTS.md](../GUIDE-APIS-ETUDIANTS.md#-qwen-image-edit-comfyui-api)

### ✅ API Forge (Accès Public)

**Notebook** : [`01-4-Forge-SD-XL-Turbo.ipynb`](../../../MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb)

- 🌐 **Accès public** : Aucune authentification requise
- 🚀 **Capacités** : Génération rapide text-to-image (SD XL Turbo)
- ⚡ **Performance** : ~18s pour génération 512×512
- 📖 **Guide** : Voir [GUIDE-APIS-ETUDIANTS.md](../GUIDE-APIS-ETUDIANTS.md#-forge-sd-xl-turbo)

---

## 💡 Ressources Complémentaires

- **Guide complet des APIs** : [`docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md`](../GUIDE-APIS-ETUDIANTS.md)
- **Rapport technique Phase 23C** : [`2025-10-21_RAPPORT-ACTIVATION-AUTH-COMFYUI.md`](2025-10-21_RAPPORT-ACTIVATION-AUTH-COMFYUI.md)
- **Documentation python-dotenv** : https://pypi.org/project/python-dotenv/

---

## 📞 Support

### Contact Enseignant

En cas de problème avec votre token ou l'authentification :
- **Email** : [À compléter par l'enseignant]
- **Forum cours** : [À compléter par l'enseignant]

### Auto-Diagnostic

Avant de contacter le support, vérifiez :
1. ✅ Le fichier `.env` existe et contient `QWEN_API_TOKEN=...`
2. ✅ Le package `python-dotenv` est installé (`pip list | grep dotenv`)
3. ✅ Le token est copié **exactement** (aucun espace, aucun retour à la ligne)
4. ✅ L'API est accessible : https://qwen-image-edit.myia.io

---

**Bon développement !** 🎨🚀

---

*Document généré automatiquement - Phase 23C - 2025-10-21*