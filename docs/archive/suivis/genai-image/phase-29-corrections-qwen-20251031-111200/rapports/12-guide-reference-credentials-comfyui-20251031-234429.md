# 🔐 Guide de Référence - Credentials ComfyUI Qwen

**Date de création** : 2025-10-31  
**Dernière mise à jour** : 2025-10-31 23:42:00  
**Version** : 1.0  
**Auteur** : Roo Code - Mode Documentation

---

## 📋 APERÇU RAPIDE

Ce guide documente la configuration complète des credentials pour l'authentification ComfyUI Qwen.

### ✅ Configuration Finale

| Type | Valeur | Emplacement | Usage |
|---|---|---|---|
| **Token Brut** | `@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf` | `.secrets/.env.generated` | Clients Bearer |
| **Hash bcrypt** | `$2b$12$UDceblhZeE...` | `.secrets/qwen-api-user.token` | Serveur Validation |
| **Docker Env** | `QWEN_API_TOKEN=...` | `docker-configurations/services/comfyui-qwen/.env` | Config Docker |

---

## 🔍 ARCHITECTURE D'AUTHENTIFICATION

```
┌─────────────────┐
│  Client Python  │
│                 │
│  Token Brut:    │
│  @TKEoMzUx...   │──┐
└─────────────────┘  │
                     │
                     │ Authorization: Bearer @TKEoMzUx...
                     │
                     ▼
┌─────────────────────────────────────┐
│     Serveur ComfyUI (Docker)        │
│                                     │
│  1. Reçoit: Bearer @TKEoMzUx...    │
│  2. Hash avec bcrypt                │
│  3. Compare avec:                   │
│     $2b$12$UDceblhZeE...           │
│                                     │
│  Fichier: qwen-api-user.token       │
└─────────────────────────────────────┘
```

---

## 📁 STRUCTURE DES FICHIERS

### 1. Token Brut Client

**Fichier** : `.secrets/.env.generated`
```env
QWEN_API_USER_TOKEN=@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf
```

**Caractéristiques** :
- Longueur : 32 caractères
- Format : ASCII imprimable (pas de caractères spéciaux problématiques)
- Générateur : `genai_auth_manager.py`
- Work Factor bcrypt : 12
- ⚠️ **NE JAMAIS COMMITER** dans Git

---

### 2. Hash bcrypt Serveur

**Fichier** : `.secrets/qwen-api-user.token`
```
$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni
```

**Caractéristiques** :
- Format : bcrypt hash
- Work Factor : 12 (rounds)
- Algorithme : bcrypt 2b
- ✅ Peut être commité (hash unidirectionnel)

---

### 3. Configuration Docker

**Fichier** : `docker-configurations/services/comfyui-qwen/.env`
```env
# ComfyUI API Authentication
QWEN_API_TOKEN=@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf
COMFYUI_AUTH_TOKEN_FILE=/workspace/ComfyUI/.secrets/qwen-api-user.token
```

**Fichier** : `docker-configurations/services/comfyui-qwen/docker-compose.yml`
```yaml
environment:
  - COMFYUI_LOGIN_ENABLED=true
  - COMFYUI_AUTH_TOKEN=${QWEN_API_TOKEN}
  - COMFYUI_AUTH_TOKEN_FILE=${COMFYUI_AUTH_TOKEN_FILE}

volumes:
  - type: bind
    source: ../../.secrets/qwen-api-user.token
    target: /workspace/ComfyUI/.secrets/qwen-api-user.token
    read_only: true
```

---

## 💻 UTILISATION DANS LES SCRIPTS

### Script Python Correct

```python
import os
import requests

# Lire le token depuis l'environnement ou fallback
api_key = os.getenv("QWEN_API_USER_TOKEN") or "@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf"

# Authentification Bearer
headers = {
    'Authorization': f'Bearer {api_key}',
    'Content-Type': 'application/json'
}

# Requête API
response = requests.get(
    'http://localhost:8188/system_stats',
    headers=headers,
    timeout=10
)
```

### ❌ Erreur Courante

```python
# INCORRECT: Utilisation du hash bcrypt
api_key = "$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni"
# ❌ Le serveur ne peut pas valider un hash avec un hash !
```

---

## 🔄 RÉGÉNÉRATION DES CREDENTIALS

### Étape 1 : Générer de Nouveaux Credentials

```bash
# Activer l'environnement Python
python scripts/genai-auth/genai_auth_manager.py generate \
    --service comfyui-qwen \
    --username qwen-api-user \
    --output-dir .secrets
```

### Étape 2 : Mettre à Jour Docker

```bash
# Éditer .env
nano docker-configurations/services/comfyui-qwen/.env

# Mettre à jour QWEN_API_TOKEN avec le nouveau token brut
# depuis .secrets/.env.generated
```

### Étape 3 : Redémarrer le Serveur

```bash
cd docker-configurations/services/comfyui-qwen
docker-compose down
docker-compose up -d
```

---

## 🧪 TESTS DE VALIDATION

### Test 1 : Vérifier le Token Brut

```bash
# Afficher le token brut
cat .secrets/.env.generated
# Doit afficher: QWEN_API_USER_TOKEN=@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf
```

### Test 2 : Vérifier le Hash

```bash
# Afficher le hash bcrypt
cat .secrets/qwen-api-user.token
# Doit afficher: $2b$12$UDceblhZeE...
```

### Test 3 : Tester l'Authentification

```bash
# Exporter le token
export QWEN_API_USER_TOKEN="@TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf"

# Lancer le script de validation
python scripts/genai-auth/validation_complete_qwen_system.py
```

### Test 4 : Tester avec curl

```bash
curl -X GET \
  -H "Authorization: Bearer @TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf" \
  -H "Content-Type: application/json" \
  http://localhost:8188/system_stats
```

**Réponse attendue** :
- ✅ HTTP 200 : Authentification réussie
- ❌ HTTP 401 : Token invalide
- ❌ HTTP 403 : Accès refusé

---

## 🔐 SÉCURITÉ

### ✅ Bonnes Pratiques

1. **Token Brut** :
   - ✅ Stocké dans `.secrets/.env.generated`
   - ✅ Ajouté au `.gitignore`
   - ✅ Permissions restrictives (600)
   - ❌ Jamais hardcodé dans les scripts
   - ❌ Jamais commité dans Git

2. **Hash bcrypt** :
   - ✅ Stocké dans `.secrets/qwen-api-user.token`
   - ✅ Peut être commité (hash unidirectionnel)
   - ✅ Work factor 12 (sécurité élevée)
   - ✅ Monté en read-only dans Docker

3. **Variables d'Environnement** :
   - ✅ Chargées depuis `.env` (non commité)
   - ✅ Utilisées dans `docker-compose.yml`
   - ❌ Jamais exposées dans les logs

### 🚨 Alertes de Sécurité

- ⚠️ Le token brut est **sensible** : traiter comme un mot de passe
- ⚠️ Rotation recommandée tous les 90 jours
- ⚠️ Ne jamais partager le token brut par email/chat
- ⚠️ Utiliser des variables d'environnement pour les CI/CD

---

## 📊 MAPPING COMPLET

### Flux d'Authentification

```
Client Python → Lit .secrets/.env.generated → Token Brut
    ↓
Authorization: Bearer @TKEoMzUx...
    ↓
HTTP Request → Serveur ComfyUI
    ↓
Serveur lit .secrets/qwen-api-user.token → Hash bcrypt
    ↓
Validation (hash token reçu vs hash stocké)
    ↓
Réponse HTTP (200/401/403)
```

### Fichiers de Configuration

| Fichier | Contenu | Type | Git |
|---|---|---|---|
| `.secrets/.env.generated` | Token brut | Plain text | ❌ Ignoré |
| `.secrets/qwen-api-user.token` | Hash bcrypt | Bcrypt hash | ✅ Peut commiter |
| `docker-configurations/services/comfyui-qwen/.env` | Variables Docker | Config | ❌ Ignoré |
| `docker-configurations/services/comfyui-qwen/docker-compose.yml` | Config Docker | YAML | ✅ Commité |

---

## 🛠️ DÉPANNAGE

### Problème : Authentification échoue (HTTP 401)

**Diagnostic** :
```bash
# Vérifier le token configuré
echo $QWEN_API_USER_TOKEN

# Vérifier le token dans .env.generated
cat .secrets/.env.generated

# Vérifier les logs Docker
docker logs comfyui-qwen | grep -i auth
```

**Solutions** :
1. Vérifier que le token brut est utilisé (pas le hash)
2. Vérifier que le serveur Docker a accès au fichier token
3. Redémarrer le container Docker
4. Régénérer les credentials si corrompus

### Problème : Token non trouvé

**Diagnostic** :
```bash
# Vérifier l'existence des fichiers
ls -la .secrets/qwen-api-user.token
ls -la .secrets/.env.generated

# Vérifier les permissions
ls -l .secrets/
```

**Solutions** :
1. Régénérer les credentials avec `genai_auth_manager.py`
2. Vérifier les permissions (doit être lisible)
3. Vérifier le chemin dans `docker-compose.yml`

---

## 📌 NOTES IMPORTANTES

1. **Token Brut ≠ Hash bcrypt**
   - Le client envoie le token **brut**
   - Le serveur stocke le **hash bcrypt**
   - Le serveur hash le token reçu et compare avec le hash stocké

2. **Environnement Variables**
   - `QWEN_API_USER_TOKEN` : Token brut (clients)
   - `QWEN_API_TOKEN` : Token brut (Docker)
   - `COMFYUI_AUTH_TOKEN_FILE` : Chemin du fichier hash (Docker)

3. **Docker Volumes**
   - Le fichier token est monté en **read-only**
   - Chemin relatif : `../../.secrets/qwen-api-user.token`
   - Chemin container : `/workspace/ComfyUI/.secrets/qwen-api-user.token`

---

## 🔄 HISTORIQUE DES MODIFICATIONS

| Date | Version | Changements |
|---|---|---|
| 2025-10-31 | 1.0 | Création initiale du guide après diagnostic et correction |

---

**Document maintenu par** : Roo Code  
**Contact** : Voir README.md du projet  
**Dernière révision** : 2025-10-31 23:42:00