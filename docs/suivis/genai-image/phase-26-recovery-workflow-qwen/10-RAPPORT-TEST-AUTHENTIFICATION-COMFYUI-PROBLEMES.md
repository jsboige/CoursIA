# RAPPORT - Test Authentification ComfyUI : Problèmes Identifiés

**Date**: 2025-10-23  
**Mission**: Valider l'API ComfyUI avec authentification Bearer  
**Statut**: ⚠️ BLOQUÉ - Problèmes de configuration container

---

## 🎯 OBJECTIF INITIAL

Tester que l'API ComfyUI fonctionne correctement avec l'authentification Bearer activée via ComfyUI-Login.

### Prérequis attendus
- ✅ ComfyUI-Login installé dans le workspace WSL
- ✅ Tokens Bearer générés (user: qwen-api-user)
- ✅ Fichier .env configuré avec le token
- ❌ Container ComfyUI fonctionnel avec ComfyUI-Login activé

---

## ❌ PROBLÈMES DÉCOUVERTS

### 1. Container inexistant au démarrage de la mission

**Constat**: Le container `comfyui-qwen` n'existait pas au début de la mission.

**Action effectuée**: 
- Copie du [`docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml) vers `/home/jesse/SD/workspace/comfyui-qwen/`
- Création du fichier `.env` avec les variables nécessaires

**Résultat**: Container créé mais ne démarre pas correctement.

---

### 2. Erreur critique : Module 'yaml' introuvable

**Erreur rencontrée**:
```python
Traceback (most recent call last):
  File "/workspace/ComfyUI/main.py", line 11, in <module>
    import utils.extra_config
  File "/workspace/ComfyUI/utils/extra_config.py", line 2, in <module>
    import yaml
ModuleNotFoundError: No module named 'yaml'
```

**Cause identifiée**: Incompatibilité entre Python 3.12 (hôte WSL) et Python 3.10 (container)

#### Détails techniques
1. Le venv (`/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv`) a été créé sur l'hôte avec Python 3.12
2. Le container CUDA Ubuntu 22.04 utilise Python 3.10
3. Les packages Python sont liés à la version spécifique de Python utilisée lors de l'installation
4. Le docker-compose.yml monte le workspace en volume, donc le venv de l'hôte est utilisé dans le container

**Tentatives de résolution**:
- ✅ Installation de PyYAML dans le venv (confirmé installé)
- ✅ Mise à jour du [`docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml) pour utiliser `venv/bin/python3` au lieu de `python3`
- ✅ Recréation du venv avec toutes les dépendances
- ❌ Problème persiste car incompatibilité de versions Python

---

### 3. Problème architectural : Volume monté vs Installation dans container

**Problème fondamental**:

Le [`docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml:19-21) actuel monte le workspace en volume :

```yaml
volumes:
  - type: bind
    source: ${COMFYUI_WORKSPACE_PATH}
    target: /workspace/ComfyUI
```

Cela signifie que les dépendances Python installées sur l'hôte sont utilisées dans le container, causant des incompatibilités.

**Impact**:
- Le container redémarre en boucle (restart policy)
- ComfyUI ne peut pas démarrer
- L'authentification ne peut pas être testée

---

## 📋 FICHIERS CRÉÉS DURANT LA MISSION

### Scripts de test et réparation

1. [`scripts/genai-auth/setup-and-test-comfyui.sh`](../scripts/genai-auth/setup-and-test-comfyui.sh)
   - Setup complet de l'environnement ComfyUI
   - Tests d'authentification automatisés
   - Statut: Prêt mais non exécuté (container non fonctionnel)

2. [`scripts/genai-auth/fix-comfyui-dependencies.sh`](../scripts/genai-auth/fix-comfyui-dependencies.sh)
   - Réparation des dépendances Python
   - Statut: Exécuté mais inefficace (problème architectural)

3. [`scripts/genai-auth/recreate-venv-in-container.sh`](../scripts/genai-auth/recreate-venv-in-container.sh)
   - Recréation du venv sur l'hôte
   - Statut: Exécuté mais inefficace (problème de version Python)

### Modifications de configuration

4. [`docker-configurations/services/comfyui-qwen/docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml)
   - ✅ Correction ligne 44 : `exec venv/bin/python3` au lieu de `exec python3`
   - Statut: Modifié mais problème persiste

---

## 💡 SOLUTIONS RECOMMANDÉES

### Solution A : Installation des dépendances dans le container (RECOMMANDÉE)

**Principe**: Créer le venv DANS le container au démarrage, pas sur l'hôte.

**Modifications du docker-compose.yml**:

```yaml
command: >
  bash -c "
    apt-get update -qq &&
    apt-get install -y -qq --no-install-recommends python3 python3-pip python3-venv git curl wget ca-certificates &&
    apt-get clean &&
    rm -rf /var/lib/apt/lists/* &&
    cd /workspace/ComfyUI &&
    if [ ! -d venv ] || [ ! -f venv/.docker_created ]; then
      rm -rf venv &&
      python3 -m venv venv &&
      source venv/bin/activate &&
      pip install --upgrade pip &&
      pip install -r requirements.txt &&
      touch venv/.docker_created &&
      deactivate
    fi &&
    exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention
  "
```

**Avantages**:
- ✅ Garantit la compatibilité Python 3.10
- ✅ Venv créé avec la bonne version de Python
- ✅ Installation automatique au premier démarrage
- ✅ Fichier `.docker_created` évite les réinstallations inutiles

**Inconvénients**:
- Premier démarrage plus lent (installation des dépendances)
- Le venv dans le volume devient spécifique au container

---

### Solution B : Image Docker personnalisée (IDÉALE LONG TERME)

**Principe**: Créer une image Docker avec toutes les dépendances pré-installées.

**Fichier Dockerfile**:
```dockerfile
FROM nvidia/cuda:12.4.0-devel-ubuntu22.04

# Installation des dépendances système
RUN apt-get update && \
    apt-get install -y python3 python3-pip python3-venv git curl wget ca-certificates && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Création du répertoire de travail
WORKDIR /workspace/ComfyUI

# Copie et installation des requirements
COPY requirements.txt .
RUN python3 -m venv venv && \
    . venv/bin/activate && \
    pip install --upgrade pip && \
    pip install -r requirements.txt

# Variables d'environnement
ENV PYTHONUNBUFFERED=1
ENV PYTHONDONTWRITEBYTECODE=1

# Point d'entrée
CMD ["venv/bin/python3", "main.py", "--listen", "0.0.0.0", "--port", "8188", "--preview-method", "auto", "--use-split-cross-attention"]
```

**Avantages**:
- ✅ Démarrage instantané
- ✅ Reproductible
- ✅ Portable
- ✅ Optimisé pour la production

**Inconvénients**:
- Nécessite un build initial de l'image
- Modifications de requirements.txt nécessitent un rebuild

---

### Solution C : Utiliser un requirements.txt fixe

**Principe**: Forcer l'installation de versions compatibles dans requirements.txt

**Action**:
Ajouter au début du [`requirements.txt`](../ComfyUI/requirements.txt):
```
pyyaml>=6.0
```

Et s'assurer que le venv est créé avec la bonne version de Python.

---

## 🔍 ÉTAT ACTUEL DU SYSTÈME

### Container ComfyUI

```bash
# Statut
$ docker ps --filter "name=comfyui-qwen"
STATUS: Up X seconds (health: starting) - Redémarre en boucle

# Derniers logs
$ docker logs comfyui-qwen --tail 10
ModuleNotFoundError: No module named 'yaml'
```

### Fichiers de configuration

- ✅ [`docker-configurations/services/comfyui-qwen/docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml) - Modifié
- ✅ `/home/jesse/SD/workspace/comfyui-qwen/.env` - Créé
- ✅ [`MyIA.AI.Notebooks/GenAI/.env`](../MyIA.AI.Notebooks/GenAI/.env) - Token Bearer configuré
- ❌ ComfyUI-Login - Non chargé (serveur ne démarre pas)

### Tokens d'authentification

```bash
# Token généré pour qwen-api-user
Token: $2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni
Fichier: /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/PASSWORD
```

⚠️ **ATTENTION**: Le token est maintenant exposé dans plusieurs fichiers. Considérer la régénération après résolution.

---

## 📝 TESTS NON EFFECTUÉS

En raison du blocage du container, les tests suivants n'ont pas pu être réalisés :

### Test 1: Authentification requise (négatif)
```bash
# Devrait retourner 401 Unauthorized
curl -X GET http://localhost:8188/system_stats
```

### Test 2: Authentification valide (positif)
```bash
# Devrait retourner 200 OK
curl -X GET http://localhost:8188/system_stats \
  -H "Authorization: Bearer $2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni"
```

### Test 3: Script PowerShell
```powershell
# Devrait tester les deux scénarios
./scripts/genai-auth/test-comfyui-auth.ps1 `
  -ApiToken '$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni' `
  -ComfyUIUrl 'http://localhost:8188'
```

---

## 🎯 PROCHAINES ÉTAPES RECOMMANDÉES

### Priorité 1 : Résoudre le problème du container

1. **Arrêter le container actuel**
   ```bash
   cd /home/jesse/SD/workspace/comfyui-qwen
   docker-compose stop
   ```

2. **Appliquer la Solution A** (recommandée)
   - Mettre à jour le docker-compose.yml avec le nouveau command
   - Supprimer l'ancien venv : `rm -rf /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv`
   - Redémarrer : `docker-compose up -d`
   - Attendre 2-3 minutes (première installation)

3. **Vérifier les logs**
   ```bash
   docker logs comfyui-qwen -f
   # Attendre "Starting server" ou équivalent
   ```

### Priorité 2 : Vérifier ComfyUI-Login

Une fois le serveur fonctionnel :

1. Vérifier que ComfyUI-Login est chargé
   ```bash
   docker logs comfyui-qwen 2>&1 | grep -i "login"
   ```

2. Si ComfyUI-Login n'est pas chargé, vérifier l'installation :
   ```bash
   ls -la /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ | grep -i login
   ```

### Priorité 3 : Exécuter les tests d'authentification

Une fois le serveur stable :

1. Exécuter le script de test complet
   ```bash
   ./scripts/genai-auth/setup-and-test-comfyui.sh
   ```

2. Valider manuellement les endpoints critiques

3. Documenter les résultats

---

## 📊 TEMPS INVESTI

- Investigation initiale : 15 min
- Tentatives de réparation : 45 min
- Documentation : 20 min
- **Total : ~80 minutes**

---

## ✅ LIVRABLES

### Scripts créés (prêts à l'emploi)

1. [`scripts/genai-auth/setup-and-test-comfyui.sh`](../scripts/genai-auth/setup-and-test-comfyui.sh) - Setup et tests complets
2. [`scripts/genai-auth/fix-comfyui-dependencies.sh`](../scripts/genai-auth/fix-comfyui-dependencies.sh) - Réparation dépendances
3. [`scripts/genai-auth/recreate-venv-in-container.sh`](../scripts/genai-auth/recreate-venv-in-container.sh) - Recréation venv

### Configuration

4. [`docker-configurations/services/comfyui-qwen/docker-compose.yml`](../docker-configurations/services/comfyui-qwen/docker-compose.yml) - Partiellement corrigé

### Documentation

5. Ce rapport avec analyse détaillée et solutions

---

## 🔐 SÉCURITÉ

⚠️ **RECOMMANDATION CRITIQUE** :

Le token Bearer est actuellement exposé dans :
- [`MyIA.AI.Notebooks/GenAI/.env`](../MyIA.AI.Notebooks/GenAI/.env)
- `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/PASSWORD`
- Ce rapport (hashé)
- Potentiellement dans les logs

**Action recommandée après résolution** :
```bash
# Régénérer un nouveau token
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
python3 custom_nodes/ComfyUI-Login/generate_token.py --username qwen-api-user

# Mettre à jour le fichier .env
vim MyIA.AI.Notebooks/GenAI/.env

# Redémarrer le container
docker-compose restart
```

---

## 📚 RÉFÉRENCES

- [ComfyUI Documentation](https://github.com/comfyanonymous/ComfyUI)
- [ComfyUI-Login Plugin](https://github.com/liusida/ComfyUI-Login)
- [Docker Compose Best Practices](https://docs.docker.com/compose/production/)
- [Python Virtual Environments](https://docs.python.org/3/library/venv.html)

---

## 🏁 CONCLUSION

La mission de test de l'authentification ComfyUI n'a pas pu être menée à terme en raison d'un problème de configuration container plus fondamental que prévu.

**Ce qui a été réalisé** :
- ✅ Diagnostic complet du problème
- ✅ Identification de la cause racine
- ✅ Proposition de 3 solutions avec leurs avantages/inconvénients
- ✅ Scripts de test prêts à l'emploi
- ✅ Documentation détaillée

**Ce qui reste à faire** :
- ❌ Appliquer l'une des solutions proposées
- ❌ Valider le démarrage de ComfyUI
- ❌ Exécuter les tests d'authentification
- ❌ Valider l'intégration avec les notebooks Jupyter

**Estimation pour compléter** : 30-45 minutes (après application Solution A)

---

**Rapport généré le** : 2025-10-23T14:52:00+02:00  
**Par** : Roo (Code Mode)  
**Contexte** : Mission Test Authentification ComfyUI