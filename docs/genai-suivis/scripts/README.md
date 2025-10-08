# Scripts de Test - Infrastructure Docker GenAI

Scripts de test progressifs pour valider l'infrastructure Docker des services GenAI.

## 📁 Structure

| Script | Service | GPU | Taille DL | Durée |
|--------|---------|-----|-----------|-------|
| `test-01-orchestrator.ps1` | Orchestrator | ❌ Non | ~100 MB | 1-2 min |
| `test-02-comfyui.ps1` | ComfyUI | ✅ Oui | ~5-10 GB | 10-30 min |

## 🚀 Utilisation

### Test 1: Orchestrator (Simple, sans GPU)

```powershell
# Démarrer le test
cd docs/genai-suivis/scripts
.\test-01-orchestrator.ps1

# Arrêter le service
.\test-01-orchestrator.ps1 -Stop
```

**Résultat attendu:**
- ✅ Container démarré
- ✅ Health check OK sur http://localhost:8193/health
- ✅ Logs sans erreurs

### Test 2: ComfyUI (Nécessite GPU)

```powershell
# Vérifier les prérequis et taille du téléchargement
cd docs/genai-suivis/scripts
.\test-02-comfyui.ps1

# Si OK, lancer le téléchargement et le test
.\test-02-comfyui.ps1 -Force

# Arrêter le service
.\test-02-comfyui.ps1 -Stop
```

**Résultat attendu:**
- ✅ GPU NVIDIA détecté
- ✅ Image Docker téléchargée (~5-10 GB)
- ✅ Container démarré avec GPU
- ✅ Interface accessible sur http://localhost:8191

## 📊 Ordre d'Exécution Recommandé

1. **Test 1 - Orchestrator** (obligatoire)
   - Valide Docker et réseau de base
   - Rapide (~2 min)
   - Sans GPU

2. **Test 2 - ComfyUI** (recommandé)
   - Valide GPU Docker support
   - Long (~30 min au premier lancement)
   - Teste interface web

## ⚠️ Prérequis

### Système
- Docker Desktop 4.x+
- PowerShell 7.0+
- Windows 11 avec WSL 2

### GPU (pour Test 2+)
- NVIDIA GPU avec CUDA support
- Drivers NVIDIA à jour
- Docker Desktop GPU support activé

### Vérification GPU Docker

```powershell
docker run --rm --gpus all nvidia/cuda:11.8.0-base-ubuntu22.04 nvidia-smi
```

Si erreur, activer dans:
- Docker Desktop → Settings → Resources → WSL Integration
- Cocher "Enable GPU"

## 🐛 Dépannage

### Test 1 échoue

```powershell
# Vérifier Docker
docker --version
docker ps

# Vérifier les logs détaillés
docker compose -f docker-compose.test.yml logs orchestrator
```

### Test 2 - GPU non détecté

```powershell
# Vérifier drivers NVIDIA
nvidia-smi

# Vérifier Docker GPU support
docker run --rm --gpus all nvidia/cuda:11.8.0-base-ubuntu22.04 nvidia-smi

# Si erreur, redémarrer Docker Desktop
```

### Test 2 - Image ne se télécharge pas

- Vérifier connexion internet
- Vérifier espace disque (besoin de 15+ GB libre)
- Docker Desktop → Settings → Resources → Disk image size

### Ports déjà utilisés

```powershell
# Vérifier les ports
netstat -an | findstr "8191"
netstat -an | findstr "8193"

# Arrêter les services en conflit ou modifier les ports dans docker-compose.test.yml
```

## 📝 Logs et Rapports

Les scripts génèrent des logs dans le terminal. Pour sauvegarder:

```powershell
.\test-01-orchestrator.ps1 > test-01-results.log 2>&1
.\test-02-comfyui.ps1 -Force > test-02-results.log 2>&1
```

## 🧹 Nettoyage

```powershell
# Arrêter tous les services de test
docker compose -f docker-compose.test.yml down

# Supprimer le réseau de test
docker network rm genai-test-network

# Supprimer les images (optionnel, libère de l'espace)
docker rmi comfyanonymous/comfyui:latest-cu121
docker rmi coursia/genai-orchestrator:test
```

## 📚 Documentation Associée

- [docker-compose.test.yml](../../../docker-compose.test.yml) - Configuration tests
- [Infrastructure Docker](../../genai/docker-specs.md) - Spécifications complètes
- [Guide Déploiement](../../genai/deployment-guide.md) - Guide complet