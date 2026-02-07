# QuantConnect LEAN Docker - Setup Local (Optionnel)

Configuration Docker pour exécuter QuantConnect LEAN Engine en local.

**Note** : Ce setup Docker est **optionnel**. Pour la majorité des utilisateurs, l'exécution cloud sur [QuantConnect.com](https://www.quantconnect.com) est recommandée (plus simple, données gratuites, pas de configuration).

## Quand Utiliser Docker Local ?

Utilisez ce setup Docker si :

- ✅ Vous voulez développer **offline**
- ✅ Vous avez besoin de **GPU** pour Deep Learning (notebooks 22-25)
- ✅ Vous voulez des **backtests rapides** avec données locales
- ✅ Vous voulez **débugger** en profondeur avec breakpoints
- ✅ Vous voulez utiliser des **custom data sources** non disponibles en cloud

**Pour débuter**, utilisez plutôt : [QuantConnect Cloud](../../MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md)

---

## Prérequis

- **Docker Desktop** installé et en cours d'exécution
  - Windows : [Docker Desktop for Windows](https://docs.docker.com/desktop/install/windows-install/)
  - macOS : [Docker Desktop for Mac](https://docs.docker.com/desktop/install/mac-install/)
  - Linux : [Docker Engine](https://docs.docker.com/engine/install/)

- **Python 3.11+** (pour LEAN CLI)

- **Git** (pour cloner le repository CoursIA)

- **(Optionnel) NVIDIA GPU + nvidia-docker** pour Deep Learning

---

## Installation Rapide

### Étape 1 : Cloner le Repository

```bash
cd d:/Dev
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA/docker-configurations/quantconnect
```

### Étape 2 : Configurer l'Environnement

```bash
# Copier le template de configuration
cp .env.example .env

# Éditer .env et remplir :
# - QC_API_USER_ID (optionnel, pour sync cloud)
# - QC_API_ACCESS_TOKEN (optionnel)
# - NEWSAPI_KEY (pour notebook 17 - Sentiment Analysis)
# - OPENAI_API_KEY (pour notebook 26 - LLM Trading Signals)
```

### Étape 3 : Lancer LEAN Engine

```bash
# Lancer le container
docker-compose up -d

# Vérifier que le container est running
docker-compose ps

# Expected output:
# NAME                    STATUS
# quantconnect-lean       Up X seconds
```

### Étape 4 : Télécharger des Données (Optionnel)

Les données de marché doivent être téléchargées pour backtests locaux :

```bash
# Accéder au shell du container
docker-compose exec lean-engine bash

# Télécharger données US Equity (gratuit)
lean data download --dataset us-equity --start 20200101 --end 20231231

# Télécharger crypto (gratuit)
lean data download --dataset crypto --start 20200101

# Sortir du shell
exit
```

**Taille approximative** :
- US Equity daily (500 symboles, 5 ans) : ~500 MB
- Crypto daily (top 10, 5 ans) : ~10 MB

### Étape 5 : Tester avec un Backtest

```bash
# Créer un projet de test
docker-compose exec lean-engine lean project-create --language python TestStrategy

# Backtest
docker-compose exec lean-engine lean backtest TestStrategy

# Voir résultats
docker-compose exec lean-engine cat Results/latest.json
```

---

## Commandes Utiles

### Gestion du Container

```bash
# Démarrer LEAN Engine
docker-compose up -d

# Arrêter
docker-compose down

# Voir les logs
docker-compose logs -f lean-engine

# Redémarrer
docker-compose restart

# Shell interactif
docker-compose exec lean-engine bash
```

### Backtesting

```bash
# Backtest un algorithme Python
docker-compose exec lean-engine lean backtest /Lean/Launcher/algorithms/python/MovingAverageCrossover.py

# Backtest avec dates personnalisées
docker-compose exec lean-engine lean backtest --start 20200101 --end 20231231 TestStrategy

# Voir résultats détaillés
docker-compose exec lean-engine lean report TestStrategy
```

### Gestion des Données

```bash
# Lister datasets disponibles
docker-compose exec lean-engine lean data list

# Télécharger dataset spécifique
docker-compose exec lean-engine lean data download --dataset us-equity --start 20200101

# Supprimer données (libérer espace)
docker-compose exec lean-engine rm -rf /Lean/Data/equity
```

### Debugging

```bash
# Lancer avec debugger Python (port 5678)
docker-compose exec lean-engine python -m ptvsd --host 0.0.0.0 --port 5678 --wait /Lean/Launcher/your_algorithm.py

# Dans VSCode : F5 avec launch.json configuré pour port 5678
```

---

## Configuration GPU (Optionnel)

Pour utiliser GPU avec les notebooks Deep Learning (22-25) :

### 1. Installer nvidia-docker

**Linux** :
```bash
# Ajouter repository
distribution=$(. /etc/os-release;echo $ID$VERSION_ID)
curl -s -L https://nvidia.github.io/nvidia-docker/gpgkey | sudo apt-key add -
curl -s -L https://nvidia.github.io/nvidia-docker/$distribution/nvidia-docker.list | sudo tee /etc/apt/sources.list.d/nvidia-docker.list

# Installer
sudo apt-get update && sudo apt-get install -y nvidia-docker2

# Redémarrer Docker
sudo systemctl restart docker
```

**Windows** :
- Installer [NVIDIA Container Toolkit](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/install-guide.html#docker)
- Docker Desktop doit être en mode WSL2

### 2. Activer GPU dans docker-compose.yml

Décommenter la section GPU :

```yaml
deploy:
  resources:
    reservations:
      devices:
        - driver: nvidia
          device_ids: ['${GPU_DEVICE_ID:-0}']
          capabilities: [gpu]
```

### 3. Configurer .env

```env
GPU_DEVICE_ID=0  # ID de votre GPU (0 pour le premier)
```

### 4. Redémarrer

```bash
docker-compose down
docker-compose up -d
```

### 5. Vérifier GPU

```bash
docker-compose exec lean-engine nvidia-smi

# Expected output: GPU info (utilisation, mémoire, etc.)
```

---

## Volumes et Persistance

Le container LEAN monte les répertoires suivants :

| Host | Container | Description |
|------|-----------|-------------|
| `../../MyIA.AI.Notebooks/QuantConnect` | `/Lean/Launcher/notebooks` | Notebooks Jupyter |
| `../../MyIA.AI.Notebooks/QuantConnect/algorithms` | `/Lean/Launcher/algorithms` | Algorithmes production |
| `../../MyIA.AI.Notebooks/QuantConnect/data` | `/Lean/Data` | Données de marché |
| `../../MyIA.AI.Notebooks/QuantConnect/shared` | `/Lean/Launcher/shared` | Bibliothèques partagées |
| `./results` | `/Lean/Results` | Résultats de backtests |
| `./logs` | `/Lean/Logs` | Logs LEAN |

**Persistance** : Toutes les données (résultats, logs, données market) persistent après arrêt du container.

---

## Troubleshooting

### Docker ne démarre pas

**Problème** : "Docker daemon not running"
**Solution** : Lancer Docker Desktop

### Container crashe au démarrage

**Problème** : "Exited (137)" (Out of Memory)
**Solution** : Augmenter mémoire Docker Desktop (Settings → Resources → Memory → 8GB+)

### Données non trouvées

**Problème** : "Data not found for SPY"
**Solution** :
```bash
docker-compose exec lean-engine lean data download --dataset us-equity --start 20200101
```

### Permission denied (Linux)

**Problème** : "Permission denied" lors de l'accès aux volumes
**Solution** :
```bash
# Ajouter votre user au groupe docker
sudo usermod -aG docker $USER

# Se déconnecter et reconnecter
# Ou : newgrp docker
```

### GPU not detected

**Problème** : "CUDA not available"
**Solutions** :
1. Vérifier nvidia-docker : `docker run --rm --gpus all nvidia/cuda:11.0-base nvidia-smi`
2. Vérifier section GPU dans docker-compose.yml (décommenter)
3. Vérifier `GPU_DEVICE_ID` dans `.env`

### Backtest trop lent

**Solutions** :
1. Réduire période de backtest
2. Utiliser résolution Daily au lieu de Minute
3. Augmenter CPU/Memory limits dans `.env`
4. Vérifier que Docker Desktop a suffisamment de ressources

---

## Nettoyage

```bash
# Arrêter et supprimer container
docker-compose down

# Supprimer volumes (ATTENTION : efface données)
docker-compose down -v

# Supprimer image LEAN (libère espace disque)
docker rmi quantconnect/lean:latest

# Nettoyer système Docker complet
docker system prune -a
```

---

## Ressources

- [LEAN Engine GitHub](https://github.com/QuantConnect/Lean)
- [LEAN CLI Documentation](https://www.quantconnect.com/docs/v2/lean-cli)
- [Docker Documentation](https://docs.docker.com/)
- [nvidia-docker GitHub](https://github.com/NVIDIA/nvidia-docker)

---

## Notes Importantes

1. **Cloud-first** : Ce setup Docker est optionnel. La plateforme QuantConnect cloud est recommandée pour débutants.

2. **Données locales** : Les données de marché doivent être téléchargées manuellement (contrairement au cloud où c'est automatique).

3. **Ressources** : LEAN peut consommer beaucoup de RAM (surtout avec data minute). Allouer 8GB+ recommandé.

4. **GPU** : Optionnel pour notebooks Deep Learning. Les notebooks sont conçus CPU-first.

5. **Sync cloud** : Avec `QC_API_*` configuré, vous pouvez sync vos projets entre local et cloud.

---

**Besoin d'aide ?** Consultez le [QuantConnect Forum](https://www.quantconnect.com/forum) ou la documentation principale : [README](../../MyIA.AI.Notebooks/QuantConnect/README.md)
