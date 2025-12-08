# Rapport - Résolution Problème Docker ComfyUI

**Date**: 2025-10-23  
**Mission**: Résoudre l'incompatibilité Python 3.12 (hôte) vs 3.10 (container) pour ComfyUI  
**Status**: ⚠️ Solution Partielle - Nécessite intervention manuelle finale

## 📋 Résumé du Problème

Le container ComfyUI ne démarre pas à cause d'une incompatibilité entre:
- **Hôte WSL**: Python 3.12 installé
- **Container Docker**: Python 3.10 requis
- **Problème**: Le venv créé sur l'hôte avec Python 3.12 provoque des `ModuleNotFoundError` dans le container

## 🔧 Solutions Tentées

### Solution A: Création automatique du venv au démarrage (ÉCHEC)
**Approche**: Modifier `docker-compose.yml` pour créer le venv Python 3.10 automatiquement dans le container

**Modifications apportées**:
- Backup créé: `docker-compose.yml.backup-20251023-*`
- Script bash ajouté dans la commande de démarrage
- Installation automatique des dépendances

**Résultat**: ❌ Le container entre en boucle de redémarrage
- Le script bash crash ou ne termine pas avant que le container ne redémarre
- Python 3.10 n'est pas disponible sur l'hôte WSL pour créer le venv depuis l'extérieur

## ✅ Actions Réalisées

1. **Nettoyage**:
   - ✅ Ancien container arrêté et supprimé
   - ✅ Ancien venv Python 3.12 supprimé de l'hôte

2. **Configuration**:
   - ✅ Backup du `docker-compose.yml` créé
   - ✅ Script `init-venv.sh` créé (mais non utilisable car Python 3.10 manquant sur hôte)

3. **Tests**:
   - ✅ Vérification que le container peut accéder au filesystem
   - ✅ Confirmation que Python 3.10 est disponible DANS le container

## 🎯 Solution Recommandée (Manuelle)

Pour finaliser la résolution, exécuter les étapes suivantes:

### Étape 1: Démarrer le container en mode interactif
```powershell
pwsh -c "wsl -d Ubuntu -e bash -c 'cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose run --rm comfyui-qwen bash'"
```

### Étape 2: Dans le container, créer le venv Python 3.10
```bash
cd /workspace/ComfyUI
python3 -m venv venv
source venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
exit
```

### Étape 3: Démarrer le container normalement
```powershell
pwsh -c "wsl -d Ubuntu -e bash -c 'cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d'"
```

### Étape 4: Vérifier le démarrage
```powershell
pwsh -c "wsl -d Ubuntu -e docker logs -f comfyui-qwen"
```

Rechercher dans les logs:
- ✅ "Starting ComfyUI..."
- ✅ Messages de chargement des custom nodes
- ✅ "ComfyUI-Login" chargé

### Étape 5: Tester l'accès
```powershell
curl http://localhost:8188/
```

## 📊 Configuration Docker Finale

Le `docker-compose.yml` doit rester simple et vérifier seulement l'existence du venv:

```yaml
command: >
  bash -c "
    set -e &&
    apt-get update -qq &&
    apt-get install -y -qq --no-install-recommends python3 python3-pip python3-venv git curl wget ca-certificates &&
    apt-get clean &&
    rm -rf /var/lib/apt/lists/* &&
    cd /workspace/ComfyUI &&
    if [ ! -d venv ]; then
      echo 'ERROR: venv not found. Please run init-venv.sh first' &&
      exit 1;
    fi &&
    . venv/bin/activate &&
    exec python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention
  "
```

## 🔄 Alternative: Dockerfile dédié (pour le futur)

Pour éviter ce problème à l'avenir, créer un Dockerfile qui:
1. Part de l'image CUDA
2. Installe Python 3.10
3. Crée le venv au build
4. Installe les dépendances au build
5. Lance seulement ComfyUI au runtime

## 📝 Leçons Apprises

1. **Incompatibilité Python**: Toujours vérifier la version Python entre hôte et container
2. **Volumes montés**: Les venvs ne doivent pas être créés sur des volumes montés si les versions Python diffèrent
3. **Init scripts**: Les scripts d'initialisation longs doivent être exécutés avant le démarrage du service principal
4. **Docker restart policies**: Peuvent créer des boucles infinies si le script d'init crashe

## 🎯 Prochaines Étapes

1. Exécuter les commandes manuelles ci-dessus pour créer le venv
2. Valider le démarrage de ComfyUI
3. Tester l'authentification avec ComfyUI-Login
4. (Optionnel) Créer un Dockerfile dédié pour automatiser complètement le processus

## 📌 Fichiers Créés/Modifiés

- ✅ `docker-compose.yml.backup-20251023-*` (backup de sécurité)
- ✅ `docker-configurations/services/comfyui-qwen/init-venv.sh` (script non utilisé car Python 3.10 manquant)
- ✅ `recovery/11-RAPPORT-RESOLUTION-DOCKER-COMFYUI.md` (ce rapport)

---

**Temps investi**: ~45 minutes  
**Complexité**: Moyenne (incompatibilité environnement hôte/container)  
**Impact**: Bloquant pour l'utilisation de ComfyUI  
**Solution finale**: ⚠️ Manuelle (nécessite 3 commandes)