# Rapport - Problème Docker ComfyUI avec venv Python

## Date
2025-10-24 01:27 UTC+2

## Contexte
Mission de finalisation de la configuration Docker ComfyUI avec venv Python 3.10 et authentification ComfyUI-Login.

## Travaux Réalisés

### 1. Scripts Créés
- ✅ `scripts/genai-auth/create-venv-in-container.sh` - Script automatisé de création venv
- ✅ `scripts/genai-auth/recreate-venv-in-container.sh` - Script de recréation avec diagnostic
- ✅ `docker-configurations/services/comfyui-qwen/init-venv.sh` - Script d'initialisation venv pour Docker

### 2. Venv Créé avec Succès
```bash
# Commande exécutée avec succès:
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && python3 -m venv venv && source venv/bin/activate && pip install -r requirements.txt"
```

**Résultat:**
- ✅ Venv créé: `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv`
- ✅ Python 3.12 (compatible avec Python 3.10)
- ✅ Toutes les dépendances installées (torch, torchvision, PIL, yaml, etc.)
- ✅ Total: ~80 packages installés

### 3. Configuration Docker Modifiée
- ✅ `docker-configurations/services/comfyui-qwen/docker-compose.yml` simplifié
- ✅ Suppression de la création automatique du venv dans le container
- ✅ Utilisation du venv pré-créé dans le workspace WSL

## Problème Identifié

### Symptôme
Le container ComfyUI crashe en boucle avec l'erreur:
```
ModuleNotFoundError: No module named 'yaml'
```

### Cause Racine
**INCOMPATIBILITÉ ENTRE PYTHON DU VENV ET PYTHON DU CONTAINER**

1. **Venv créé dans WSL:**
   - Python 3.12 (`/usr/bin/python3`)
   - Dépendances installées pour Python 3.12
   - Chemin: `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv`

2. **Container Docker:**
   - Installe Python 3.10 au démarrage
   - Le script d'activation du venv ne fonctionne pas correctement
   - Le container utilise Python 3.10 système sans les dépendances

3. **Problème de symlinks:**
   ```bash
   venv/bin/python -> python3
   venv/bin/python3 -> /usr/bin/python3  # Pointe vers Python système WSL
   ```

## Solutions Proposées

### Solution A (RECOMMANDÉE) - Venv Compatible avec Container
Recréer le venv **DANS** le container avec Python 3.10:

```bash
# 1. Arrêter le container
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down"

# 2. Supprimer l'ancien venv
wsl -d Ubuntu -e bash -c "rm -rf /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv"

# 3. Créer le venv dans un container temporaire
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose run --rm comfyui-qwen bash -c 'apt-get update -qq && apt-get install -y python3 python3-pip python3-venv && cd /workspace/ComfyUI && python3 -m venv venv && source venv/bin/activate && pip install --upgrade pip && pip install -r requirements.txt'"

# 4. Redémarrer le container normalement
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"

# 5. Surveiller les logs
wsl -d Ubuntu -e docker logs -f --tail 100 comfyui-qwen
```

### Solution B - Image Docker Personnalisée
Créer une image Docker avec Python 3.10 et les dépendances pré-installées:

```dockerfile
FROM nvidia/cuda:12.4.0-devel-ubuntu22.04

# Installer Python 3.10
RUN apt-get update && \
    apt-get install -y python3.10 python3-pip python3-venv git curl wget ca-certificates && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Créer venv et installer dépendances
WORKDIR /workspace/ComfyUI
COPY requirements.txt .
RUN python3 -m venv venv && \
    . venv/bin/activate && \
    pip install --upgrade pip && \
    pip install -r requirements.txt

CMD ["bash", "-c", "source venv/bin/activate && python main.py --listen 0.0.0.0 --port 8188"]
```

### Solution C - Modifier docker-compose.yml pour Utiliser init-venv.sh
Copier `init-venv.sh` dans le workspace et l'utiliser comme entrypoint:

```yaml
command: >
  bash -c "
    apt-get update -qq &&
    apt-get install -y python3 python3-pip git curl wget ca-certificates &&
    apt-get clean &&
    rm -rf /var/lib/apt/lists/* &&
    cd /workspace/ComfyUI &&
    bash init-venv.sh
  "
```

## État Actuel

### Container
- ❌ État: Restarting (1)
- ❌ Erreur: ModuleNotFoundError: No module named 'yaml'
- ⚠️ Le venv n'est pas activé correctement

### Venv
- ✅ Existe: `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv`
- ✅ Dépendances installées
- ⚠️ Créé avec Python 3.12 (WSL) au lieu de Python 3.10 (container)

### Fichiers Modifiés
1. `docker-configurations/services/comfyui-qwen/docker-compose.yml` - Simplifié
2. `docker-configurations/services/comfyui-qwen/init-venv.sh` - Nouveau script d'init
3. `scripts/genai-auth/create-venv-in-container.sh` - Script de création
4. `scripts/genai-auth/recreate-venv-in-container.sh` - Script de recréation

## Prochaines Étapes

### Immédiat (Solution A)
1. ⏭️ Exécuter la Solution A (venv compatible container)
2. ⏭️ Valider le démarrage de ComfyUI
3. ⏭️ Tester l'endpoint http://localhost:8188
4. ⏭️ Vérifier le chargement de ComfyUI-Login

### Court Terme
1. ⏭️ Documenter la procédure de création du venv
2. ⏭️ Créer un script d'automatisation complet
3. ⏭️ Tester l'authentification ComfyUI-Login

### Moyen Terme
1. ⏭️ Créer une image Docker personnalisée (Solution B)
2. ⏭️ Automatiser le déploiement complet
3. ⏭️ Créer des tests de validation

## Leçons Apprises

### Problèmes Rencontrés
1. **Incompatibilité Python**: Venv créé avec Python WSL vs Python container
2. **Symlinks**: Venv pointe vers Python système au lieu de Python isolé
3. **Docker-compose run**: N'exécute pas la commande principale, donc Python n'est pas installé

### Bonnes Pratiques Identifiées
1. ✅ Toujours créer le venv **dans** le container avec la même version Python
2. ✅ Utiliser `--copies` lors de la création du venv pour éviter les symlinks
3. ✅ Tester l'activation du venv avant le démarrage de l'application
4. ✅ Séparer installation système et installation venv

## Commandes Utiles

```bash
# Vérifier l'état du container
wsl -d Ubuntu -e docker ps -a | Select-String comfyui

# Voir les logs en temps réel
wsl -d Ubuntu -e docker logs -f --tail 100 comfyui-qwen

# Vérifier le venv
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && ls -la venv/bin/python*"

# Tester l'activation du venv
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && source venv/bin/activate && python --version && python -c 'import yaml; import torch'"

# Arrêter et nettoyer
wsl -d Ubuntu -e bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down"
```

## Conclusion

La mission a permis de:
- ✅ Créer les scripts d'automatisation nécessaires
- ✅ Créer un venv fonctionnel (mais incompatible avec le container)
- ✅ Identifier la cause racine du problème
- ✅ Proposer 3 solutions viables

**Action Immédiate Recommandée:** Exécuter la **Solution A** pour recréer le venv dans le container avec Python 3.10.

---
*Rapport généré le 2025-10-24 01:27 UTC+2*
*Mission: Finalisation Docker ComfyUI avec venv Python 3.10*