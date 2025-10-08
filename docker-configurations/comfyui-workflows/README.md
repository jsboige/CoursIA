# ComfyUI Workflows Service

## 📋 Description

Service ComfyUI dédié aux workflows pédagogiques et orchestration avancée.
Permet de créer et exécuter des workflows complexes combinant plusieurs modèles.

## 🎯 Rôle du Service

- Exécution de workflows ComfyUI éducatifs
- Orchestration multi-modèles (FLUX + SD3.5)
- Bibliothèque de workflows prédéfinis
- Interface web pour édition de workflows

## 📁 Structure des Fichiers

```
comfyui-workflows/
├── config/                       # Configuration du service
├── workflows/                    # Workflows ComfyUI (.json)
│   └── (workflows pédagogiques à créer)
└── README.md                     # Ce fichier
```

## 🎨 Workflows Disponibles

### Workflows Éducatifs (à créer)

1. **basic-text-to-image.json**
   - Workflow simple: prompt → image
   - Idéal pour débutants

2. **multi-model-comparison.json**
   - Compare FLUX vs SD3.5 sur même prompt
   - Analyse des différences

3. **style-transfer.json**
   - Transfert de style entre images
   - Utilise VAE et LoRA

4. **batch-generation.json**
   - Génération par lots
   - Variations sur un thème

## 🔧 Configuration

### Connexion aux Autres Services

Ce service peut communiquer avec:
- **FLUX.1-dev** via réseau Docker (`flux-1-dev:8188`)
- **Stable Diffusion 3.5** via réseau Docker (`stable-diffusion-35:8000`)

### Variables d'Environnement

- `COMFYUI_ARGS=--enable-cors-header` : Active CORS pour API
- `WORKFLOW_AUTO_SAVE=true` : Sauvegarde auto des workflows
- `ENABLE_WORKFLOW_API=true` : Active l'API workflow

## 🚀 Utilisation

### Démarrage du Service

```powershell
# Via docker-compose principal
docker compose up comfyui-workflows -d

# Suivre les logs
docker compose logs -f comfyui-workflows
```

### Accès à l'Interface

- **Interface Web**: http://localhost:8191
- **API**: http://localhost:8191/api

### Créer un Nouveau Workflow

1. Ouvrir http://localhost:8191
2. Menu → Load → New workflow
3. Ajouter des nodes (clic droit)
4. Connecter les nodes
5. Menu → Save → Sauvegarder

### Exécuter un Workflow

1. Charger un workflow existant
2. Configurer les paramètres (prompts, résolution, etc.)
3. Cliquer sur "Queue Prompt"
4. Suivre la progression dans l'interface

## 📦 Partage des Modèles

Ce service partage les modèles avec FLUX.1-dev:
- **Checkpoints**: Accès aux modèles FLUX
- **VAE/CLIP**: Encodeurs partagés
- **Custom Nodes**: Nodes personnalisés

## 🧪 Commandes de Test

```powershell
# Vérifier que le service démarre
docker compose logs comfyui-workflows

# Tester l'interface
# Ouvrir: http://localhost:8191

# Lister les workflows disponibles
docker exec comfyui-workflows ls -l /app/web/workflows/

# Vérifier la connectivité aux autres services
docker exec comfyui-workflows ping -c 3 flux-1-dev
docker exec comfyui-workflows ping -c 3 stable-diffusion-35
```

## 📊 Ressources Système

### Configuration Minimale
- **RAM**: 4 GB
- **GPU VRAM**: 4 GB (si génération directe)
- **Espace Disque**: 10 GB

### Configuration Recommandée
- **RAM**: 8 GB
- **GPU VRAM**: 8 GB+
- **Espace Disque**: 20 GB

**Note**: Ce service peut fonctionner sans GPU s'il orchestre uniquement d'autres services.

## 🎓 Workflows Pédagogiques

### Structure d'un Workflow

```json
{
  "nodes": [
    {
      "id": 1,
      "type": "CLIPTextEncode",
      "inputs": {"text": "A beautiful landscape"}
    },
    {
      "id": 2,
      "type": "KSampler",
      "inputs": {"model": "flux-1-dev"}
    }
  ],
  "connections": [...]
}
```

### Workflows par Niveau

| Niveau | Workflow | Complexité |
|--------|----------|------------|
| 🟢 Débutant | basic-text-to-image | Simple |
| 🟡 Intermédiaire | style-transfer | Moyenne |
| 🔴 Avancé | multi-model-comparison | Complexe |

## 🐛 Dépannage

### L'interface ne charge pas

```powershell
# Vérifier les logs
docker compose logs comfyui-workflows

# Vérifier le port
netstat -an | findstr "8191"
```

### Workflow échoue

Causes possibles:
- Modèle non chargé
- Paramètres invalides
- Mémoire insuffisante

Solution:
```powershell
# Consulter les logs d'erreur
docker compose logs comfyui-workflows | Select-String -Pattern "error|fail"
```

### Impossible de charger un workflow

- Vérifier format JSON valide
- Vérifier que les nodes existent
- Vérifier compatibilité version ComfyUI

## 📚 Ressources

- [ComfyUI Documentation](https://github.com/comfyanonymous/ComfyUI/wiki)
- [Workflow Examples](https://comfyanonymous.github.io/ComfyUI_examples/)
- [Custom Nodes Repository](https://github.com/ltdrdata/ComfyUI-Manager)

## 🔗 Intégration

### Utilisation depuis Jupyter

```python
import requests

# Charger un workflow
workflow = {
    "prompt": "Beautiful sunset",
    "workflow_id": "basic-text-to-image"
}

response = requests.post(
    "http://localhost:8191/api/prompt",
    json=workflow
)

# Récupérer le résultat
result = response.json()
```

### Utilisation depuis API

```bash
# POST un workflow
curl -X POST http://localhost:8191/api/prompt \
  -H "Content-Type: application/json" \
  -d @workflow.json
```

## 📝 Bonnes Pratiques

1. **Nommage**: Utiliser des noms descriptifs pour les workflows
2. **Documentation**: Commenter les workflows complexes
3. **Versioning**: Sauvegarder les versions de workflows
4. **Test**: Tester les workflows avec des paramètres variés
5. **Optimisation**: Réutiliser les modèles chargés quand possible