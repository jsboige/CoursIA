# API OpenAI Compatible - ComfyUI + Forge

**Date**: 2025-10-15 23:55 UTC  
**Phase**: 12A Finalisation  
**Status**: Documentation Complète

## Vue d'Ensemble

Ce document décrit les APIs disponibles pour ComfyUI et Forge, avec focus sur la compatibilité OpenAI pour faciliter l'intégration.

---

## ComfyUI API

### Configuration de Base

**Base URL**: `https://qwen-image-edit.myia.io`  
**Protocol**: HTTPS avec certificat SSL Let's Encrypt  
**Port interne**: 8188 (via reverse proxy IIS)

### Endpoints Principaux

#### 1. System Stats
**Endpoint**: `/system_stats`  
**Méthode**: GET  
**Description**: Récupère les statistiques système (GPU, mémoire, etc.)

**Exemple PowerShell**:
```powershell
$response = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats" -UseBasicParsing
$stats = $response.Content | ConvertFrom-Json
Write-Host "GPU: $($stats.devices[0].name)"
Write-Host "VRAM libre: $($stats.devices[0].vram_free / 1GB) GB"
```

**Exemple Python**:
```python
import requests

response = requests.get("https://qwen-image-edit.myia.io/system_stats")
stats = response.json()
print(f"GPU: {stats['devices'][0]['name']}")
print(f"VRAM libre: {stats['devices'][0]['vram_free'] / 1024**3:.2f} GB")
```

**Réponse type**:
```json
{
  "devices": [
    {
      "name": "NVIDIA GeForce RTX 3090",
      "type": "cuda",
      "vram_total": 25769803776,
      "vram_free": 24360296448
    }
  ],
  "system": {
    "os": "Windows",
    "python_version": "3.10.x"
  }
}
```

---

#### 2. Queue Management
**Endpoint**: `/queue`  
**Méthode**: GET  
**Description**: Récupère l'état de la queue de génération

**Exemple PowerShell**:
```powershell
$queue = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/queue" -UseBasicParsing | ConvertFrom-Json
Write-Host "Files en attente: $($queue.queue_pending.Count)"
Write-Host "En cours: $($queue.queue_running.Count)"
```

**Réponse type**:
```json
{
  "queue_running": [],
  "queue_pending": []
}
```

---

#### 3. Submit Prompt
**Endpoint**: `/prompt`  
**Méthode**: POST  
**Description**: Soumet un workflow pour génération

**Exemple PowerShell**:
```powershell
$workflow = @{
    prompt = @{
        "1" = @{
            class_type = "CheckpointLoaderSimple"
            inputs = @{
                ckpt_name = "model.safetensors"
            }
        }
        # ... autres nodes
    }
} | ConvertTo-Json -Depth 10

$response = Invoke-WebRequest `
    -Uri "https://qwen-image-edit.myia.io/prompt" `
    -Method Post `
    -Body $workflow `
    -ContentType "application/json"
```

**Exemple Python**:
```python
import requests
import json

workflow = {
    "prompt": {
        "1": {
            "class_type": "CheckpointLoaderSimple",
            "inputs": {
                "ckpt_name": "model.safetensors"
            }
        }
        # ... autres nodes
    }
}

response = requests.post(
    "https://qwen-image-edit.myia.io/prompt",
    json=workflow
)
result = response.json()
prompt_id = result.get("prompt_id")
```

---

#### 4. History
**Endpoint**: `/history`  
**Méthode**: GET  
**Description**: Récupère l'historique des prompts

**Exemple PowerShell**:
```powershell
$history = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/history" -UseBasicParsing | ConvertFrom-Json
$history.PSObject.Properties | ForEach-Object {
    Write-Host "ID: $($_.Name) - Status: $($_.Value.status.status_str)"
}
```

---

#### 5. Object Info
**Endpoint**: `/object_info`  
**Méthode**: GET  
**Description**: Récupère les informations sur tous les nodes disponibles (y compris custom nodes)

**Exemple PowerShell**:
```powershell
$objects = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/object_info" -UseBasicParsing | ConvertFrom-Json
$qwenNodes = $objects.PSObject.Properties | Where-Object { $_.Name -like "*Qwen*" }
$qwenNodes | ForEach-Object { Write-Host $_.Name }
```

---

### Mode API OpenAI (Custom Nodes)

ComfyUI ne dispose pas nativement d'une API compatible OpenAI, mais des custom nodes peuvent être installés pour ajouter cette fonctionnalité:

**Custom Nodes Potentiels**:
- `ComfyUI-LLM` - Pour intégration LLM
- `ComfyUI-OpenAI` - Wrapper OpenAI (si disponible)

**Vérification disponibilité**:
```powershell
# Vérifier si endpoints OpenAI existent
$endpoints = @("/v1/completions", "/v1/chat/completions", "/api/v1/completions")
foreach ($endpoint in $endpoints) {
    try {
        Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io$endpoint" -Method Get -ErrorAction Stop
        Write-Host "✅ $endpoint disponible"
    } catch {
        Write-Host "❌ $endpoint non disponible"
    }
}
```

---

## Forge API

### Configuration de Base

**Base URL**: `https://turbo.stable-diffusion-webui-forge.myia.io`  
**Protocol**: HTTPS avec certificat SSL Let's Encrypt  
**Port interne**: 7860 (via reverse proxy IIS)

### Endpoints Principaux

#### 1. API Documentation (Swagger)
**Endpoint**: `/docs`  
**Méthode**: GET  
**Description**: Documentation interactive Swagger de l'API

**Accès**: Ouvrir dans navigateur  
```
https://turbo.stable-diffusion-webui-forge.myia.io/docs
```

---

#### 2. Text-to-Image
**Endpoint**: `/sdapi/v1/txt2img`  
**Méthode**: POST  
**Description**: Génération d'image à partir d'un prompt texte

**Exemple PowerShell**:
```powershell
$body = @{
    prompt = "a beautiful landscape, highly detailed, 8k"
    negative_prompt = "blurry, low quality"
    steps = 20
    width = 512
    height = 512
    cfg_scale = 7.0
    sampler_name = "Euler a"
    seed = -1
} | ConvertTo-Json

$response = Invoke-WebRequest `
    -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/txt2img" `
    -Method Post `
    -Body $body `
    -ContentType "application/json" `
    -TimeoutSec 120

$result = $response.Content | ConvertFrom-Json
$imageBase64 = $result.images[0]

# Sauvegarder l'image
$imageBytes = [Convert]::FromBase64String($imageBase64)
[IO.File]::WriteAllBytes("output.png", $imageBytes)
```

**Exemple Python**:
```python
import requests
import base64
from io import BytesIO
from PIL import Image

payload = {
    "prompt": "a beautiful landscape, highly detailed, 8k",
    "negative_prompt": "blurry, low quality",
    "steps": 20,
    "width": 512,
    "height": 512,
    "cfg_scale": 7.0,
    "sampler_name": "Euler a",
    "seed": -1
}

response = requests.post(
    "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/txt2img",
    json=payload,
    timeout=120
)

result = response.json()
image_data = base64.b64decode(result['images'][0])
image = Image.open(BytesIO(image_data))
image.save("output.png")
```

**Paramètres Principaux**:
| Paramètre | Type | Description | Défaut |
|-----------|------|-------------|---------|
| `prompt` | string | Prompt de génération | Required |
| `negative_prompt` | string | Éléments à éviter | "" |
| `steps` | integer | Nombre d'étapes | 20 |
| `width` | integer | Largeur image | 512 |
| `height` | integer | Hauteur image | 512 |
| `cfg_scale` | float | Scale CFG | 7.0 |
| `sampler_name` | string | Nom du sampler | "Euler a" |
| `seed` | integer | Seed (-1 = aléatoire) | -1 |
| `batch_size` | integer | Nombre d'images | 1 |

---

#### 3. Image-to-Image
**Endpoint**: `/sdapi/v1/img2img`  
**Méthode**: POST  
**Description**: Génération à partir d'une image source

**Exemple PowerShell**:
```powershell
# Charger image source en base64
$imageBytes = [IO.File]::ReadAllBytes("input.png")
$imageBase64 = [Convert]::ToBase64String($imageBytes)

$body = @{
    init_images = @($imageBase64)
    prompt = "transform into oil painting style"
    steps = 20
    denoising_strength = 0.7
} | ConvertTo-Json

$response = Invoke-WebRequest `
    -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/img2img" `
    -Method Post `
    -Body $body `
    -ContentType "application/json" `
    -TimeoutSec 120
```

---

#### 4. Options & Models
**Endpoint**: `/sdapi/v1/options`  
**Méthode**: GET  
**Description**: Récupère les options de configuration

```powershell
$options = Invoke-WebRequest -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/options" -UseBasicParsing | ConvertFrom-Json
Write-Host "Modèle actuel: $($options.sd_model_checkpoint)"
```

**Endpoint**: `/sdapi/v1/sd-models`  
**Méthode**: GET  
**Description**: Liste les modèles disponibles

```powershell
$models = Invoke-WebRequest -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/sd-models" -UseBasicParsing | ConvertFrom-Json
$models | ForEach-Object { Write-Host $_.title }
```

**Endpoint**: `/sdapi/v1/samplers`  
**Méthode**: GET  
**Description**: Liste les samplers disponibles

```powershell
$samplers = Invoke-WebRequest -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/samplers" -UseBasicParsing | ConvertFrom-Json
$samplers | ForEach-Object { Write-Host $_.name }
```

---

## Exemples d'Intégration

### Workflow Complet ComfyUI + Forge

**Scénario**: Utiliser ComfyUI pour le traitement avancé et Forge pour la génération simple

```powershell
# 1. Vérifier disponibilité services
$comfyStats = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats" -UseBasicParsing | ConvertFrom-Json
$forgeModels = Invoke-WebRequest -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/sd-models" -UseBasicParsing | ConvertFrom-Json

Write-Host "✅ ComfyUI GPU: $($comfyStats.devices[0].name)"
Write-Host "✅ Forge modèles: $($forgeModels.Count)"

# 2. Génération via Forge
$payload = @{
    prompt = "a serene mountain landscape"
    steps = 25
    width = 768
    height = 768
} | ConvertTo-Json

$image = Invoke-WebRequest `
    -Uri "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/txt2img" `
    -Method Post `
    -Body $payload `
    -ContentType "application/json"

Write-Host "✅ Image générée via Forge"

# 3. (Optionnel) Post-traitement via ComfyUI
# Utiliser l'image générée comme input pour un workflow ComfyUI avancé
```

---

## Sécurité et Bonnes Pratiques

### Authentification
⚠️ **Important**: Actuellement, les APIs ne disposent pas d'authentification native. 

**Recommandations**:
- Utiliser uniquement en réseau interne/VPN
- Configurer authentication au niveau IIS si exposition publique
- Monitorer les accès via logs IIS

### Rate Limiting
- ComfyUI: Queue interne limite les générations simultanées
- Forge: Configurable via `--api-queue-size`

### Timeout
- Générations longues: Prévoir timeout > 120 secondes
- Monitoring: Utiliser `/queue` ou `/system_stats` pour suivre progression

### Gestion Erreurs

**Codes HTTP Communs**:
| Code | Signification | Action |
|------|--------------|--------|
| 200 | Succès | Traiter la réponse |
| 400 | Requête invalide | Vérifier format JSON/paramètres |
| 404 | Endpoint non trouvé | Vérifier l'URL |
| 405 | Méthode non autorisée | Utiliser GET/POST approprié |
| 500 | Erreur serveur | Vérifier logs, ressources GPU |

---

## Monitoring et Debugging

### Logs ComfyUI
```powershell
# Logs Windows Event Viewer
Get-EventLog -LogName Application -Source "ComfyUI" -Newest 50

# Logs IIS
Get-Content "C:\inetpub\logs\LogFiles\W3SVC*\*.log" -Tail 100
```

### Logs Forge
```powershell
# Similaire, adapter selon configuration
```

### Métriques Performance
```powershell
# Script de monitoring
while ($true) {
    $stats = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats" -UseBasicParsing | ConvertFrom-Json
    Write-Host "$(Get-Date -Format 'HH:mm:ss') - VRAM libre: $([math]::Round($stats.devices[0].vram_free / 1GB, 2)) GB"
    Start-Sleep -Seconds 5
}
```

---

## Tests et Validation

### Script de Test Rapide
```powershell
# Test santé des services
$services = @(
    @{ Name = "ComfyUI"; URL = "https://qwen-image-edit.myia.io/system_stats" }
    @{ Name = "Forge"; URL = "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/options" }
)

foreach ($service in $services) {
    try {
        $response = Invoke-WebRequest -Uri $service.URL -UseBasicParsing -TimeoutSec 10
        Write-Host "✅ $($service.Name): OK (HTTP $($response.StatusCode))" -ForegroundColor Green
    } catch {
        Write-Host "❌ $($service.Name): ERREUR - $($_.Exception.Message)" -ForegroundColor Red
    }
}
```

---

## Références

- **ComfyUI GitHub**: https://github.com/comfyanonymous/ComfyUI
- **Forge GitHub**: https://github.com/lllyasviel/stable-diffusion-webui-forge
- **Documentation IIS**: https://learn.microsoft.com/iis
- **Let's Encrypt**: https://letsencrypt.org/

---

**Version**: 1.0  
**Dernière mise à jour**: 2025-10-15 23:55 UTC  
**Auteur**: Phase 12A Finalisation