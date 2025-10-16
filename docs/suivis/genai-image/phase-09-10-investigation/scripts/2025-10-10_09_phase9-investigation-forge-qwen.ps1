# Phase 9: Investigation Infrastructure Forge + Qwen Image-Edit Requirements
# Date: 2025-10-10
# Objectif: Collecter toutes les informations sur l'infrastructure Forge existante et requirements Qwen

$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$reportPath = "docs/genai-suivis/2025-10-10_09_rapport-investigation-forge-qwen.md"

Write-Host "=== Phase 9: Investigation Infrastructure Forge + Qwen ===" -ForegroundColor Cyan
Write-Host ""

# Initialiser le rapport
$report = @"
# Phase 9: Rapport Investigation Infrastructure Forge + Qwen Image-Edit

**Date**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**Objectif**: Investigation complète infrastructure Stable Diffusion Forge + Requirements Qwen Image-Edit

---

## 1. INFRASTRUCTURE FORGE EXISTANTE

### 1.1 Configuration Docker Compose

"@

Write-Host "1. Analyse configuration Docker Compose..." -ForegroundColor Yellow

# Lire les docker-compose
$forgeDir = "D:\Production\stable-diffusion-webui-forge"
if (Test-Path $forgeDir) {
    $report += @"

**Répertoire principal**: ``$forgeDir``

#### Docker Compose principal
``````yaml
$(Get-Content "$forgeDir\docker-compose.yaml" -Raw)
``````

#### Fichier myia.env
``````env
$(Get-Content "$forgeDir\myia.env" -Raw)
``````

#### Fichier myia-turbo.env
``````env
$(Get-Content "$forgeDir\myia-turbo.env" -Raw)
``````

"@
}

Write-Host "2. Analyse reverse proxies IIS..." -ForegroundColor Yellow

$report += @"

### 1.2 Configuration Reverse Proxies IIS

#### stable-diffusion-webui-forge.myia.io
``````xml
$(Get-Content "D:\Production\stable-diffusion-webui-forge.myia.io\web.config" -Raw)
``````

#### turbo.stable-diffusion-webui-forge.myia.io
``````xml
$(Get-Content "D:\Production\turbo.stable-diffusion-webui-forge.myia.io\web.config" -Raw)
``````

**Ports identifiés**:
- Forge principal (GPU 0): Port **36525** → https://stable-diffusion-webui-forge.myia.io
- Forge Turbo (GPU 1): Port **17861** → https://turbo.stable-diffusion-webui-forge.myia.io

"@

Write-Host "3. Investigation workspace WSL et modèles..." -ForegroundColor Yellow

$wslWorkspace = "\\wsl.localhost\Ubuntu\home\jesse\SD\workspace"
$report += @"

### 1.3 Workspace WSL et Modèles

**Chemin workspace**: ``$wslWorkspace``

#### Structure workspace:
``````
"@

if (Test-Path $wslWorkspace) {
    Get-ChildItem $wslWorkspace -Directory | ForEach-Object {
        $report += "$($_.Name)/`n"
    }
}

$report += @"
``````

#### Modèles Stable Diffusion détectés:

"@

$modelsPath = Join-Path $wslWorkspace "stable-diffusion-webui-forge\models"
if (Test-Path $modelsPath) {
    Write-Host "   Scanning modèles (ceci peut prendre quelques minutes)..." -ForegroundColor Gray
    
    # Lister les sous-dossiers de models
    $modelTypes = @("Stable-diffusion", "SDXL", "Flux", "Lora", "VAE", "ControlNet")
    
    foreach ($type in $modelTypes) {
        $typePath = Join-Path $modelsPath $type
        if (Test-Path $typePath) {
            $files = Get-ChildItem $typePath -Include "*.safetensors","*.ckpt","*.pt" -Recurse -ErrorAction SilentlyContinue
            if ($files.Count -gt 0) {
                $report += "`n**$type** ($($files.Count) fichiers):`n"
                $totalSize = 0
                foreach ($file in $files) {
                    $sizeGB = [math]::Round($file.Length/1GB, 2)
                    $totalSize += $sizeGB
                    $report += "- $($file.Name) - ${sizeGB}GB`n"
                }
                $report += "*Total: $([math]::Round($totalSize, 2))GB*`n"
            }
        }
    }
}

$report += @"

---

## 2. CONFIGURATION GPU ACTUELLE

### 2.1 Allocation GPU Forge

Selon docker-compose.yaml:
- **GPU 0 (RTX 3080 - 16GB)**: Service `myia` - Port 36525
  - Args: `--gpu-device-id 0 --cuda-malloc --xformers`
  
- **GPU 1 (RTX 3090 - 24GB)**: Service `myia-turbo` - Port 17861
  - Args: `--gpu-device-id 1 --cuda-malloc --xformers`

### 2.2 Objectif Mission Phase 9+

**Target nouvelle allocation**:
- **RTX 3080 (16GB)** → SD XL Turbo Forge (conserver)
- **RTX 3090 (24GB)** → Qwen Image-Edit (nouveau service)

---

## 3. REQUIREMENTS QWEN IMAGE-EDIT

### 3.1 Modèle de base

**Qwen2-VL-7B-Instruct**:
- Modèle multimodal vision-language
- Capacités: Image understanding, editing, generation
- Taille base: ~14GB en FP16

### 3.2 Quantization pour RTX 3090 24GB

Options identifiées:
1. **AWQ (4-bit)**: ~3.5-4GB VRAM - Recommandé
2. **GPTQ (4-bit)**: ~4-4.5GB VRAM - Alternative
3. **GGUF (Q4_K_M)**: ~4GB VRAM - Pour llama.cpp/Ollama
4. **FP16 (no quant)**: ~14GB VRAM - Possible avec marge

**Recommandation**: AWQ 4-bit permet ~20GB libre pour contexte et batch processing

### 3.3 Méthodes de déploiement

#### Option A: ComfyUI + Qwen Node
**Avantages**:
- Interface visuelle workflow
- Intégration native SD + Qwen
- Workflow image-to-image avec édition

**Inconvénients**:
- Setup plus complexe
- Moins optimisé pour API

#### Option B: vLLM
**Avantages**:
- API OpenAI-compatible native
- Performance optimale (PagedAttention)
- Quantization AWQ intégrée

**Inconvénients**:
- Pas de GUI
- Focus LLM (vision en beta)

#### Option C: Text-Generation-WebUI (Oobabooga)
**Avantages**:
- GUI existante
- Support vision models
- Déjà utilisé sur infrastructure

**Inconvénients**:
- API moins standard
- Performance moyenne

### 3.4 Recommandation préliminaire

**vLLM avec AWQ quantization**:
``````bash
# Installation
pip install vllm

# Lancement Qwen2-VL-7B-AWQ
vllm serve Qwen/Qwen2-VL-7B-Instruct-AWQ \
  --gpu-memory-utilization 0.9 \
  --max-model-len 4096 \
  --tensor-parallel-size 1
``````

**Port suggéré**: 8000 (ou 8001 si conflit)  
**API OpenAI-compatible**: http://localhost:8000/v1/

---

## 4. ARCHITECTURE CIBLE PROPOSÉE

### 4.1 Services GPU

| Service | GPU | VRAM | Port | Domain |
|---------|-----|------|------|--------|
| SD Forge | RTX 3080 (16GB) | ~12GB | 36525 | stable-diffusion-webui-forge.myia.io |
| SD Turbo | RTX 3080 (16GB) | ~8GB | 17861 | turbo.stable-diffusion-webui-forge.myia.io |
| Qwen Image-Edit | RTX 3090 (24GB) | ~4GB (AWQ) | 8000 | qwen-image-edit.myia.io |

### 4.2 Configuration IIS à créer

Nouveau site IIS pour Qwen:
``````xml
<configuration>
    <system.webServer>
        <rewrite>
            <rules>
                <rule name="ReverseProxy_Qwen" stopProcessing="true">
                    <match url="(.*)" />
                    <action type="Rewrite" url="http://localhost:8000/{R:1}" />
                </rule>
            </rules>
        </rewrite>
    </system.webServer>
</configuration>
``````

### 4.3 Docker Compose à créer

Nouveau service dans docker-compose ou fichier séparé:
``````yaml
services:
  qwen-image-edit:
    image: vllm/vllm-openai:latest
    container_name: qwen-image-edit
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['0']  # RTX 3090
              capabilities: [gpu]
    volumes:
      - /path/to/models:/models
    ports:
      - "8000:8000"
    command: >
      --model Qwen/Qwen2-VL-7B-Instruct-AWQ
      --gpu-memory-utilization 0.9
      --max-model-len 4096
    restart: unless-stopped
``````

---

## 5. ÉTAT CONTAINERS ACTUEL

"@

Write-Host "4. Vérification état containers Docker..." -ForegroundColor Yellow

# Tenter de vérifier via WSL si possible
$wslAvailable = $false
try {
    $wslCheck = wsl --list --quiet 2>&1
    if ($LASTEXITCODE -eq 0) {
        $wslAvailable = $true
        $report += @"

**Docker via WSL**: Disponible

"@
        
        # Essayer de récupérer les containers
        try {
            $dockerPs = wsl docker ps -a 2>&1
            if ($LASTEXITCODE -eq 0) {
                $report += @"
``````
$dockerPs
``````

"@
            }
        } catch {
            $report += "*Note*: Docker non accessible via WSL`n"
        }
    }
} catch {
    $report += "*Note*: WSL non accessible depuis ce contexte`n"
}

$report += @"

---

## 6. VOLUMES ET STOCKAGE

### 6.1 Volumes Docker identifiés

Selon docker-compose:
- **Workspace partagé**: ``\\wsl.localhost\Ubuntu\home\jesse\SD\workspace``
- Monté en `rshared` pour les deux services Forge
- Contient: models, outputs, configurations

### 6.2 Espace disque requis

**Pour Qwen Image-Edit**:
- Modèle AWQ: ~4GB
- Cache et outputs: ~10GB recommandé
- **Total estimé**: 15-20GB

**Vérification espace disponible**:
"@

Write-Host "5. Vérification espace disque..." -ForegroundColor Yellow

try {
    $wslDrive = Get-PSDrive | Where-Object { $_.Name -like "*wsl*" -or $_.Root -like "*Ubuntu*" }
    if ($wslDrive) {
        $report += "`n- Espace libre WSL: $([math]::Round($wslDrive.Free/1GB, 2))GB / $([math]::Round(($wslDrive.Used + $wslDrive.Free)/1GB, 2))GB`n"
    } else {
        $report += "`n*Note*: Espace WSL non mesurable directement depuis Windows`n"
    }
} catch {
    $report += "`n*Note*: Vérification espace à faire manuellement dans WSL`n"
}

$report += @"

---

## 7. PROBLÈMES IDENTIFIÉS

### 7.1 Containers arrêtés

D'après mission: "Containers avaient problèmes démarrage, fonctionnaient avant"

**Actions requises**:
1. Diagnostiquer logs des containers
2. Vérifier GPU allocation
3. Tester redémarrage avec docker-compose up

### 7.2 Conflits potentiels

- GPU 1 actuellement assigné à `myia-turbo` (Forge)
- Nécessite réaffectation pour Qwen Image-Edit
- Potentiel conflit de ports si plusieurs services

---

## 8. PLAN D'ACTION PHASES 10-14

### Phase 10: Diagnostic et Réparation Forge
- [ ] Analyser logs containers Forge
- [ ] Identifier causes problèmes démarrage
- [ ] Réparer configuration si nécessaire
- [ ] Valider fonctionnement Forge GPU 0

### Phase 11: Préparation Infrastructure Qwen
- [ ] Télécharger Qwen2-VL-7B-Instruct-AWQ
- [ ] Créer docker-compose pour vLLM
- [ ] Configurer GPU allocation (RTX 3090)
- [ ] Créer reverse proxy IIS

### Phase 12: Déploiement Qwen Image-Edit
- [ ] Lancer container vLLM + Qwen
- [ ] Tester API OpenAI-compatible
- [ ] Configurer certificat HTTPS
- [ ] Tests fonctionnels basiques

### Phase 13: Intégration et Tests
- [ ] Tests charge GPU
- [ ] Validation API endpoints
- [ ] Tests image editing
- [ ] Documentation API

### Phase 14: Validation Finale
- [ ] Tests end-to-end
- [ ] Performance benchmarks
- [ ] Documentation complète
- [ ] Handover et formation

---

## 9. RESSOURCES ET RÉFÉRENCES

### Documentation Qwen
- HuggingFace: https://huggingface.co/Qwen/Qwen2-VL-7B-Instruct
- GitHub: https://github.com/QwenLM/Qwen2-VL
- AWQ Quantization: https://huggingface.co/Qwen/Qwen2-VL-7B-Instruct-AWQ

### Documentation vLLM
- Docs: https://docs.vllm.ai/
- OpenAI API: https://docs.vllm.ai/en/latest/serving/openai_compatible_server.html
- Vision Models: https://docs.vllm.ai/en/latest/models/vlm.html

### Infrastructure existante
- Forge Docker: https://github.com/ai-dock/stable-diffusion-webui-forge
- IIS Reverse Proxy: Docs Microsoft ARR

---

## 10. CHECKPOINTS SÉMANTIQUES

### Checkpoint 1: Infrastructure Forge ✓
- Configuration Docker Compose analysée
- Reverse proxies IIS identifiés
- Volumes et modèles listés
- GPU allocation comprise

### Checkpoint 2: Requirements Qwen (En cours)
- Modèle identifié: Qwen2-VL-7B-Instruct
- Quantization: AWQ 4-bit recommandé
- Déploiement: vLLM recommandé
- VRAM: ~4GB (laisse 20GB libres)

### Checkpoint 3: Architecture cible (En cours)
- 2 GPUs, 3 services
- Ports: 36525, 17861, 8000
- APIs OpenAI-compatible pour les 2 services
- IIS reverse proxy avec HTTPS

---

## 11. DÉCISIONS TECHNIQUES

| Décision | Justification |
|----------|---------------|
| vLLM pour Qwen | API OpenAI-compatible native, performance optimale |
| AWQ quantization | Meilleur ratio qualité/VRAM (4GB) |
| GPU 0 → Forge | VRAM suffisant pour SD XL (16GB) |
| GPU 1 → Qwen | VRAM optimal pour VLM (24GB) |
| Port 8000 | Standard vLLM, pas de conflit |
| IIS ARR | Cohérent avec infrastructure existante |

---

**Fin du rapport Phase 9**

*Prochaine étape*: Phase 10 - Diagnostic et réparation containers Forge
"@

# Sauvegarder le rapport
$report | Out-File -FilePath $reportPath -Encoding UTF8

Write-Host ""
Write-Host "=== Investigation terminée ===" -ForegroundColor Green
Write-Host "Rapport sauvegardé: $reportPath" -ForegroundColor Cyan
Write-Host ""
Write-Host "Résumé des découvertes:" -ForegroundColor Yellow
Write-Host "- Infrastructure Forge: 2 services (GPU 0 et 1)" -ForegroundColor White
Write-Host "- Ports: 36525 (Forge) et 17861 (Turbo)" -ForegroundColor White
Write-Host "- Workspace WSL: $wslWorkspace" -ForegroundColor White
Write-Host "- Target: RTX 3090 (24GB) pour Qwen Image-Edit" -ForegroundColor White
Write-Host "- Recommandation: vLLM + AWQ quantization" -ForegroundColor White
Write-Host ""