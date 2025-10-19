# Grounding Sémantique Initial - Phase 14B
**Date**: 2025-10-16  
**Phase**: 14B - Tests Exhaustifs 2 APIs GenAI  
**Méthode**: SDDD (Semantic-Documentation-Driven-Design)

---

## 🎯 Objectif

Documenter les découvertes issues des **3 recherches sémantiques initiales** pour établir les patterns de tests à utiliser pour valider les APIs Qwen et SD XL Turbo en production.

---

## 📚 Recherche 1: Tests Infrastructure Existants

### Query
`"ComfyUI API Qwen tests validation production endpoints infrastructure"`

### Découvertes Clés

#### Client ComfyUI Production
- **Fichier**: [`MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py`](../../../MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py)
- **Status**: Production Ready
- **Utilisation**: Base pour tests Python

#### Tests Validation Phase 12B
- **Rapport**: [`phase-12-production/rapports/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md`](../phase-12-production/rapports/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md)
- **Script**: [`phase-12b-tests/scripts/2025-10-16_12B_test-generation-comfyui.ps1`](../phase-12b-tests/scripts/2025-10-16_12B_test-generation-comfyui.ps1)
- **Patterns identifiés**:
  - Logging structuré avec niveaux (INFO, ERROR, SUCCESS, WARNING)
  - Tests accessibilité via `Invoke-WebRequest`
  - Mesure performance avec stats GPU
  - Gestion timeouts pour générations
  - Sauvegarde logs/outputs structurée

#### Configuration Production
- **API Qwen**: `https://qwen-image-edit.myia.io`
- **Endpoints critiques**:
  - `/system_stats` - Health check + stats GPU
  - `/queue` - File d'attente jobs
  - `/object_info` - Nodes disponibles
  - `/prompt` - Soumission workflows

#### Patterns Tests PowerShell
```powershell
# Structure standard découverte
param([string]$BaseUrl, [switch]$VerboseOutput)

# Logging avec niveaux
function Write-TestLog {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    # Couleurs selon niveau + sauvegarde fichier
}

# Tests avec try-catch
try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/endpoint" -TimeoutSec 10
    # Validation + logging succès
} catch {
    # Logging erreur + détails
}
```

---

## 🔍 Recherche 2: API Forge et Tests

### Query
`"Stable Diffusion Forge API REST text-to-image generation validation tests PowerShell"`

### Découvertes Clés

#### API Forge Endpoints (Automatic1111 Compatible)
- **Base URL**: `https://turbo.stable-diffusion-webui-forge.myia.io`
- **Endpoints critiques**:
  - `/` - Health check (page accueil)
  - `/sdapi/v1/sd-models` - Liste modèles disponibles
  - `/sdapi/v1/samplers` - Liste samplers
  - `/sdapi/v1/txt2img` - Génération text-to-image

#### Format Requêtes txt2img
```json
{
  "prompt": "description",
  "negative_prompt": "what to avoid",
  "steps": 4,  // Turbo = 4 steps
  "width": 512,
  "height": 512,
  "cfg_scale": 2.0,  // Turbo = low CFG
  "sampler_name": "DPM++ SDE"
}
```

#### Patterns Validation Existants
- Tests endpoints multiples en séquence
- Validation codes HTTP 200
- Mesure temps réponse
- Tests génération avec payload simple
- Rapport markdown automatisé

---

## 📋 Recherche 3: Patterns Scripts PowerShell

### Query
`"Phase 12B tests validation ComfyUI production websocket rapport test generation"`

### Script Référence Analysé
**Fichier**: [`phase-12b-tests/scripts/2025-10-16_12B_test-generation-comfyui.ps1`](../phase-12b-tests/scripts/2025-10-16_12B_test-generation-comfyui.ps1)

### Bonnes Pratiques Identifiées

#### 1. Structure Fichier
```powershell
# En-tête descriptif
# Phase, Date, Objectif

# Paramètres avec valeurs par défaut
param(
    [string]$BaseUrl = "https://...",
    [switch]$VerboseOutput
)

# Configuration chemins
$REPORTS_DIR = "..."
$LOGS_DIR = "..."

# Création répertoires
New-Item -ItemType Directory -Path $X -Force | Out-Null
```

#### 2. Fonction Logging Standard
- Timestamp ISO format
- Niveau codé couleur
- Sauvegarde fichier log
- Support verbose conditionnel

#### 3. Tests Hiérarchisés
1. **Test préliminaire**: Accessibilité service
2. **Tests endpoints**: Validation APIs
3. **Tests fonctionnels**: Génération complète
4. **Stats performance**: Mesures quantitatives

#### 4. Gestion Erreurs Robuste
- Try-catch sur chaque test
- Logging détaillé erreurs
- Exit codes appropriés
- Continue after non-critical failures

#### 5. Rapport Automatisé
- Markdown structuré
- Sections clairement séparées
- Statistiques calculées
- Conclusions exploitables

---

## 🎨 Architecture Tests Phase 14B

### Tests Qwen API (ComfyUI)
```
1. Health Check (/system_stats)
   - Vérifier 200 OK
   - Extraire stats GPU (RTX 3090, VRAM)
   
2. Queue Endpoint (/queue)
   - Vérifier accessibilité
   - Compter jobs pending/running
   
3. Object Info (/object_info)
   - Vérifier nodes disponibles
   - Compter nodes Qwen
   
4. Génération Test (/prompt)
   - Workflow minimal (256x256)
   - Vérifier prompt_id retourné
   - Note: Ne pas attendre complétion
```

### Tests SD XL Turbo (Forge)
```
1. Health Check (/)
   - Vérifier page accueil 200 OK
   
2. Models Endpoint (/sdapi/v1/sd-models)
   - Lister modèles disponibles
   - Chercher modèle Turbo
   
3. Samplers Endpoint (/sdapi/v1/samplers)
   - Lister samplers disponibles
   - Compter total
   
4. Génération Test (/sdapi/v1/txt2img)
   - Payload Turbo (4 steps, CFG 2.0)
   - Dimensions 256x256
   - Vérifier images générées
```

---

## 📊 Métriques à Collecter

### Pour Chaque API
- ✅ Health check status (OK/FAIL)
- ✅ Endpoints fonctionnels (X/4)
- ✅ Temps réponse moyen
- ✅ Erreurs critiques rencontrées
- ✅ Status final (OPERATIONAL/DEGRADED/DOWN)

### Format Rapport
```markdown
## ✅ Test X: Nom Test
- **Status**: SUCCESS/FAILURE
- **Code HTTP**: 200 OK / Error
- **Détails**: [métriques spécifiques]
- **Temps réponse**: Xs (optionnel)
```

---

## 🔄 Adaptations Nécessaires

### Par rapport aux tests Phase 12B

1. **Pas de WSL nvidia-smi**
   - APIs distantes (myia.io)
   - Stats GPU via endpoints APIs seulement

2. **Pas d'attente génération complète**
   - Tests validation endpoints uniquement
   - Génération test = vérification queuing

3. **2 APIs différentes**
   - Qwen = ComfyUI (workflow JSON complexe)
   - SD XL Turbo = Forge (payload simple REST)

4. **URLs production**
   - HTTPS avec certificats valides
   - Pas de localhost

---

## ✅ Validation Grounding

### Documents Pertinents Identifiés
- [x] Client ComfyUI production
- [x] Script tests Phase 12B
- [x] Rapport final Phase 12B
- [x] Documentation API Forge
- [x] Patterns PowerShell infrastructure

### Patterns Réutilisables
- [x] Structure logging standardisée
- [x] Hiérarchie tests (health → endpoints → functional)
- [x] Rapport markdown automatique
- [x] Gestion erreurs robuste
- [x] Paramètres configurables

### Gaps Identifiés
- [ ] Documentation API Forge spécifique CoursIA
- [ ] Credentials SD XL Turbo (mentionnés dans guide étudiants)
- [ ] Benchmarks performance attendus

---

## 📝 Implications pour Phase 14B

### Scripts à Créer

1. **`2025-10-16_01_test-qwen-api.ps1`**
   - 4 tests endpoints ComfyUI
   - Workflow Qwen minimal
   - Rapport markdown automatique

2. **`2025-10-16_02_test-sdxl-turbo-api.ps1`**
   - 4 tests endpoints Forge
   - Payload txt2img Turbo
   - Rapport markdown automatique

### Structure Répertoires
```
phase-14b-tests-apis/
├── scripts/
│   ├── 2025-10-16_01_test-qwen-api.ps1
│   └── 2025-10-16_02_test-sdxl-turbo-api.ps1
├── rapports/
│   ├── 2025-10-16_14B_rapport-test-qwen-api.md
│   └── 2025-10-16_14B_rapport-test-sdxl-turbo-api.md
└── 2025-10-16_14B_01_grounding-semantique-initial.md (ce fichier)
```

---

## 🎯 Prochaines Étapes

1. ✅ Grounding sémantique initial (TERMINÉ)
2. ⏳ Grounding conversationnel (via roo-state-manager)
3. ⏳ Création scripts tests
4. ⏳ Exécution et validation
5. ⏳ Documentation finale

---

**Synthèse**: Le grounding sémantique a permis d'identifier tous les patterns nécessaires pour créer des tests robustes et documentés des 2 APIs GenAI en production. Les scripts Phase 12B fournissent une base solide à adapter pour Phase 14B.

*Document généré automatiquement - Phase 14B SDDD*