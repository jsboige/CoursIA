# Checkpoint 1: Contexte Workflows ComfyUI + Qwen

**Date**: 2025-10-16  
**Phase**: 12B - Tests End-to-End Génération Images  
**Objectif**: Documenter workflows disponibles et nodes Qwen avant tests

---

## 📚 Résultats Recherches Sémantiques

### Recherche 1: Workflows ComfyUI Basiques

**Query**: `"ComfyUI workflows default basic image generation text-to-image checkpoint KSampler"`

**Résultats Clés**:

#### Structure JSON Workflow Standard

```json
{
  "prompt": {
    "3": {  // Node KSampler
      "inputs": {
        "seed": 42,
        "steps": 20,
        "cfg": 7.0,
        "sampler_name": "euler",
        "scheduler": "normal",
        "denoise": 1.0,
        "model": ["4", 0],
        "positive": ["6", 0],
        "negative": ["7", 0],
        "latent_image": ["5", 0]
      },
      "class_type": "KSampler"
    },
    "4": {  // Node CheckpointLoader
      "inputs": {
        "ckpt_name": "model.safetensors"
      },
      "class_type": "CheckpointLoaderSimple"
    },
    "5": {  // Node EmptyLatentImage
      "inputs": {
        "width": 512,
        "height": 512,
        "batch_size": 1
      },
      "class_type": "EmptyLatentImage"
    },
    "6": {  // Node CLIP Positive
      "inputs": {
        "text": "prompt positif",
        "clip": ["4", 1]
      },
      "class_type": "CLIPTextEncode"
    },
    "7": {  // Node CLIP Negative
      "inputs": {
        "text": "prompt négatif",
        "clip": ["4", 1]
      },
      "class_type": "CLIPTextEncode"
    },
    "8": {  // Node VAEDecode
      "inputs": {
        "samples": ["3", 0],
        "vae": ["4", 2]
      },
      "class_type": "VAEDecode"
    },
    "9": {  // Node SaveImage
      "inputs": {
        "filename_prefix": "ComfyUI",
        "images": ["8", 0]
      },
      "class_type": "SaveImage"
    }
  }
}
```

#### Nodes Essentiels Identifiés

1. **CheckpointLoaderSimple**: Charge le modèle principal
2. **CLIPTextEncode**: Encode prompts texte (positif/négatif)
3. **EmptyLatentImage**: Crée latent initial pour génération
4. **KSampler**: Processus de diffusion principal
5. **VAEDecode**: Décode latent vers image
6. **SaveImage**: Sauvegarde résultat

#### Exemples Workflows Trouvés

- **basic-text-to-image**: Génération simple depuis prompt
- **style-transfer**: Transfert de style entre images
- **multi-model-comparison**: Comparaison FLUX vs SD3.5

---

### Recherche 2: Custom Nodes Qwen Spécifiques

**Query**: `"Qwen Image Edit custom nodes workflows image-to-image editing QwenVL QwenImageWanBridge"`

**Résultats Clés**:

#### 28 Custom Nodes Qwen Détectés

Liste complète des nodes disponibles:

1. **ModelMergeQwenImage** - Fusion modèles Qwen
2. **TextEncodeQwenImageEdit** - Encodage texte pour édition
3. **TextEncodeQwenImageEditPlus** - Encodage avancé
4. **QwenImageDiffsynthControlnet** - ControlNet Qwen
5. **QwenVLCLIPLoader** - Chargeur CLIP VL
6. **QwenVLTextEncoder** - Encodeur texte VL
7. **QwenLowresFixNode** - Amélioration résolution
8. **QwenVLTextEncoderAdvanced** - Encodage avancé
9. **QwenVLEmptyLatent** - Latent vide VL
10. **QwenVLImageToLatent** - Conversion image→latent
11. **QwenTemplateBuilder** - Construction templates
12. **QwenTemplateConnector** - Connexion templates
13. **QwenEliGenEntityControl** - Contrôle entités
14. **QwenEliGenMaskPainter** - Peinture masques
15. **QwenTokenDebugger** - Debug tokens
16. **QwenTokenAnalyzer** - Analyse tokens
17. **QwenSpatialTokenGenerator** - Génération tokens spatiaux
18. **QwenImageDiTLoaderWrapper** - Wrapper DiT
19. **QwenVLTextEncoderLoaderWrapper** - Wrapper encoder
20. **QwenImageVAELoaderWrapper** - Wrapper VAE
21. **QwenModelManagerWrapper** - Gestionnaire modèles
22. **QwenImageSamplerNode** - Sampler Qwen
23. **QwenProcessorWrapper** - Wrapper processeur
24. **QwenProcessedToEmbedding** - Conversion embeddings
25. **QwenImageEncodeWrapper** - Wrapper encodage
26. **QwenImageModelWithEdit** - Modèle avec édition
27. **QwenImageSamplerWithEdit** - Sampler avec édition
28. **QwenDebugLatents** - Debug latents

#### Fonctionnalités Supportées

Selon documentation Phase 11/12A:

- **Image Generation**: Génération depuis texte
- **Image-to-Image**: Transformation images existantes
- **Multi-Image Editing**: Édition 1-3 images simultanément
- **Pose Transfer**: Transfert pose entre images
- **Style Transfer**: Application styles
- **Text-Guided Editing**: Édition guidée par texte
- **ControlNet Integration**: Génération guidée

#### Custom Node Source

- **Repository**: `gokayfem/ComfyUI-QwenImageWanBridge`
- **Installation**: Déjà installé dans `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/`
- **Statut**: ✅ Chargé et validé (Phase 12A)

---

### Recherche 3: Patterns Test Automatisé

**Query**: `"Playwright automation testing ComfyUI API image generation validation WebSocket queue prompt"`

**Résultats Clés**:

#### Scripts PowerShell Existants

1. **`2025-10-16_07_validation-finale-autonome.ps1`**:
   - Tests WebSocket validation
   - Tests génération image
   - Tests custom nodes
   - Utilise API REST ComfyUI

2. **`2025-10-16_01_test-websocket-comfyui.ps1`**:
   - Validation connexion WebSocket
   - Tests console logs
   - Vérification erreurs

3. **`2025-10-15_13_test-playwright-ui.ps1`**:
   - Installation Playwright
   - Capture screenshots
   - Tests UI automatisés

#### Méthodes d'Attente Génération

**Pattern identifié** (polling status):

```powershell
$promptId = $response.prompt_id
$maxWait = 120  # seconds
$waited = 0
$completed = $false

while ($waited -lt $maxWait -and -not $completed) {
    Start-Sleep -Seconds 5
    $waited += 5
    
    # Vérifier status via history
    $history = Invoke-RestMethod -Uri "$COMFYUI_URL/history/$promptId"
    if ($history.$promptId.status.completed -eq $true) {
        $completed = $true
    }
}
```

#### Validation Résultats

**Métriques à capturer**:
- Temps génération (secondes)
- VRAM utilisée (MB)
- Température GPU (°C)
- Status HTTP réponses
- Présence erreurs logs

#### Endpoints API ComfyUI

- **`/system_stats`**: État système/GPU
- **`/prompt`**: Soumettre workflow (POST)
- **`/history/{prompt_id}`**: Status génération
- **`/queue`**: File d'attente
- **`/object_info`**: Nodes disponibles

---

## 🎯 Workflows à Tester (Phase 12B)

### Test 1: Génération Image Simple ✅ PRIORITÉ

**Objectif**: Valider génération basique text-to-image

**Workflow**:
```json
{
  "prompt": {
    "checkpoint": "Qwen-Image-Edit-2509-FP8/diffusion_pytorch_model.safetensors",
    "positive_prompt": "A beautiful mountain landscape at sunset with vibrant colors",
    "negative_prompt": "blurry, low quality, watermark",
    "width": 512,
    "height": 512,
    "steps": 20,
    "cfg_scale": 7.0,
    "seed": 42,
    "sampler": "euler",
    "scheduler": "normal"
  }
}
```

**Métriques Attendues**:
- Temps génération: <10s
- VRAM: 12-18 GB (50-75%)
- Température: <80°C
- Résultat: Image 512x512 générée

**Validation**:
- ✅ HTTP 200 response
- ✅ Image file créé
- ✅ Pas d'erreurs logs

---

### Test 2: QwenVL Description Image

**Objectif**: Tester node QwenVLTextEncoder pour analyse image

**Workflow Conceptuel**:
```json
{
  "workflow": {
    "nodes": [
      {
        "type": "LoadImage",
        "inputs": {"image": "test.png"}
      },
      {
        "type": "QwenVLCLIPLoader",
        "inputs": {"model": "Qwen-Image-Edit-2509-FP8"}
      },
      {
        "type": "QwenVLTextEncoder",
        "inputs": {
          "image": "node1_output",
          "clip": "node2_output",
          "mode": "description"
        }
      }
    ]
  }
}
```

**Output Attendu**: Description textuelle détaillée de l'image

**Validation**:
- ✅ Description générée
- ✅ Cohérence avec image input
- ✅ Longueur raisonnable (50-200 mots)

---

### Test 3: QwenImageEdit Édition Guidée

**Objectif**: Tester édition image avec prompt

**Workflow Conceptuel**:
```json
{
  "workflow": {
    "nodes": [
      {
        "type": "LoadImage",
        "inputs": {"image": "source.png"}
      },
      {
        "type": "QwenImageModelWithEdit",
        "inputs": {"model": "Qwen-Image-Edit-2509-FP8"}
      },
      {
        "type": "TextEncodeQwenImageEditPlus",
        "inputs": {
          "text": "Change the sky to a dramatic sunset",
          "clip": "node2_output"
        }
      },
      {
        "type": "QwenImageSamplerWithEdit",
        "inputs": {
          "model": "node2_output",
          "conditioning": "node3_output",
          "image": "node1_output",
          "steps": 25,
          "cfg": 7.5
        }
      }
    ]
  }
}
```

**Output Attendu**: Image éditée avec ciel modifié

**Validation**:
- ✅ Édition appliquée visuellement
- ✅ Reste de l'image préservé
- ✅ Qualité satisfaisante

---

## 📊 Infrastructure Disponible (Phase 12A ✅)

### Backend ComfyUI

- **URL Local**: http://localhost:8188
- **URL Production**: https://qwen-image-edit.myia.io
- **GPU**: NVIDIA RTX 3090 (24GB VRAM)
- **Version**: ComfyUI v0.3.664
- **Modèle**: Qwen-Image-Edit-2509-FP8 (54GB)
- **Custom Nodes**: 28 nodes Qwen chargés

### Métriques Baseline

- **VRAM Idle**: 1.3 GB / 24 GB (5.2%)
- **Température Idle**: 28°C
- **Temps Démarrage**: 10-15 secondes
- **WebSocket**: ✅ Fonctionnel (corrigé Phase 12A)

### Endpoints API Validés

- ✅ `/system_stats` - Statistiques système
- ✅ `/queue` - File d'attente
- ✅ `/prompt` - Soumettre workflow
- ✅ `/history` - Historique générations
- ✅ `/object_info` - Liste nodes disponibles

---

## 🔧 Outils Disponibles pour Tests

### Scripts PowerShell

1. **GPU Monitoring**:
   ```powershell
   wsl nvidia-smi --query-gpu=memory.used,memory.total,temperature.gpu,utilization.gpu --format=csv,noheader,nounits -i 1
   ```

2. **API Tests**:
   ```powershell
   Invoke-RestMethod -Uri "https://qwen-image-edit.myia.io/system_stats"
   ```

3. **Workflow Submission**:
   ```powershell
   $workflow = @{prompt = @{...}} | ConvertTo-Json -Depth 10
   Invoke-RestMethod -Uri "https://qwen-image-edit.myia.io/prompt" -Method POST -Body $workflow -ContentType "application/json"
   ```

### MCP Playwright (Optionnel)

- **Installation**: MCP disponible pour tests UI
- **Capabilities**: Navigation, screenshots, validation visuelle
- **Usage**: Tests manuels interactifs si nécessaire

---

## ✅ Prêt pour Exécution Tests

**Contexte Documenté**:
- ✅ Structure workflows JSON
- ✅ 28 custom nodes Qwen identifiés
- ✅ Patterns test automatisé analysés
- ✅ Infrastructure validée (Phase 12A)
- ✅ Scripts exemples disponibles

**Prochaines Étapes**:
1. Créer script test PowerShell complet
2. Exécuter Test 1 (génération simple)
3. Capturer métriques performance
4. Documenter résultats
5. Tests 2 & 3 si workflow disponibles

---

**Checkpoint 1 Complété**: 2025-10-16  
**Status**: ✅ READY FOR TESTING  
**Next**: Créer `2025-10-16_12B_test-generation-playwright.ps1`