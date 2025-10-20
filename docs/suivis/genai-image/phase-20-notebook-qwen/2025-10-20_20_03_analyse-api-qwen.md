# Analyse API Qwen-Image-Edit - Phase 20

**Date**: 2025-10-20  
**Objectif**: Extraction endpoints, paramètres et workflows pour notebook pédagogique  
**Sources**: GUIDE-APIS-ETUDIANTS.md + 12C_architectures-5-workflows-qwen.md

---

## 🎯 Informations API Production

### Accès Service

| Paramètre | Valeur | Notes |
|-----------|--------|-------|
| **URL Production** | `https://qwen-image-edit.myia.io` | Service déployé Phase 12 |
| **Port API** | 8188 | WebSocket ComfyUI standard |
| **Architecture** | ComfyUI + vLLM | Backend ComfyUI natif |
| **GPU** | RTX 3090 (24GB VRAM) | GPU 2 dédié (GPU 1 = Turbo) |
| **Modèle** | Qwen-Image-Edit-2509-FP8 | 54GB quantifié FP8 |
| **Authentication** | None | Interne réseau CoursIA |

### Endpoints ComfyUI Critiques

**Documentation complète**: [ComfyUI API Docs](https://github.com/comfyanonymous/ComfyUI/wiki/API)

| Endpoint | Méthode | Usage | Essentiel Notebook |
|----------|---------|-------|-------------------|
| `/prompt` | POST | Soumettre workflow → Récupérer `prompt_id` | ✅ OUI |
| `/history/{prompt_id}` | GET | Récupérer résultats génération | ✅ OUI |
| `/upload/image` | POST | Upload image source (I2I) | ⚠️ I2I seulement |
| `/ws` | WebSocket | Streaming progression temps réel | ❌ Avancé |
| `/queue` | GET | État queue génération | ❌ Optionnel |

---

## 📊 Pattern API ComfyUI (vs Forge)

### Comparaison Architecture

**Forge (Simple)**: 1 requête synchrone
```python
response = requests.post(
    "https://turbo.forge.myia.io/sdapi/v1/txt2img",
    json={"prompt": "...", "steps": 4}
)
image = Image.open(BytesIO(base64.b64decode(response.json()["images"][0])))
```

**ComfyUI (Queue + Poll)**: 2 requêtes asynchrones
```python
# 1. Queue workflow
response = requests.post(
    "https://qwen-image-edit.myia.io/prompt",
    json={"prompt": workflow_json, "client_id": "client123"}
)
prompt_id = response.json()["prompt_id"]

# 2. Poll résultat (boucle)
while True:
    response = requests.get(f"https://qwen-image-edit.myia.io/history/{prompt_id}")
    result = response.json()
    if prompt_id in result and "outputs" in result[prompt_id]:
        # Résultat disponible
        break
    time.sleep(1)  # Attente polling
```

### Différence Clef: Workflow JSON

**Forge**: Paramètres clé-valeur simples
```json
{"prompt": "text", "steps": 20, "cfg_scale": 7.5}
```

**ComfyUI**: Graph JSON complet (nodes + connexions)
```json
{
  "1": {"class_type": "QwenVLCLIPLoader", "inputs": {"model_path": "..."}},
  "2": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"text": "...", "clip": ["1", 0]}},
  "5": {"class_type": "QwenImageSamplerNode", "inputs": {"steps": 20, "transformer": ["1", 1], ...}}
}
```

---

## 🏗️ Workflows JSON Pédagogiques

### Workflow 1: Text-to-Image Basique (Débutant)

**Objectif**: Génération image simple depuis texte  
**VRAM**: 12-15GB  
**Temps**: 5-10s  
**Nodes**: 7

#### Architecture JSON Complète

```json
{
  "1": {
    "class_type": "QwenVLCLIPLoader",
    "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"}
  },
  "2": {
    "class_type": "TextEncodeQwenImageEdit",
    "inputs": {
      "text": "A beautiful mountain landscape at sunset, highly detailed, 8k",
      "clip": ["1", 0]
    }
  },
  "3": {
    "class_type": "TextEncodeQwenImageEdit",
    "inputs": {
      "text": "blurry, low quality, watermark",
      "clip": ["1", 0]
    }
  },
  "4": {
    "class_type": "QwenVLEmptyLatent",
    "inputs": {"width": 512, "height": 512, "batch_size": 1}
  },
  "5": {
    "class_type": "QwenImageSamplerNode",
    "inputs": {
      "seed": 42,
      "steps": 20,
      "cfg": 7.0,
      "sampler_name": "euler_ancestral",
      "scheduler": "normal",
      "transformer": ["1", 1],
      "positive": ["2", 0],
      "negative": ["3", 0],
      "latent_image": ["4", 0]
    }
  },
  "6": {
    "class_type": "VAEDecode",
    "inputs": {
      "samples": ["5", 0],
      "vae": ["1", 2]
    }
  },
  "7": {
    "class_type": "SaveImage",
    "inputs": {
      "filename_prefix": "Qwen_T2I",
      "images": ["6", 0]
    }
  }
}
```

#### Paramètres Pédagogiques Clés

| Paramètre | Plage | Recommandé | Impact Pédagogique |
|-----------|-------|------------|-------------------|
| `steps` | 1-50 | 20 | **Exercice 1**: Comparer 10/20/30 steps |
| `cfg` | 1-20 | 7.0 | **Exercice 2**: Tester 5/7/10/15 |
| `width/height` | 256-2048 | 512 | **Exercice 3**: Impact VRAM |
| `seed` | -1 ou int | 42 | **Exercice 4**: Reproductibilité |

---

### Workflow 2: Image-to-Image Editing (Intermédiaire)

**Objectif**: Édition image existante guidée texte  
**VRAM**: 15-18GB  
**Temps**: 8-12s  
**Nodes**: 9

#### Architecture JSON Condensée

```json
{
  "1": {"class_type": "LoadImage", "inputs": {"image": "source.png"}},
  "2": {"class_type": "QwenVLCLIPLoader", "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"}},
  "3": {"class_type": "QwenVLImageToLatent", "inputs": {"image": ["1", 0], "vae": ["2", 2]}},
  "4": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"text": "Change sky to sunset", "clip": ["2", 0]}},
  "5": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"text": "blurry, distorted", "clip": ["2", 0]}},
  "6": {
    "class_type": "QwenImageSamplerWithEdit",
    "inputs": {
      "seed": 42,
      "steps": 25,
      "cfg": 7.5,
      "denoise": 0.6,
      "edit_strength": 0.75,
      "transformer": ["2", 1],
      "positive": ["4", 0],
      "negative": ["5", 0],
      "image": ["3", 0]
    }
  },
  "7": {"class_type": "VAEDecode", "inputs": {"samples": ["6", 0], "vae": ["2", 2]}},
  "8": {"class_type": "SaveImage", "inputs": {"filename_prefix": "Qwen_I2I", "images": ["7", 0]}}
}
```

#### Paramètres Critiques I2I

| Paramètre | Plage | Recommandé | Usage Pédagogique |
|-----------|-------|------------|-------------------|
| `denoise` | 0.0-1.0 | 0.6 | **Exercice 5**: 0.3 (subtil) vs 0.8 (fort) |
| `edit_strength` | 0.0-1.0 | 0.75 | **Exercice 6**: Force transformation |
| `steps` | 1-50 | 25 | Plus élevé que T2I pour précision |

---

## 🐍 Client Python Pédagogique

### Fonction Helper Principale (À inclure Notebook)

```python
import requests
import json
import time
from PIL import Image
from io import BytesIO
import base64

class ComfyUIClient:
    """Client pédagogique pour API ComfyUI Qwen"""
    
    def __init__(self, base_url="https://qwen-image-edit.myia.io"):
        self.base_url = base_url
        self.client_id = "notebook_student"
    
    def execute_workflow(self, workflow_json, wait_for_completion=True, max_wait=60):
        """
        Exécute workflow ComfyUI et attend résultat
        
        Args:
            workflow_json (dict): Workflow JSON ComfyUI
            wait_for_completion (bool): Attendre fin génération
            max_wait (int): Timeout secondes
        
        Returns:
            dict: Résultat avec images générées
        """
        # 1. Queue workflow
        payload = {
            "prompt": workflow_json,
            "client_id": self.client_id
        }
        
        response = requests.post(
            f"{self.base_url}/prompt",
            json=payload,
            timeout=30
        )
        
        if response.status_code != 200:
            raise Exception(f"Erreur queue: {response.status_code}")
        
        prompt_id = response.json()["prompt_id"]
        print(f"✅ Workflow queued: {prompt_id}")
        
        if not wait_for_completion:
            return {"prompt_id": prompt_id, "status": "queued"}
        
        # 2. Poll résultat
        start_time = time.time()
        
        while True:
            # Timeout check
            if time.time() - start_time > max_wait:
                raise TimeoutError(f"Timeout après {max_wait}s")
            
            # Récupérer historique
            response = requests.get(
                f"{self.base_url}/history/{prompt_id}",
                timeout=10
            )
            
            result = response.json()
            
            # Vérifier si terminé
            if prompt_id in result:
                task = result[prompt_id]
                
                if "outputs" in task:
                    print(f"✅ Génération terminée en {time.time() - start_time:.1f}s")
                    return self._extract_images(task["outputs"])
            
            # Attendre avant re-poll
            time.sleep(1)
            print("⏳ Génération en cours...")
    
    def _extract_images(self, outputs):
        """Extrait images depuis outputs ComfyUI"""
        images = []
        
        for node_id, output in outputs.items():
            if "images" in output:
                for img_data in output["images"]:
                    # Récupérer image depuis serveur
                    img_url = f"{self.base_url}/view?filename={img_data['filename']}"
                    response = requests.get(img_url)
                    
                    image = Image.open(BytesIO(response.content))
                    images.append(image)
        
        return {"images": images, "count": len(images)}
```

### Utilisation Pédagogique Étape par Étape

```python
# Cellule 1: Imports + Configuration
import sys
sys.path.insert(0, '../shared/helpers')  # Ajuster selon structure
from comfyui_client import ComfyUIClient

# Connexion service
client = ComfyUIClient("https://qwen-image-edit.myia.io")

# Cellule 2: Workflow T2I Simple
workflow_hello = {
    "1": {"class_type": "QwenVLCLIPLoader", "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"}},
    "2": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"text": "A cute cat", "clip": ["1", 0]}},
    "3": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"text": "blurry", "clip": ["1", 0]}},
    "4": {"class_type": "QwenVLEmptyLatent", "inputs": {"width": 512, "height": 512, "batch_size": 1}},
    "5": {"class_type": "QwenImageSamplerNode", "inputs": {
        "seed": 42, "steps": 20, "cfg": 7.0,
        "sampler_name": "euler_ancestral", "scheduler": "normal",
        "transformer": ["1", 1], "positive": ["2", 0], "negative": ["3", 0], "latent_image": ["4", 0]
    }},
    "6": {"class_type": "VAEDecode", "inputs": {"samples": ["5", 0], "vae": ["1", 2]}},
    "7": {"class_type": "SaveImage", "inputs": {"filename_prefix": "cat", "images": ["6", 0]}}
}

# Exécution
result = client.execute_workflow(workflow_hello)

# Affichage
import matplotlib.pyplot as plt
plt.figure(figsize=(8, 8))
plt.imshow(result["images"][0])
plt.axis("off")
plt.title("Mon premier chat Qwen!")
plt.show()
```

---

## 📚 Paramètres Recommandés Par Cas Usage

### Génération Text-to-Image

| Qualité | steps | cfg | VRAM | Temps |
|---------|-------|-----|------|-------|
| **Rapide** | 15 | 6.0 | 10GB | 3-5s |
| **Standard** | 20 | 7.0 | 12GB | 5-10s |
| **Qualité Max** | 30 | 7.5 | 15GB | 10-15s |

### Édition Image-to-Image

| Force Édition | denoise | edit_strength | steps | Usage |
|---------------|---------|---------------|-------|-------|
| **Subtile** | 0.3 | 0.5 | 20 | Correction couleurs |
| **Équilibrée** | 0.6 | 0.75 | 25 | Changement ciel |
| **Forte** | 0.8 | 1.0 | 30 | Transformation style |

### Résolutions Optimales RTX 3090

| Résolution | VRAM | Recommandation |
|------------|------|----------------|
| 384x384 | 8GB | Prototypage rapide |
| 512x512 | 12GB | **Optimal pédagogique** ✅ |
| 768x768 | 18GB | Qualité standard |
| 1024x1024 | 22GB | Maximum RTX 3090 |
| 2048x2048 | ⚠️ OOM | Impossible RTX 3090 |

---

## 🎯 Checklist Implémentation Notebook

### Éléments Techniques Essentiels

- [ ] Client ComfyUI avec queue + poll
- [ ] Workflow T2I JSON complet
- [ ] Workflow I2I JSON complet
- [ ] Fonction helper extraction images
- [ ] Gestion erreurs API (timeout, OOM)
- [ ] Affichage matplotlib images

### Éléments Pédagogiques

- [ ] Explication pattern "queue and poll"
- [ ] Comparaison Forge vs ComfyUI
- [ ] Exercices variations paramètres
- [ ] Visualisation impact steps/cfg
- [ ] Troubleshooting CUDA OOM
- [ ] Bonnes pratiques prompts

### Workflows Progressifs

1. **Débutant**: T2I simple (chat, paysage)
2. **Intermédiaire**: Variation prompts (styles multiples)
3. **Avancé**: I2I édition (changement ciel)
4. **Expert**: Comparaison paramètres (grid visualisation)

---

## 🐛 Troubleshooting API

### Erreur: Connection Timeout

**Symptôme**: `requests.exceptions.Timeout`

**Solutions**:
```python
# Augmenter timeout
client = ComfyUIClient(timeout=60)

# Ou dans requests
response = requests.post(url, json=payload, timeout=60)
```

### Erreur: CUDA Out of Memory

**Symptôme**: Workflow queue mais aucun résultat

**Solutions progressives**:
1. Réduire résolution (768→512→384)
2. Attendre 30s entre générations
3. Redémarrer service ComfyUI
4. Utiliser workflow plus simple

**Code gestion erreur**:
```python
try:
    result = client.execute_workflow(workflow, max_wait=120)
except TimeoutError:
    print("⚠️ Génération trop longue, service surchargé?")
    print("💡 Essayer résolution plus petite ou moins de steps")
except Exception as e:
    print(f"❌ Erreur API: {e}")
```

### Erreur: "Value not in list"

**Cause**: Utilisation nodes Stable Diffusion standard au lieu custom Qwen

**Solution**: Vérifier `class_type` dans JSON:
- ✅ `QwenVLCLIPLoader`
- ❌ `CheckpointLoaderSimple`

### Images Floues/Artefacts

**Solutions**:
1. Augmenter `steps` (20→25→30)
2. Ajuster `cfg` (7→8)
3. Améliorer negative prompt
4. Réduire `denoise` pour I2I (0.8→0.6)

---

## 📊 Métriques Performance Attendues

### Latences Typiques RTX 3090

| Workflow | Résolution | Steps | VRAM | Temps Moyen |
|----------|-----------|-------|------|-------------|
| T2I Basique | 512x512 | 20 | 12GB | 5-8s |
| T2I Qualité | 512x512 | 30 | 15GB | 8-12s |
| I2I Standard | 512x512 | 25 | 15GB | 10-14s |
| I2I Détaillé | 768x768 | 30 | 18GB | 15-20s |

### Températures GPU Normales

- 60-70°C: Génération standard
- 70-78°C: Génération intensive
- >80°C: ⚠️ Vérifier ventilation

---

## 🎓 Progression Pédagogique Recommandée

### Notebook Structure (15 cellules)

**Section 1: Introduction ComfyUI** (3 cellules)
1. Markdown: Présentation API + use cases
2. Code: Imports + Client setup
3. Markdown: Architecture workflow JSON

**Section 2: Text-to-Image Basique** (4 cellules)
4. Markdown: Explication workflow T2I
5. Code: Workflow JSON + exécution
6. Code: Exercice variation prompts
7. Code: Analyse impact paramètres (steps/cfg)

**Section 3: Image-to-Image** (4 cellules)
8. Markdown: Principes édition guidée texte
9. Code: Upload + workflow I2I
10. Code: Exercice changement style
11. Code: Comparaison denoise/edit_strength

**Section 4: Avancé** (3 cellules)
12. Markdown: Optimisation VRAM + troubleshooting
13. Code: Grid comparaison paramètres
14. Code: Exercice pratique autonome

**Section 5: Conclusion** (1 cellule)
15. Markdown: Ressources + projets suggérés

---

## 📝 Notes Implementation Notebook

### Simplifications Pédagogiques

**Ne PAS inclure dans notebook débutant**:
- ❌ Workflows multi-images (trop complexe)
- ❌ Style transfer avancé (nécessite 2 images)
- ❌ WebSocket real-time (technique avancé)
- ❌ Hybride local/cloud (scope trop large)

**Inclure obligatoirement**:
- ✅ Helper function queue + poll
- ✅ Workflow T2I complet fonctionnel
- ✅ Workflow I2I simple (changement ciel exemple)
- ✅ Gestion erreurs timeout + OOM
- ✅ Visualisation matplotlib résultats

### Code Réutilisable Phase 12C

**Disponible dans**: `docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_design-notebooks-pedagogiques.md`

- Client Python ComfyUI complet
- Workflows JSON validés 5 types
- Tests unitaires API
- Scripts troubleshooting

---

## ✅ Validation Analyse API

### Informations Extraites

- [x] URL production + port API
- [x] Endpoints ComfyUI critiques
- [x] Pattern queue + poll vs Forge
- [x] Workflow T2I JSON complet
- [x] Workflow I2I JSON complet
- [x] Paramètres recommandés par cas usage
- [x] Client Python helper function
- [x] Troubleshooting erreurs communes
- [x] Métriques performance RTX 3090
- [x] Progression pédagogique 15 cellules

### Prochaine Étape

**Step 4**: Design Notebook Structure Complète

**Fichier suivant**: `2025-10-20_20_04_design-notebook-qwen.md`

**Contenu prévu**:
- Spécification complète 15 cellules
- Contenu markdown détaillé
- Code Python chaque cellule code
- Objectifs pédagogiques cellule
- Validation cohérence structure

---

**Document créé**: 2025-10-20 22:34 CEST  
**Statut Step 3**: ✅ COMPLÉTÉ  
**Lignes**: 656  
**Prochaine action**: Design complet notebook Phase 20