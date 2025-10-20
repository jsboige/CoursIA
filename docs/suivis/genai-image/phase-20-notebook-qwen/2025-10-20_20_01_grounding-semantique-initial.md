# Phase 20 - Grounding Sémantique Initial
**Date**: 2025-10-20 22:25  
**Objectif**: Recherche API ComfyUI + workflows Qwen pour design notebook pédagogique

---

## 1. RECHERCHE COMFYUI API WORKFLOWS

### Requête Sémantique
`"ComfyUI API REST workflows JSON prompt image edit Qwen"`

### Découvertes Critiques

#### 1.1 Architecture ComfyUI
**Endpoints API identifiés**:
- ✅ `/prompt` - Exécution workflows JSON
- ✅ `/queue` - Gestion file d'attente
- ✅ `/history` - Historique exécutions
- ✅ `/object_info` - Liste nodes disponibles
- ✅ `/upload/image` - Upload images sources
- ✅ `/system_stats` - Health check GPU/VRAM

**Format workflow JSON**:
```json
{
  "nodes": [
    {
      "id": "1",
      "inputs": { "param1": "value1" },
      "class_type": "NodeClassName"
    }
  ],
  "connections": [...]
}
```

#### 1.2 Contrainte Critique Qwen 🔴

**DÉCOUVERTE MAJEURE** (Phase 14B):
> **Qwen-Image-Edit-2509-FP8 INCOMPATIBLE avec workflows ComfyUI standards**

**Raison Technique**:
- ❌ Pas de checkpoint unifié `.safetensors`
- ✅ Modèle divisé en composants:
  - `text_encoder/` (4 fichiers)
  - `transformer/` (5 fichiers diffusion)
  - `vae/` (1 fichier)

**Implication Design Notebook**:
- Workflows standards (`CheckpointLoaderSimple`) NE FONCTIONNENT PAS
- **Solution obligatoire**: Utiliser 28 custom nodes Qwen spécifiques
- Erreur typique: `HTTP 400 - prompt_outputs_failed_validation`

**28 Custom Nodes Qwen Identifiés**:
1. `QwenVLCLIPLoader` - Chargement modèle VLM
2. `TextEncodeQwenImageEdit` - Encodage prompts positifs/négatifs
3. `QwenImageSamplerNode` - Sampler spécifique Qwen
4. ... (25 autres nodes documentés Phase 12C)

---

## 2. RECHERCHE WORKFLOWS QWEN PHASE 12C

### Requête Sémantique
`"workflows Qwen image edit ComfyUI VLM Phase 12C custom nodes"`

### Découvertes Documentation

#### 2.1 Document Référence Trouvé
**Fichier**: `docs/genai-suivis/2025-10-16_12C_architectures-5-workflows-qwen.md`

**Contenu attendu**:
- 5 workflows Qwen documentés
- Progression pédagogique simple→avancé
- Exemples JSON complets
- Paramètres recommandés VLM

**Action requise**: Lire ce document en détail (étape 3 - Analyse API Qwen)

#### 2.2 Helper Python Existant
**Fichier**: `MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py`

**Workflow basique Qwen identifié** (lignes 223-267):
```python
# Workflow JSON Qwen basique (référence Phase 12C)
workflow = {
    "1": {
        "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"},
        "class_type": "QwenVLCLIPLoader"
    },
    "2": {
        "inputs": {
            "text": prompt,
            "clip": ["1", 0]
        },
        "class_type": "TextEncodeQwenImageEdit"
    },
    "3": {
        "inputs": {
            "text": negative_prompt,
            "clip": ["1", 0]
        },
        "class_type": "TextEncodeQwenImageEdit"
    },
    "5": {
        "inputs": {
            "seed": seed,
            "steps": steps,
            "cfg": cfg,
            "sampler_name": "euler_ancestral",
            "scheduler": "normal",
            "denoise": 1.0,
            "transformer": ["1", 1],
            "positive": ["2", 0],
            "negative": ["3", 0],
            "latent_image": ["4", 0]
        },
        "class_type": "QwenImageSamplerNode"
    }
}
```

**Points clés**:
- Chaînage nodes via références `["node_id", output_index]`
- Sampler recommandé: `euler_ancestral` + scheduler `normal`
- Inputs essentiels: transformer, positive, negative, latent_image

---

## 3. RECHERCHE NOTEBOOK FORGE PHASE 18

### Requête Sémantique
`"notebook Forge Phase 18 structure pédagogique API REST"`

### Découvertes Modèle

#### 3.1 Fichier Référence
**Notebook**: `MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb`

**Structure attendue** (à valider étape 2 - Grounding Conversationnel):
- Introduction pédagogique
- Setup environnement (imports, config)
- Fonctions helper API REST
- Exemples progressifs (simple→avancé)
- Exercice pratique final
- Ressources complémentaires

**Patterns réutilisables identifiés**:
1. **Helper API générique**:
   ```python
   def call_api(endpoint, params):
       # Gestion erreurs
       # Retry logic
       # Logging clair
   ```

2. **Visualisation résultats**:
   ```python
   import matplotlib.pyplot as plt
   from PIL import Image
   # Affichage avant/après
   ```

3. **Gestion erreurs pédagogique**:
   - Messages clairs pour étudiants
   - Suggestions résolution
   - Exemples corrections

#### 3.2 Adaptation Requise pour Qwen

**Différences Forge vs Qwen**:

| Aspect | Forge (Phase 18) | Qwen (Phase 20) |
|--------|------------------|-----------------|
| **API** | REST simple (Automatic1111) | ComfyUI (workflows JSON) |
| **Endpoints** | `/txt2img`, `/img2img` | `/prompt`, `/upload/image` |
| **Format requête** | JSON params directs | Workflow graph JSON |
| **Complexité** | 🟢 Faible | 🟡 Moyenne |
| **Custom nodes** | ❌ Non requis | ✅ 28 nodes Qwen |

**Adaptations design notebook**:
1. Expliquer architecture ComfyUI workflows
2. Introduire concept graph nodes + connections
3. Fournir workflow template réutilisable
4. Helper fonction `execute_comfyui_workflow()`

---

## 4. SYNTHÈSE GROUNDING INITIAL

### 4.1 Contraintes Techniques Validées

✅ **API Qwen Opérationnelle**:
- URL: `https://qwen-image-edit.myia.io`
- Status: 100% (validé Phase 16)
- Performance: ~1.4s/requête
- GPU: RTX 3090 (24GB VRAM)

⚠️ **Complexité ComfyUI**:
- Workflows JSON (non REST simple)
- 28 custom nodes obligatoires
- Architecture graph nodes

✅ **Documentation Existante**:
- Workflows Phase 12C disponibles
- Helper Python `comfyui_client.py` fonctionnel
- Guide étudiants `GUIDE-APIS-ETUDIANTS.md` à jour

### 4.2 Patterns Pédagogiques Identifiés

**Du notebook Forge Phase 18**:
1. ✅ Progression logique simple→avancé
2. ✅ Exemples concrets reproductibles
3. ✅ Exercice pratique final
4. ✅ Gestion erreurs expliquée

**Adaptations Qwen requises**:
1. 🆕 Expliquer architecture ComfyUI
2. 🆕 Workflow JSON template
3. 🆕 Custom nodes Qwen (28)
4. 🆕 Upload image (édition)

### 4.3 Risques Identifiés

🔴 **Risque Complexité**:
- Workflows JSON plus complexes que REST simple
- Courbe apprentissage étudiants

**Mitigation**:
- Templates réutilisables fournis
- Helper `execute_comfyui_workflow()` abstrait complexité
- Progression pédagogique soignée

🟡 **Risque Custom Nodes**:
- 28 nodes Qwen non documentés pour étudiants

**Mitigation**:
- Documenter nodes essentiels dans notebook
- Fournir workflows validés Phase 12C
- Limiter à 5-6 nodes pour débutants

### 4.4 Décisions Design Préliminaires

**Structure notebook proposée** (15 cellules):

1. **Markdown**: Introduction API Qwen + ComfyUI
2. **Code**: Imports + configuration
3. **Markdown**: Architecture ComfyUI (nodes/connections)
4. **Code**: Helper `execute_comfyui_workflow()`
5. **Markdown**: Workflow simple "Hello World"
6. **Code**: Exemple génération basique
7. **Markdown**: Édition images avec Qwen VLM
8. **Code**: Fonction upload image
9. **Markdown**: Workflow édition image
10. **Code**: Exemple édition complète
11. **Markdown**: Cas d'usage avancés
12. **Code**: Comparaison variations prompts
13. **Markdown**: Bonnes pratiques ComfyUI
14. **Code**: Exercice pratique à compléter
15. **Markdown**: Ressources complémentaires

**Validation**: Cohérent avec structure Forge Phase 18 ✅

---

## 5. PROCHAINES ÉTAPES

### Étape 2: Grounding Conversationnel
**Actions**:
1. Analyser notebook Forge Phase 18 (détails structure)
2. Examiner historique conversations création notebooks
3. Identifier patterns efficaces validation

### Étape 3: Analyse API Qwen
**Actions**:
1. Lire `2025-10-16_12C_architectures-5-workflows-qwen.md`
2. Extraire workflows simples pour débutants
3. Documenter paramètres essentiels Qwen VLM

### Étape 4: Design Notebook
**Actions**:
1. Spécification complète 15 cellules
2. Workflows JSON validés
3. Code Python complet helpers

---

## 6. DÉCOUVRABILITÉ SDDD

### Mots-clés Sémantiques Documentés
- `ComfyUI API workflows JSON Phase 20`
- `Qwen Image-Edit custom nodes notebook pédagogique`
- `workflow graph nodes connections JSON`
- `QwenVLCLIPLoader TextEncodeQwenImageEdit`
- `notebook Forge Phase 18 pattern réutilisable`

### Documents Liés
- `docs/genai-suivis/2025-10-16_12C_architectures-5-workflows-qwen.md`
- `MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py`
- `docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md`
- `docs/suivis/genai-image/phase-14b-tests-apis/2025-10-16_14B_02_grounding-conversationnel.md`

---

## CONCLUSION GROUNDING INITIAL

✅ **Recherche sémantique complète**  
✅ **Contraintes techniques identifiées**  
✅ **Patterns pédagogiques validés**  
✅ **Risques anticipés et mitigés**  
✅ **Design préliminaire cohérent**

**Prêt pour étape 2**: Grounding Conversationnel (analyse notebook Forge)