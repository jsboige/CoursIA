# 🎨 Guide Utilisateur - Écosystème GenAI Images CoursIA

**Date :** 7 octobre 2025  
**Version :** 1.0  
**Public :** Étudiants, Enseignants, Développeurs

---

## 🚀 Démarrage Rapide (5 minutes)

### Étape 1 : Vérification Prérequis

**Environnement Requis :**
- Python 3.9+ avec Jupyter
- Visual Studio Code avec extensions Python + Jupyter
- Clé API OpenRouter (recommandé) OU OpenAI

**Vérification Installation :**
```powershell
# Vérification Python et Jupyter
python --version
jupyter --version

# Test d'environnement CoursIA
cd "d:\dev\CoursIA\MyIA.AI.Notebooks\GenAI"
python -c "import jupyter; print('✅ Jupyter OK')"
```

### Étape 2 : Configuration API (2 minutes)

**Option A : OpenRouter (Recommandé) 🌟**
1. Créer compte sur [OpenRouter.ai](https://openrouter.ai/)
2. Récupérer votre clé API
3. Ajouter dans `.env` :
```bash
OPENROUTER_API_KEY=sk-or-v1-votre-clé-ici
```

**Option B : OpenAI (Alternative)**
1. Compte OpenAI avec crédits
2. Ajouter dans `.env` :
```bash
OPENAI_API_KEY=sk-proj-votre-clé-ici
```

### Étape 3 : Premier Test (3 minutes)

```python
# Test rapide dans un notebook
from pathlib import Path
from dotenv import load_dotenv
import os

# Chargement configuration
load_dotenv()

# Vérification API
if os.getenv("OPENROUTER_API_KEY"):
    print("🎉 OpenRouter configuré - Prêt pour GenAI Images!")
elif os.getenv("OPENAI_API_KEY"):
    print("✅ OpenAI configuré - Mode fallback actif")
else:
    print("❌ Aucune API configurée - Voir guide configuration")
```

---

## 📚 Parcours d'Apprentissage Recommandés

### 🎯 Parcours Débutant (2-3 heures)

**Pour qui :** Première expérience avec GenAI Images

1. **📖 00-GenAI-Environment/00-Environment-Validation.ipynb** *(15 min)*
   - Configuration et validation environnement
   - Test des APIs disponibles
   - Familiarisation interface

2. **🖼️ 01-Images-Foundation/01-OpenAI-DALLE-Intro.ipynb** *(30 min)*
   - Première génération d'images avec DALL-E
   - Compréhension des prompts basiques
   - Paramètres de base

3. **🔍 01-Images-Foundation/02-OpenRouter-GPT5-Vision.ipynb** *(30 min)*
   - Analyse d'images avec GPT-5 Vision
   - Descriptions automatiques
   - Vision + génération combinées

4. **🎨 01-Images-Foundation/03-Stable-Diffusion-Basics.ipynb** *(45 min)*
   - Introduction Stable Diffusion
   - Comparaison avec DALL-E
   - Styles et techniques de base

**🎓 Résultat :** Capacité à générer et analyser des images avec 3 technologies différentes

### 🎯 Parcours Intermédiaire (4-5 heures)

**Pour qui :** Bases GenAI acquises, souhait d'approfondir

*Prérequis : Parcours Débutant complété*

1. **✏️ 02-Images-Advanced/01-Qwen-Image-Edit-2509.ipynb** *(60 min)*
   - Édition d'images avec IA
   - Modifications ciblées
   - Workflows d'amélioration

2. **🎭 02-Images-Advanced/02-FLUX1-Creative-Generation.ipynb** *(60 min)*
   - Génération créative avancée
   - Styles artistiques complexes
   - Techniques de prompt engineering

3. **⚙️ 02-Images-Advanced/03-ComfyUI-Workflows.ipynb** *(90 min)*
   - Workflows ComfyUI
   - Pipelines automatisés
   - Génération en série

**🎓 Résultat :** Maîtrise des techniques avancées et workflows complexes

### 🎯 Parcours Expert (6-8 heures)

**Pour qui :** Développement d'applications complètes

*Prérequis : Parcours Intermédiaire complété*

1. **🔄 03-Images-Orchestration/01-Multi-Model-Pipeline.ipynb** *(90 min)*
   - Orchestration de plusieurs modèles
   - Pipelines de traitement complexes
   - Optimisation performances

2. **☁️ 03-Images-Orchestration/02-Hybrid-Cloud-Local.ipynb** *(90 min)*
   - Architecture hybride cloud/local
   - Basculement automatique
   - Gestion des coûts

3. **⚡ 03-Images-Orchestration/03-Batch-Processing.ipynb** *(90 min)*
   - Traitement en lot
   - Automatisation complète
   - Monitoring et reporting

4. **🏗️ 04-Images-Applications/01-Educational-Content.ipynb** *(120 min)*
   - Création contenu éducatif
   - Génération automatisée
   - Application pratique complète

**🎓 Résultat :** Capacité à développer des applications GenAI Images production-ready

---

## 🛠️ Guides Techniques

### Configuration Environnement

#### Variables d'Environnement (.env)

**Configuration Minimale :**
```bash
# API Principal (choisir un)
OPENROUTER_API_KEY=sk-or-v1-your-key-here
# OU
OPENAI_API_KEY=sk-proj-your-key-here

# Configuration de base
GENAI_OUTPUT_DIR="outputs"
GENAI_DEFAULT_MODEL="gpt-4o-2024-08-06"
```

**Configuration Avancée :**
```bash
# URLs de base (personnalisables)
OPENROUTER_BASE_URL="https://openrouter.ai/api/v1"
OPENROUTER_APP_NAME="CoursIA-GenAI"
OPENAI_BASE_URL="https://api.openai.com/v1"

# Paramètres de performance
GENAI_TIMEOUT_SECONDS=300
GENAI_MAX_RETRIES=3
GENAI_CONCURRENT_REQUESTS=2

# Services Docker locaux (optionnel)
FLUX_API_URL="http://localhost:8001"
STABLE_DIFFUSION_URL="http://localhost:7860"
COMFYUI_API_URL="http://localhost:8188"

# Debug et logging
GENAI_DEBUG_LEVEL="INFO"
GENAI_LOG_FILE="logs/genai.log"
```

#### Résolution Problèmes Courants

**Problème : "Module not found"**
```powershell
# Installation packages requis
pip install python-dotenv requests pillow jupyter ipywidgets
pip install openai anthropic  # APIs
```

**Problème : "API Key not found"**
```python
# Diagnostic clé API
import os
from dotenv import load_dotenv

load_dotenv()
print("OpenRouter:", "✅" if os.getenv("OPENROUTER_API_KEY") else "❌")
print("OpenAI:", "✅" if os.getenv("OPENAI_API_KEY") else "❌")
```

**Problème : Timeout API**
```python
# Configuration timeout adaptatif
import os
os.environ["GENAI_TIMEOUT_SECONDS"] = "600"  # 10 minutes
```

### Optimisation Performances

#### Gestion Mémoire
```python
# Libération mémoire entre générations
import gc
gc.collect()

# Limitation taille images
MAX_IMAGE_SIZE = (1024, 1024)
COMPRESSION_QUALITY = 85
```

#### Cache et Réutilisation
```python
# Cache des réponses API
import hashlib
import pickle
from pathlib import Path

def cache_api_response(prompt, response, model="default"):
    cache_dir = Path("cache")
    cache_dir.mkdir(exist_ok=True)
    
    prompt_hash = hashlib.md5(f"{model}:{prompt}".encode()).hexdigest()
    cache_file = cache_dir / f"{prompt_hash}.pkl"
    
    with open(cache_file, 'wb') as f:
        pickle.dump(response, f)
```

---

## 📊 Monitoring et Analytics

### Métriques de Performance

**Indicateurs Clés :**
```python
import time
import json
from datetime import datetime

class GenAIMetrics:
    def __init__(self):
        self.metrics = {
            "generations": [],
            "api_calls": [],
            "errors": [],
            "costs": []
        }
    
    def log_generation(self, model, prompt, duration, success):
        self.metrics["generations"].append({
            "timestamp": datetime.now().isoformat(),
            "model": model,
            "prompt_length": len(prompt),
            "duration_seconds": duration,
            "success": success
        })
    
    def get_stats(self):
        total_gens = len(self.metrics["generations"])
        success_rate = sum(g["success"] for g in self.metrics["generations"]) / total_gens * 100
        avg_duration = sum(g["duration_seconds"] for g in self.metrics["generations"]) / total_gens
        
        return {
            "total_generations": total_gens,
            "success_rate": f"{success_rate:.1f}%",
            "average_duration": f"{avg_duration:.1f}s"
        }

# Usage dans notebooks
metrics = GenAIMetrics()
# ... pendant génération ...
metrics.log_generation("gpt-4o", prompt, duration, success)
print(metrics.get_stats())
```

### Logging Avancé

**Configuration Logging :**
```python
import logging
from datetime import datetime
from pathlib import Path

# Setup logging CoursIA GenAI
def setup_genai_logging(level="INFO"):
    logger = logging.getLogger('coursia_genai')
    logger.setLevel(getattr(logging, level))
    
    # File handler
    log_dir = Path("logs")
    log_dir.mkdir(exist_ok=True)
    
    file_handler = logging.FileHandler(
        log_dir / f"genai_{datetime.now().strftime('%Y%m%d')}.log"
    )
    file_handler.setLevel(logging.DEBUG)
    
    # Console handler
    console_handler = logging.StreamHandler()
    console_handler.setLevel(getattr(logging, level))
    
    # Formatter
    formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    file_handler.setFormatter(formatter)
    console_handler.setFormatter(formatter)
    
    logger.addHandler(file_handler)
    logger.addHandler(console_handler)
    
    return logger

# Usage dans notebooks
logger = setup_genai_logging()
logger.info("🚀 Démarrage session GenAI")
logger.debug(f"Configuration: {api_config}")
```

---

## 🔧 Intégration MCP

### Exécution via MCP (Mode Batch)

**Configuration MCP :**
Les notebooks sont compatibles avec l'infrastructure MCP de CoursIA pour exécution automatisée.

**Variables Papermill :**
```python
# Cellule Parameters (à personnaliser)
notebook_mode = "batch"        # Mode MCP
api_provider = "openrouter"    # Provider par défaut  
skip_widgets = True            # Désactive widgets interactifs
debug_level = "INFO"           # Niveau logging
output_format = "detailed"     # Format de sortie
```

**Commandes MCP :**
```python
# Via jupyter-papermill-mcp-server
await execute_notebook_sync(
    notebook_path="01-Images-Foundation/01-OpenAI-DALLE-Intro.ipynb",
    parameters={
        "notebook_mode": "batch",
        "api_provider": "openrouter",
        "skip_widgets": True,
        "prompt": "Un paysage futuriste avec des robots"
    },
    timeout_seconds=300
)
```

### Paramétrage Avancé MCP

**Injection de Sujets Complexes :**
```python
# Pour notebooks éducatifs avec sujets générés
complex_topic = {
    "subject": "Architecture GenAI multimodale",
    "difficulty": "advanced", 
    "focus_areas": ["orchestration", "performance", "coûts"],
    "deliverables": ["rapport", "code", "présentation"]
}

# MCP injection
await execute_notebook_with_complex_topic(
    notebook_path="04-Images-Applications/01-Educational-Content.ipynb",
    topic_parameters=complex_topic
)
```

---

## 🎓 Cas d'Usage Pédagogiques

### Pour Enseignants

**Génération de Contenu Pédagogique :**
- Illustrations automatiques pour cours
- Diagrammes techniques générés
- Exemples visuels personnalisés par sujet

**Évaluation et Exercices :**
- Génération d'images pour exercices d'analyse
- Création de références visuelles
- Tests de reconnaissance automatique

### Pour Étudiants

**Projets Pratiques :**
- Portfolio d'images générées
- Comparaison de modèles GenAI
- Applications créatives personnelles

**Recherche et Expérimentation :**
- Test de prompts avancés
- Analyse qualitative des résultats
- Optimisation de paramètres

### Pour Développeurs

**Prototypage Rapide :**
- Maquettes visuelles automatiques
- Assets pour applications
- Tests A/B de concepts visuels

**Intégration Applications :**
- APIs prêtes à l'emploi
- Patterns de code réutilisables
- Monitoring production-ready

---

## 🚨 Sécurité et Bonnes Pratiques

### Protection des Clés API

**✅ Faire :**
- Utiliser des fichiers `.env` (jamais en git)
- Rotation régulière des clés
- Variables d'environnement système
- Clés avec permissions minimales

**❌ Ne Jamais Faire :**
- Clés en dur dans le code
- Partage de clés par email/chat
- Commit accidentel de `.env`
- Clés dans logs ou outputs

### Utilisation Responsable

**Coûts et Limites :**
- Surveillance de la consommation API
- Timeouts appropriés
- Cache des résultats fréquents
- Modèles adaptés au besoin

**Contenu Généré :**
- Vérification du contenu produit
- Respect des politiques d'usage
- Attribution appropriée
- Respect de la propriété intellectuelle

---

## 🆘 Support et Dépannage

### FAQ Rapide

**Q: Quelle API choisir entre OpenRouter et OpenAI ?**
R: OpenRouter pour accès unifié à multiple modèles (GPT-5, Qwen), OpenAI pour simplicité et fiabilité.

**Q: Docker est-il obligatoire ?**
R: Non, tous les notebooks fonctionnent avec APIs cloud. Docker est optionnel pour modèles locaux.

**Q: Puis-je utiliser mes propres images ?**
R: Oui, les notebooks supportent upload et analyse d'images personnelles.

**Q: Les notebooks fonctionnent-ils offline ?**
R: Partiellement. Configuration et interface oui, génération nécessite API/Docker.

### Diagnostic Automatisé

**Script de Diagnostic :**
```python
def diagnostic_complet():
    """Diagnostic automatique environnement GenAI"""
    print("🔍 Diagnostic CoursIA GenAI\n")
    
    # Test Python et modules
    try:
        import sys, jupyter, dotenv
        print(f"✅ Python {sys.version}")
        print(f"✅ Jupyter {jupyter.__version__}")
    except ImportError as e:
        print(f"❌ Module manquant: {e}")
    
    # Test configuration
    from dotenv import load_dotenv
    import os
    
    load_dotenv()
    apis = {
        "OpenRouter": os.getenv("OPENROUTER_API_KEY"),
        "OpenAI": os.getenv("OPENAI_API_KEY")
    }
    
    for api, key in apis.items():
        status = "✅" if key else "❌"
        print(f"{status} {api}: {'Configuré' if key else 'Manquant'}")
    
    # Test répertoires
    from pathlib import Path
    
    required_dirs = [
        Path("outputs"),
        Path("logs"), 
        Path("cache")
    ]
    
    for dir_path in required_dirs:
        if dir_path.exists():
            print(f"✅ Répertoire {dir_path}")
        else:
            dir_path.mkdir(exist_ok=True)
            print(f"🔧 Créé répertoire {dir_path}")
    
    print("\n🎉 Diagnostic terminé!")

# Lancer dans n'importe quel notebook
diagnostic_complet()
```

### Contact Support

**Ressources :**
- **Documentation :** [`docs/genai-images-development-standards.md`](genai-images-development-standards.md)
- **Problèmes techniques :** Issues GitHub du projet CoursIA
- **Communauté :** Discord/Forum CoursIA (si disponible)

---

*Guide conçu pour accompagner votre apprentissage GenAI Images avec CoursIA 🚀*