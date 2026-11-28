# 🔧 TROUBLESHOOTING GUIDE - GenAI Images CoursIA

> **Guide complet de résolution des problèmes courants**  
> Solutions étape par étape | Scripts diagnostiques | Support production

---

## 📑 Table des Matières

1. [Problèmes APIs Externes](#problèmes-apis-externes)
2. [Erreurs Configuration](#erreurs-configuration)
3. [Issues MCP/Papermill](#issues-mcppapermill)
4. [Problèmes Performance](#problèmes-performance)
5. [Quality Issues](#quality-issues)
6. [Gestion des Coûts](#gestion-des-coûts)
7. [Problèmes Intégration](#problèmes-intégration)
8. [Scripts Diagnostiques](#scripts-diagnostiques)
9. [Support & Escalation](#support--escalation)

---

## 🌐 Problèmes APIs Externes

### 1. ❌ API Key Invalid (OpenAI)

#### Symptômes
```python
openai.AuthenticationError: Incorrect API key provided: sk-****
```

#### Diagnostic
```python
import os
from dotenv import load_dotenv

# Vérifier chargement .env
load_dotenv()

# Afficher début clé (sécurisé)
api_key = os.getenv("OPENAI_API_KEY")
if api_key:
    print(f"✅ Clé trouvée: {api_key[:10]}...{api_key[-4:]}")
else:
    print("❌ Variable OPENAI_API_KEY non définie")
```

#### Solutions

**Solution 1: Vérifier fichier .env**
```bash
# 1. Vérifier .env existe
ls -la .env  # Linux/Mac
dir .env     # Windows

# 2. Contenu attendu
cat .env
# Output: OPENAI_API_KEY=sk-proj-...
```

**Solution 2: Recharger environnement**
```python
# Dans Jupyter, redémarrer kernel
# Kernel > Restart Kernel

# Puis recharger
from dotenv import load_dotenv
load_dotenv(override=True)  # Force reload
```

**Solution 3: Vérifier clé sur plateforme**
```bash
# 1. Aller sur https://platform.openai.com/api-keys
# 2. Créer nouvelle clé si nécessaire
# 3. Copier dans .env (sans espaces)
OPENAI_API_KEY=sk-proj-abcd1234...
```

**Solution 4: Tester connexion**
```python
from openai import OpenAI
import os

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

try:
    # Test minimal
    models = client.models.list()
    print("✅ Connexion OpenAI OK")
except Exception as e:
    print(f"❌ Erreur: {e}")
```

---

### 2. ⚠️ Rate Limit Exceeded

#### Symptômes
```python
openai.RateLimitError: Rate limit reached for requests
```

#### Causes Fréquentes
- Trop de requêtes simultanées
- Dépassement quota tier gratuit
- Boucles mal contrôlées

#### Solution 1: Retry avec Backoff Exponentiel
```python
import time
from openai import RateLimitError, OpenAI

def generate_with_retry(client, prompt, max_retries=5):
    """Génération avec retry automatique"""
    for attempt in range(max_retries):
        try:
            response = client.images.generate(
                model="dall-e-3",
                prompt=prompt,
                size="1024x1024"
            )
            return response
        except RateLimitError as e:
            if attempt == max_retries - 1:
                raise
            wait_time = 2 ** attempt  # Backoff: 1s, 2s, 4s, 8s, 16s
            print(f"⏳ Rate limit, attente {wait_time}s... (tentative {attempt+1}/{max_retries})")
            time.sleep(wait_time)
```

#### Solution 2: Throttling Manuel
```python
import time
from datetime import datetime

class RateLimiter:
    """Limiteur de taux configurable"""
    def __init__(self, requests_per_minute=50):
        self.requests_per_minute = requests_per_minute
        self.min_interval = 60.0 / requests_per_minute
        self.last_request = 0
    
    def wait(self):
        """Attend le temps nécessaire avant prochaine requête"""
        now = time.time()
        time_since_last = now - self.last_request
        
        if time_since_last < self.min_interval:
            sleep_time = self.min_interval - time_since_last
            print(f"⏸️ Throttling: {sleep_time:.2f}s")
            time.sleep(sleep_time)
        
        self.last_request = time.time()

# Usage
limiter = RateLimiter(requests_per_minute=30)

for prompt in prompts:
    limiter.wait()
    response = client.images.generate(...)
```

#### Solution 3: Batch avec Délais
```python
import asyncio

async def generate_batch_with_delay(prompts, delay_seconds=2):
    """Batch processing avec délais"""
    results = []
    
    for i, prompt in enumerate(prompts):
        print(f"🎨 Génération {i+1}/{len(prompts)}")
        
        response = client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size="1024x1024"
        )
        results.append(response)
        
        if i < len(prompts) - 1:
            await asyncio.sleep(delay_seconds)
    
    return results
```

#### Solution 4: Upgrade Tier
```bash
# Si usage fréquent, passer à tier payant
# https://platform.openai.com/account/billing/overview

# Limites par tier:
# Free: 3 images/min
# Tier 1 ($5+): 50 images/min
# Tier 2 ($50+): 100 images/min
```

---

### 3. 🔒 OpenRouter API Issues

#### Symptômes
```python
openai.APIError: OpenRouter API error: Invalid model specified
```

#### Solution 1: Vérifier Format Modèle
```python
from openai import OpenAI
import os

# ❌ Incorrect
client = OpenAI(
    api_key=os.getenv("OPENROUTER_API_KEY"),
    base_url="https://openrouter.ai/api/v1"
)
response = client.chat.completions.create(
    model="gpt-5-preview",  # ❌ Format incorrect
    ...
)

# ✅ Correct
response = client.chat.completions.create(
    model="openai/gpt-5-preview",  # ✅ Avec provider prefix
    ...
)
```

#### Solution 2: Tester Disponibilité Modèle
```python
def check_model_availability(model_id):
    """Vérifie si modèle disponible sur OpenRouter"""
    import requests
    
    headers = {
        "Authorization": f"Bearer {os.getenv('OPENROUTER_API_KEY')}"
    }
    
    response = requests.get(
        "https://openrouter.ai/api/v1/models",
        headers=headers
    )
    
    models = response.json()
    available = [m['id'] for m in models.get('data', [])]
    
    if model_id in available:
        print(f"✅ {model_id} disponible")
        return True
    else:
        print(f"❌ {model_id} non disponible")
        print(f"Modèles similaires: {[m for m in available if model_id.split('/')[-1] in m]}")
        return False

# Test
check_model_availability("openai/gpt-5-preview")
```

#### Solution 3: Headers Additionnels
```python
# Pour tracking et features avancées
client = OpenAI(
    api_key=os.getenv("OPENROUTER_API_KEY"),
    base_url="https://openrouter.ai/api/v1",
    default_headers={
        "HTTP-Referer": "https://coursia.ai",  # Optional
        "X-Title": "CoursIA GenAI Images"      # Optional
    }
)
```

---

### 4. 💸 Budget Exceeded

#### Symptômes
```python
openai.APIError: You exceeded your current quota
```

#### Diagnostic Budget
```python
import requests
import os

def check_openai_usage():
    """Vérifie usage et limites OpenAI"""
    headers = {
        "Authorization": f"Bearer {os.getenv('OPENAI_API_KEY')}"
    }
    
    # Note: API usage endpoint deprecated, vérifier sur dashboard
    print("📊 Vérifier usage sur: https://platform.openai.com/usage")
    print("💳 Vérifier limites sur: https://platform.openai.com/account/billing/limits")

check_openai_usage()
```

#### Solutions

**Solution 1: Configurer Limites Budgétaires**
```bash
# Dans dashboard OpenAI:
# 1. Account > Billing > Usage limits
# 2. Set monthly budget cap
# 3. Enable email alerts at 75%, 90%
```

**Solution 2: Local Cost Tracking**
```python
class CostTracker:
    """Suivi coûts local"""
    def __init__(self):
        self.costs = {
            'dalle-3-standard': 0.040,
            'dalle-3-hd': 0.080,
            'gpt-5-preview-input': 0.00001,  # per token
            'gpt-5-preview-output': 0.00003
        }
        self.usage = []
    
    def log_dalle_generation(self, size, quality='standard'):
        """Log génération DALL-E"""
        key = f'dalle-3-{quality}'
        cost = self.costs[key]
        self.usage.append({
            'type': 'dalle-3',
            'cost': cost,
            'size': size,
            'quality': quality
        })
        return cost
    
    def get_total_cost(self):
        """Calcule coût total"""
        return sum(item['cost'] for item in self.usage)
    
    def get_report(self):
        """Rapport détaillé"""
        total = self.get_total_cost()
        return {
            'total_cost': total,
            'num_requests': len(self.usage),
            'average_cost': total / len(self.usage) if self.usage else 0
        }

# Usage
tracker = CostTracker()

# Après chaque génération
cost = tracker.log_dalle_generation('1024x1024', 'standard')
print(f"💰 Coût: ${cost:.4f}")

# Rapport final
report = tracker.get_report()
print(f"📊 Total session: ${report['total_cost']:.2f}")
```

**Solution 3: Ajouter Crédits**
```bash
# https://platform.openai.com/account/billing/overview
# Add payment method -> Add to balance
```

---

## ⚙️ Erreurs Configuration

### 5. 📝 .env File Not Found

#### Symptômes
```python
# Variables d'environnement None
os.getenv("OPENAI_API_KEY") returns None
```

#### Solution 1: Créer .env
```bash
# Créer depuis template
cp .env.example .env

# Éditer avec clés réelles
nano .env  # Linux/Mac
notepad .env  # Windows
```

#### Solution 2: Vérifier Emplacement
```python
import os
from pathlib import Path

# Afficher working directory
print(f"Working dir: {os.getcwd()}")

# Vérifier .env existe
env_path = Path(".env")
if env_path.exists():
    print(f"✅ .env trouvé: {env_path.absolute()}")
else:
    print(f"❌ .env manquant dans: {env_path.absolute()}")
    
# Lister fichiers .env* dans répertoire
env_files = list(Path(".").glob(".env*"))
print(f"Fichiers .env trouvés: {env_files}")
```

#### Solution 3: Load Explicite
```python
from dotenv import load_dotenv
from pathlib import Path

# Chemin explicite
env_path = Path("MyIA.AI.Notebooks/GenAI/.env")
load_dotenv(dotenv_path=env_path)

# Vérification
api_key = os.getenv("OPENAI_API_KEY")
print(f"Clé chargée: {api_key is not None}")
```

---

### 6. 🔐 Invalid Characters in API Key

#### Symptômes
```python
# Erreur parsing ou authentication
ValueError: Invalid API key format
```

#### Solution: Nettoyage Clé
```python
import os

def clean_api_key(raw_key):
    """Nettoie clé API (espaces, newlines)"""
    if not raw_key:
        return None
    
    # Supprimer whitespace
    cleaned = raw_key.strip()
    
    # Vérifier format attendu
    if cleaned.startswith("sk-"):
        return cleaned
    else:
        print(f"⚠️ Format suspect: {cleaned[:10]}...")
        return cleaned

# Usage
raw_key = os.getenv("OPENAI_API_KEY")
api_key = clean_api_key(raw_key)

# Tester
client = OpenAI(api_key=api_key)
```

---

### 7. 📦 Missing Dependencies

#### Symptômes
```python
ModuleNotFoundError: No module named 'openai'
```

#### Solution 1: Installation Complète
```bash
# Activer environnement
source venv/bin/activate  # Linux/Mac
venv\Scripts\activate     # Windows

# Installer depuis requirements
pip install -r requirements.txt

# Vérifier installation
pip list | grep openai
```

#### Solution 2: Installation Individuelle
```bash
# Dépendances core
pip install openai>=1.3.0
pip install Pillow>=10.0.0
pip install requests>=2.31.0
pip install python-dotenv>=1.0.0

# Jupyter
pip install jupyter>=1.0.0
pip install notebook>=7.0.0
```

#### Solution 3: Kernel Jupyter
```bash
# Enregistrer kernel avec environnement
python -m ipykernel install --user --name=genai-env --display-name="Python (GenAI)"

# Dans Jupyter, sélectionner kernel "Python (GenAI)"
```

---

## 🐍 Issues MCP/Papermill

### 8. 🔤 BOM UTF-8 in Notebooks

#### Symptômes
```python
# MCP Papermill erreur parsing
json.JSONDecodeError: Unexpected UTF-8 BOM
```

#### Diagnostic
```python
def check_bom(file_path):
    """Détecte BOM UTF-8 dans fichier"""
    with open(file_path, 'rb') as f:
        start = f.read(3)
        has_bom = (start == b'\xef\xbb\xbf')
        
    if has_bom:
        print(f"⚠️ BOM détecté: {file_path}")
    else:
        print(f"✅ Pas de BOM: {file_path}")
    
    return has_bom

# Tester notebook
check_bom("01-1-Generation-Image-Texte-API.ipynb")
```

#### Solution Automatique: Script PowerShell
```powershell
# Script: scripts/37-fix-genai-bom-utf8-20251008.ps1
$notebooks = Get-ChildItem -Path "MyIA.AI.Notebooks/GenAI" -Filter "*.ipynb" -Recurse

foreach ($notebook in $notebooks) {
    # Lire contenu
    $content = Get-Content $notebook.FullName -Raw -Encoding UTF8
    
    # Réécrire sans BOM
    [System.IO.File]::WriteAllLines($notebook.FullName, $content, [System.Text.UTF8Encoding]::new($false))
    
    Write-Host "✅ Fixed: $($notebook.Name)"
}
```

#### Solution Manuelle Python
```python
def remove_bom(file_path):
    """Supprime BOM UTF-8 d'un notebook"""
    import json
    
    # Lire avec gestion BOM
    with open(file_path, 'r', encoding='utf-8-sig') as f:
        content = json.load(f)
    
    # Réécrire sans BOM
    with open(file_path, 'w', encoding='utf-8') as f:
        json.dump(content, f, indent=2, ensure_ascii=False)
    
    print(f"✅ BOM supprimé: {file_path}")

# Usage
remove_bom("01-1-Generation-Image-Texte-API.ipynb")
```

---

### 9. 🚫 Papermill Execution Timeout

#### Symptômes
```python
papermill.exceptions.PapermillExecutionError: Execution timeout after 300s
```

#### Solution 1: Augmenter Timeout
```python
import papermill as pm

pm.execute_notebook(
    '01-1-Generation-Image-Texte-API.ipynb',
    'output.ipynb',
    timeout=600,  # 10 minutes au lieu de 5
    kernel_name='python3'
)
```

#### Solution 2: MCP Async Execution
```python
# Via MCP Papermill Server
# Tool: start_notebook_async

{
    "notebook_path": "01-1-Generation-Image-Texte-API.ipynb",
    "timeout_seconds": 1200,  # 20 minutes
    "output_path": "output.ipynb"
}

# Puis polling status
# Tool: get_execution_status_async
```

#### Solution 3: Optimiser Notebook
```python
# Identifier cellules lentes
%time  # En début de cellule

# Cacher résultats lourds
import pickle

# Sauvegarder
with open('cache.pkl', 'wb') as f:
    pickle.dump(results, f)

# Recharger
with open('cache.pkl', 'rb') as f:
    results = pickle.load(f)
```

---

### 10. 📂 Path Issues (Windows vs Linux)

#### Symptômes
```python
FileNotFoundError: [Errno 2] No such file or directory: 'outputs\image.png'
```

#### Solution: Path Agnostique
```python
from pathlib import Path

# ❌ Éviter strings hardcodés
output_path = "outputs\image.png"  # Windows uniquement

# ✅ Utiliser pathlib
output_path = Path("outputs") / "image.png"  # Cross-platform

# Créer répertoires si nécessaire
output_path.parent.mkdir(parents=True, exist_ok=True)

# Convertir en string pour APIs
image_path_str = str(output_path)
```

---

## ⚡ Problèmes Performance

### 11. 🐌 Slow Image Generation

#### Diagnostic
```python
import time

def measure_generation_time(prompt):
    """Mesure temps génération"""
    start = time.time()
    
    response = client.images.generate(
        model="dall-e-3",
        prompt=prompt,
        size="1024x1024"
    )
    
    elapsed = time.time() - start
    print(f"⏱️ Temps génération: {elapsed:.2f}s")
    
    return response, elapsed

# Test
response, timing = measure_generation_time("Test prompt")
```

#### Solutions

**Solution 1: Optimiser Taille Images**
```python
# Si possible, utiliser résolution inférieure
response = client.images.generate(
    model="dall-e-3",
    prompt=prompt,
    size="1024x1024",  # Au lieu de 1792x1024
    quality="standard"  # Au lieu de 'hd'
)
# Standard: ~30-40s vs HD: ~60-90s
```

**Solution 2: Parallel Processing**
```python
from concurrent.futures import ThreadPoolExecutor

def generate_parallel(prompts, max_workers=3):
    """Génération parallèle (attention rate limits)"""
    results = []
    
    def generate_one(prompt):
        return client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size="1024x1024"
        )
    
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        results = list(executor.map(generate_one, prompts))
    
    return results

# Usage
results = generate_parallel(prompts[:5], max_workers=2)
```

---

### 12. 💾 Out of Memory (Large Images)

#### Symptômes
```python
MemoryError: Unable to allocate array
```

#### Solution 1: Libération Mémoire
```python
from PIL import Image
import gc

# Après traitement
image = Image.open('large.png')
# ... opérations ...
image.close()
del image
gc.collect()
```

#### Solution 2: Streaming Downloads
```python
import requests
from PIL import Image
from io import BytesIO

def download_and_resize(url, max_size=(1024, 1024)):
    """Télécharge et redimensionne directement"""
    response = requests.get(url, stream=True)
    
    # Charger en mémoire minimale
    img = Image.open(BytesIO(response.content))
    
    # Redimensionner immédiatement
    img.thumbnail(max_size, Image.Resampling.LANCZOS)
    
    return img
```

#### Solution 3: Processing par Batch
```python
def process_images_batched(image_paths, batch_size=10):
    """Traite images par petits lots"""
    for i in range(0, len(image_paths), batch_size):
        batch = image_paths[i:i+batch_size]
        
        # Traiter batch
        for path in batch:
            img = Image.open(path)
            # ... opérations ...
            img.close()
        
        # Libérer mémoire
        gc.collect()
        print(f"✅ Batch {i//batch_size + 1} terminé")
```

---

### 13. 🔥 High CPU Usage

#### Solution: Limiter Threads PIL
```python
from PIL import Image

# Limiter threads pour opérations image
Image.MAX_IMAGE_PIXELS = 100000000  # Limite pixels

# Pour OpenCV
import cv2
cv2.setNumThreads(2)  # Limiter à 2 threads
```

---

## 🎨 Quality Issues

### 14. 😞 Unsatisfactory Results

#### Diagnostic: Analyse Systematic
```python
def analyze_generation_quality(prompt, num_iterations=3):
    """Génère plusieurs versions pour comparaison"""
    results = []
    
    for i in range(num_iterations):
        print(f"🎨 Itération {i+1}/{num_iterations}")
        
        response = client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size="1024x1024"
        )
        
        results.append({
            'url': response.data[0].url,
            'revised_prompt': response.data[0].revised_prompt,
            'iteration': i+1
        })
    
    return results
```

#### Solution 1: Améliorer Prompts
```python
# ❌ Prompt vague
prompt = "Cellule végétale"

# ✅ Prompt détaillé
prompt = """Diagramme scientifique détaillé d'une cellule végétale, 
vue en coupe transversale, montrant clairement:
- Noyau au centre avec nucléole
- Chloroplastes verts répartis dans cytoplasme
- Vacuole centrale large
- Paroi cellulaire épaisse externe
- Membrane plasmique
- Mitochondries
Labels français pour chaque organite, 
style manuel biologie éducatif,
fond blanc, haute clarté"""
```

#### Solution 2: Style Modifiers
```python
# Ajouter style spécifique
STYLE_MODIFIERS = {
    'educational': 'style manuel éducatif, diagramme pédagogique, labels clairs',
    'realistic': 'photoréaliste, haute définition, éclairage naturel',
    'illustration': 'illustration artistique, couleurs vives, style dessiné',
    'scientific': 'schéma scientifique précis, annotations techniques'
}

enhanced_prompt = f"{base_prompt}, {STYLE_MODIFIERS['educational']}"
```

---

### 15. 🔍 GPT-5 Vision Errors

#### Symptômes
```python
# Analyse imprécise ou erreurs
"Unable to analyze image" ou descriptions vagues
```

#### Solution 1: Optimiser Prompt Vision
```python
def create_detailed_analysis_prompt(context):
    """Crée prompt structuré pour GPT-5"""
    prompt = f"""Analyse cette image en détail pour un contexte {context}.

Structure ta réponse ainsi:
1. DESCRIPTION GÉNÉRALE (2-3 phrases)
2. ÉLÉMENTS PRINCIPAUX (liste détaillée)
3. DÉTAILS TECHNIQUES (couleurs, composition, style)
4. PERTINENCE PÉDAGOGIQUE (si applicable)
5. SUGGESTIONS AMÉLIORATION (si nécessaire)

Sois précis, factuel, et exhaustif."""
    
    return prompt

# Usage
analysis_prompt = create_detailed_analysis_prompt("éducation sciences")
```

#### Solution 2: Vérifier Qualité Image
```python
from PIL import Image

def check_image_quality(image_path):
    """Vérifie que l'image est acceptable pour GPT-5"""
    img = Image.open(image_path)
    
    # Dimensions
    width, height = img.size
    pixels = width * height
    
    checks = {
        'dimensions_ok': width >= 256 and height >= 256,
        'not_too_large': pixels <= 4096 * 4096,
        'format_supported': img.format in ['PNG', 'JPEG', 'WEBP', 'GIF']
    }
    
    if all(checks.values()):
        print(f"✅ Image OK: {width}x{height}, {img.format}")
        return True
    else:
        print(f"⚠️ Issues détectés:")
        for check, passed in checks.items():
            if not passed:
                print(f"  - {check}: ❌")
        return False
```

---

## 💰 Gestion des Coûts

### 16. 📈 Cost Overrun

#### Monitoring Costs
```python
class DetailedCostTracker:
    """Tracker coûts avec alertes"""
    def __init__(self, daily_budget=10.0):
        self.daily_budget = daily_budget
        self.costs = []
        self.alerts = []
    
    def log_request(self, model, cost, metadata=None):
        """Log requête avec coût"""
        entry = {
            'timestamp': datetime.now(),
            'model': model,
            'cost': cost,
            'metadata': metadata or {}
        }
        self.costs.append(entry)
        
        # Vérifier budget
        daily_total = self.get_daily_total()
        if daily_total > self.daily_budget * 0.8:
            self.alerts.append(f"⚠️ 80% budget quotidien atteint: ${daily_total:.2f}")
    
    def get_daily_total(self):
        """Calcule total journée en cours"""
        today = datetime.now().date()
        return sum(
            c['cost'] for c in self.costs 
            if c['timestamp'].date() == today
        )
    
    def get_report(self):
        """Rapport détaillé"""
        total = sum(c['cost'] for c in self.costs)
        by_model = {}
        
        for cost in self.costs:
            model = cost['model']
            by_model[model] = by_model.get(model, 0) + cost['cost']
        
        return {
            'total': total,
            'daily': self.get_daily_total(),
            'by_model': by_model,
            'alerts': self.alerts
        }

# Usage
tracker = DetailedCostTracker(daily_budget=5.0)

# Log chaque requête
tracker.log_request('dalle-3-standard', 0.040, {'size': '1024x1024'})

# Rapport
report = tracker.get_report()
print(f"💰 Coût total: ${report['total']:.2f}")
print(f"📊 Par modèle: {report['by_model']}")
```

---

### 17. 💡 Cost Optimization Strategies

#### Stratégie 1: Caching Intelligent
```python
import hashlib
import json
from pathlib import Path

class ImageCache:
    """Cache images générées pour éviter regénération"""
    def __init__(self, cache_dir="cache"):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)
    
    def get_cache_key(self, prompt, size, quality):
        """Génère clé cache unique"""
        content = f"{prompt}|{size}|{quality}"
        return hashlib.md5(content.encode()).hexdigest()
    
    def get(self, prompt, size, quality):
        """Récupère depuis cache si existe"""
        key = self.get_cache_key(prompt, size, quality)
        cache_file = self.cache_dir / f"{key}.json"
        
        if cache_file.exists():
            with open(cache_file) as f:
                data = json.load(f)
            print(f"✅ Cache hit: {key[:8]}...")
            return data
        
        return None
    
    def set(self, prompt, size, quality, response_data):
        """Sauvegarde dans cache"""
        key = self.get_cache_key(prompt, size, quality)
        cache_file = self.cache_dir / f"{key}.json"
        
        with open(cache_file, 'w') as f:
            json.dump(response_data, f)
        
        print(f"💾 Cached: {key[:8]}...")

# Usage
cache = ImageCache()

# Vérifier cache avant génération
cached = cache.get(prompt, '1024x1024', 'standard')
if cached:
    image_url = cached['url']
else:
    response = client.images.generate(...)
    cache.set(prompt, '1024x1024', 'standard', {
        'url': response.data[0].url,
        'revised_prompt': response.data[0].revised_prompt
    })
```

---

## 🔌 Problèmes Intégration

### 18. 🐋 Docker Services Not Starting

#### Diagnostic
```bash
# Vérifier status services
docker-compose ps

# Logs services
docker-compose logs

# Vérifier ressources
docker system df
```

#### Solutions

**Solution 1: Restart Clean**
```bash
# Arrêter tout
docker-compose down

# Nettoyer
docker system prune -a --volumes

# Redémarrer
docker-compose up -d
```

**Solution 2: Vérifier Ports**
```bash
# Vérifier ports disponibles
netstat -tuln | grep 8188  # ComfyUI
netstat -tuln | grep 8000  # Qwen

# Si port occupé, modifier docker-compose.yml
ports:
  - "8189:8188"  # Port alternatif
```

---

### 19. 🔗 Integration avec Systèmes Externes

#### Issue: CORS Errors
```javascript
// Si appel depuis browser
Access-Control-Allow-Origin error
```

#### Solution: Proxy Backend
```python
from flask import Flask, request, jsonify
from flask_cors import CORS
import requests

app = Flask(__name__)
CORS(app)

@app.route('/api/generate', methods=['POST'])
def generate_image():
    """Proxy pour éviter CORS"""
    data = request.json
    
    # Call OpenAI
    response = client.images.generate(
        model="dall-e-3",
        prompt=data['prompt'],
        size=data.get('size', '1024x1024')
    )
    
    return jsonify({
        'url': response.data[0].url,
        'revised_prompt': response.data[0].revised_prompt
    })

if __name__ == '__main__':
    app.run(port=5000)
```

---

## 🛠️ Scripts Diagnostiques

### Script 1: Health Check Complet

```python
#!/usr/bin/env python3
"""
health_check.py - Diagnostic complet écosystème GenAI
"""

import os
import sys
from pathlib import Path
from dotenv import load_dotenv
import requests

def check_environment():
    """Vérifie configuration environnement"""
    print("🔍 Vérification Environnement...")
    
    checks = {
        '.env exists': Path('.env').exists(),
        'Python >= 3.10': sys.version_info >= (3, 10),
        'OpenAI key set': bool(os.getenv('OPENAI_API_KEY')),
        'OpenRouter key set': bool(os.getenv('OPENROUTER_API_KEY'))
    }
    
    for check, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"  {status} {check}")
    
    return all(checks.values())

def check_apis():
    """Teste connectivité APIs"""
    print("\n🌐 Test APIs...")
    
    results = {}
    
    # OpenAI
    try:
        from openai import OpenAI
        client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        models = client.models.list()
        results['OpenAI'] = True
        print("  ✅ OpenAI API")
    except Exception as e:
        results['OpenAI'] = False
        print(f"  ❌ OpenAI API: {e}")
    
    # OpenRouter
    try:
        client = OpenAI(
            api_key=os.getenv("OPENROUTER_API_KEY"),
            base_url="https://openrouter.ai/api/v1"
        )
        response = client.chat.completions.create(
            model="openai/gpt-4-turbo",
            messages=[{"role": "user", "content": "test"}],
            max_tokens=5
        )
        results['OpenRouter'] = True
        print("  ✅ OpenRouter API")
    except Exception as e:
        results['OpenRouter'] = False
        print(f"  ❌ OpenRouter API: {e}")
    
    return results

def check_dependencies():
    """Vérifie dépendances Python"""
    print("\n📦 Vérification Dépendances...")
    
    required = {
        'openai': '1.3.0',
        'Pillow': '10.0.0',
        'requests': '2.31.0',
        'jupyter': '1.0.0'
    }
    
    results = {}
    for package, min_version in required.items():
        try:
            __import__(package)
            results[package] = True
            print(f"  ✅ {package}")
        except ImportError:
            results[package] = False
            print(f"  ❌ {package} (requis: >={min_version})")
    
    return results

def main():
    """Exécution diagnostic complet"""
    print("=" * 60)
    print("🏥 DIAGNOSTIC COMPLET - GenAI Images CoursIA")
    print("=" * 60)
    
    # Load environment
    load_dotenv()
    
    # Run checks
    env_ok = check_environment()
    api_results = check_apis()
    dep_results = check_dependencies()
    
    # Summary
    print("\n" + "=" * 60)
    print("📊 RÉSUMÉ")
    print("=" * 60)
    
    all_ok = (
        env_ok and
        all(api_results.values()) and
        all(dep_results.values())
    )
    
    if all_ok:
        print("✅ Tous les tests passés ! Système prêt.")
        sys.exit(0)
    else:
        print("❌ Certains tests ont échoué. Voir détails ci-dessus.")
        sys.exit(1)

if __name__ == '__main__':
    main()
```

**Usage** :
```bash
python scripts/health_check.py
```

---

### Script 2: Cost Calculator

```python
#!/usr/bin/env python3
"""
cost_calculator.py - Estimateur coûts GenAI
"""

def calculate_project_cost(num_images, size='1024x1024', quality='standard'):
    """Estime coût projet"""
    
    costs = {
        ('1024x1024', 'standard'): 0.040,
        ('1024x1024', 'hd'): 0.080,
        ('1024x1792', 'standard'): 0.080,
        ('1024x1792', 'hd'): 0.120,
        ('1792x1024', 'standard'): 0.080,
        ('1792x1024', 'hd'): 0.120
    }
    
    cost_per_image = costs.get((size, quality), 0.040)
    total = num_images * cost_per_image
    
    print(f"💰 Estimation Coûts Projet")
    print(f"=" * 40)
    print(f"Images: {num_images}")
    print(f"Taille: {size}")
    print(f"Qualité: {quality}")
    print(f"Coût unitaire: ${cost_per_image:.3f}")
    print(f"=" * 40)
    print(f"TOTAL: ${total:.2f}")
    
    return total

if __name__ == '__main__':
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python cost_calculator.py <num_images> [size] [quality]")
        sys.exit(1)
    
    num_images = int(sys.argv[1])
    size = sys.argv[2] if len(sys.argv) > 2 else '1024x1024'
    quality = sys.argv[3] if len(sys.argv) > 3 else 'standard'
    
    calculate_project_cost(num_images, size, quality)
```

**Usage** :
```bash
# Estimer 50 images standard
python scripts/cost_calculator.py 50

# Estimer 20 images HD landscape
python scripts/cost_calculator.py 20 1792x1024 hd
```

---

## 📞 Support & Escalation

### Niveaux de Support

#### Niveau 1: Auto-diagnostic
1. Consulter ce guide TROUBLESHOOTING
2. Exécuter scripts diagnostiques
3. Rechercher dans FAQ ([INDEX.md](INDEX.md))

#### Niveau 2: Documentation
1. Consulter tutoriels complets ([`tutorials/`](tutorials/))
2. Vérifier exemples sectoriels ([`examples/`](examples/))
3. Lire docs techniques ([`docs/genai/`](../../docs/genai/))

#### Niveau 3: Community Support
- 💬 **Discord**: [CoursIA Community](https://discord.gg/coursia)
- 📧 **Forum**: [forum.coursia.ai/genai](https://forum.coursia.ai/genai)
- 📚 **Stack Overflow**: Tag `coursia-genai`

#### Niveau 4: Technical Support
- 📧 **Email**: support@coursia.ai
- 🎫 **Tickets**: [support.coursia.ai](https://support.coursia.ai)
- ⏰ **Horaires**: Lun-Ven 9h-18h CET

---

### Informations à Fournir pour Support

#### Template Ticket Support

```markdown
**Environnement**
- OS: [Windows 11 / macOS 13 / Ubuntu 22.04]
- Python: [3.11.5]
- Notebook: [01-1-Generation-Image-Texte-API.ipynb]

**Problème**
[Description détaillée du problème]

**Erreur**
```
[Copier-coller message d'erreur complet avec stack trace]
```

**Étapes pour Reproduire**
1. [Étape 1]
2. [Étape 2]
3. [Résultat observé]

**Comportement Attendu**
[Ce qui devrait se passer]

**Tentatives de Résolution**
- [ ] Vérifié .env configuration
- [ ] Exécuté health_check.py
- [ ] Consulté TROUBLESHOOTING.md
- [ ] Testé avec autre notebook

**Logs/Screenshots**
[Joindre fichiers pertinents]
```

---

### Escalation Procédure

**Problèmes Critiques (P0)** :
- Services complètement indisponibles
- Perte de données
- Failles sécurité

**Action** : Email immédiat à emergency@coursia.ai

**Problèmes Majeurs (P1)** :
- Fonctionnalités principales cassées
- Blocage développement
- Erreurs APIs persistantes

**Action** : Ticket support avec priorité haute

**Problèmes Mineurs (P2)** :
- Bugs non-bloquants
- Problèmes performance
- Questions usage

**Action** : Ticket support standard ou community

---

## 📚 Ressources Additionnelles

### Documentation Officielle
- [OpenAI API Docs](https://platform.openai.com/docs)
- [OpenRouter Documentation](https://openrouter.ai/docs)
- [Pillow Documentation](https://pillow.readthedocs.io/)
- [Papermill Guide](https://papermill.readthedocs.io/)

### Guides CoursIA
- [INDEX Complet](INDEX.md)
- [DEPLOYMENT Guide](DEPLOYMENT.md)
- [Tutorials Complets](tutorials/)

### Communauté
- [Discord CoursIA](https://discord.gg/coursia)
- [GitHub Discussions](https://github.com/coursia/genai/discussions)
- [Twitter @CoursIA](https://twitter.com/coursia)

---

**Version** : 1.0.0  
**Dernière mise à jour** : 2025-10-08  
**Maintainers** : Équipe Support CoursIA

---

💡 **Problème non résolu ?** Contactez-nous sur support@coursia.ai