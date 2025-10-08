# 🚀 DEPLOYMENT GUIDE - GenAI Images Production

> **Guide complet de déploiement en production**  
> APIs Externes | Sécurité | Monitoring | Scaling | Best Practices

---

## 📑 Table des Matières

1. [Vue d'Ensemble](#vue-densemble)
2. [Environnements](#environnements)
3. [Configuration Production](#configuration-production)
4. [Sécurité](#sécurité)
5. [Monitoring et Alerting](#monitoring-et-alerting)
6. [Backup et Restore](#backup-et-restore)
7. [Scaling Strategies](#scaling-strategies)
8. [CI/CD Pipelines](#cicd-pipelines)
9. [Cost Optimization](#cost-optimization)
10. [Maintenance](#maintenance)
11. [Disaster Recovery](#disaster-recovery)

---

## 🎯 Vue d'Ensemble

### Architecture Déploiement

L'écosystème GenAI Images CoursIA utilise une architecture **hybride** :

- **APIs Externes** (OpenAI, OpenRouter) : Production-ready ✅
- **Infrastructure Docker** (FLUX, SD 3.5) : En cours 🚧

Ce guide couvre le déploiement des **APIs externes configurées**.

### Environnements Cibles

```
Development  →  Staging  →  Production
    ↓            ↓            ↓
  Local      Test APIs    Live Users
 (dev.env)   (stg.env)   (prod.env)
```

### Prérequis Production

- ✅ Environnement configuré ([`00-1-Environment-Setup.ipynb`](00-GenAI-Environment/00-1-Environment-Setup.ipynb))
- ✅ APIs validées ([`00-4-Environment-Validation.ipynb`](00-GenAI-Environment/00-4-Environment-Validation.ipynb))
- ✅ Tests passés (voir [TROUBLESHOOTING.md](TROUBLESHOOTING.md))
- ✅ Budget configuré (alertes activées)
- ✅ Monitoring en place

---

## 🌍 Environnements

### 1. Development (Local)

**Caractéristiques** :
- Environnement local développeur
- APIs test/sandbox si disponibles
- Logs verbeux
- Pas de rate limiting

**Configuration `.env.dev`** :
```bash
# Development Environment
ENV_NAME=development
DEBUG=true
LOG_LEVEL=DEBUG

# APIs - Clés développement
OPENAI_API_KEY=sk-dev-...
OPENROUTER_API_KEY=sk-or-dev-...

# Limites relâchées
MAX_IMAGES_PER_REQUEST=10
RATE_LIMIT_PER_MINUTE=50
ENABLE_CACHING=true
```

**Usage** :
```bash
# Charger env development
export ENV_FILE=.env.dev
python -m dotenv run python app.py
```

---

### 2. Staging (Pre-Production)

**Caractéristiques** :
- Réplique production
- APIs production avec budget limité
- Tests end-to-end
- Monitoring actif

**Configuration `.env.staging`** :
```bash
# Staging Environment
ENV_NAME=staging
DEBUG=false
LOG_LEVEL=INFO

# APIs - Clés staging (même que prod mais projet séparé)
OPENAI_API_KEY=sk-stg-...
OPENROUTER_API_KEY=sk-or-stg-...

# Limites production-like
MAX_IMAGES_PER_REQUEST=5
RATE_LIMIT_PER_MINUTE=30
ENABLE_CACHING=true
CACHE_TTL=3600

# Monitoring
SENTRY_DSN=https://...@sentry.io/staging
```

**Déploiement** :
```bash
# Deploy to staging
./scripts/deploy.sh staging

# Run smoke tests
pytest tests/integration/ --env=staging
```

---

### 3. Production (Live)

**Caractéristiques** :
- Environnement utilisateurs finaux
- APIs production avec budget strict
- Monitoring 24/7
- Alerting automatique
- Backups réguliers

**Configuration `.env.production`** :
```bash
# Production Environment
ENV_NAME=production
DEBUG=false
LOG_LEVEL=WARNING

# APIs - Clés production
OPENAI_API_KEY=sk-prod-...
OPENROUTER_API_KEY=sk-or-prod-...

# Limites strictes
MAX_IMAGES_PER_REQUEST=3
RATE_LIMIT_PER_MINUTE=20
ENABLE_CACHING=true
CACHE_TTL=7200

# Security
CORS_ORIGINS=https://coursia.ai,https://app.coursia.ai
API_KEY_ROTATION_DAYS=90

# Monitoring
SENTRY_DSN=https://...@sentry.io/production
SENTRY_ENVIRONMENT=production
DATADOG_API_KEY=...
ENABLE_PERFORMANCE_TRACKING=true

# Cost Controls
DAILY_BUDGET_LIMIT=50.00
COST_ALERT_THRESHOLD=0.80
AUTO_PAUSE_ON_BUDGET_EXCEEDED=true
```

---

## ⚙️ Configuration Production

### 1. Variables d'Environnement

#### Structure Recommandée

```python
# config/production.py
"""Configuration production centralisée"""

import os
from dataclasses import dataclass
from typing import Optional

@dataclass
class ProductionConfig:
    """Configuration production type-safe"""
    
    # Environment
    env_name: str = "production"
    debug: bool = False
    log_level: str = "WARNING"
    
    # APIs
    openai_api_key: str = os.getenv("OPENAI_API_KEY", "")
    openrouter_api_key: str = os.getenv("OPENROUTER_API_KEY", "")
    
    # Rate Limiting
    max_images_per_request: int = 3
    rate_limit_per_minute: int = 20
    
    # Caching
    enable_caching: bool = True
    cache_ttl: int = 7200
    redis_url: Optional[str] = os.getenv("REDIS_URL")
    
    # Cost Controls
    daily_budget_limit: float = 50.0
    cost_alert_threshold: float = 0.80
    auto_pause_on_budget: bool = True
    
    # Monitoring
    sentry_dsn: Optional[str] = os.getenv("SENTRY_DSN")
    datadog_api_key: Optional[str] = os.getenv("DATADOG_API_KEY")
    
    def validate(self):
        """Valide configuration"""
        errors = []
        
        if not self.openai_api_key:
            errors.append("OPENAI_API_KEY manquante")
        
        if not self.openrouter_api_key:
            errors.append("OPENROUTER_API_KEY manquante")
        
        if self.daily_budget_limit <= 0:
            errors.append("DAILY_BUDGET_LIMIT invalide")
        
        if errors:
            raise ValueError(f"Configuration invalide: {', '.join(errors)}")
        
        return True

# Load et valide
config = ProductionConfig()
config.validate()
```

---

### 2. Gestion Secrets

#### AWS Secrets Manager

```python
import boto3
import json

def load_secrets_from_aws():
    """Charge secrets depuis AWS Secrets Manager"""
    
    client = boto3.client('secretsmanager', region_name='us-east-1')
    
    try:
        response = client.get_secret_value(
            SecretId='coursia/genai/production'
        )
        secrets = json.loads(response['SecretString'])
        
        # Injecter dans environnement
        os.environ['OPENAI_API_KEY'] = secrets['openai_api_key']
        os.environ['OPENROUTER_API_KEY'] = secrets['openrouter_api_key']
        
        print("✅ Secrets chargés depuis AWS")
        return True
        
    except Exception as e:
        print(f"❌ Erreur chargement secrets: {e}")
        return False
```

#### Azure Key Vault

```python
from azure.keyvault.secrets import SecretClient
from azure.identity import DefaultAzureCredential

def load_secrets_from_azure():
    """Charge secrets depuis Azure Key Vault"""
    
    vault_url = "https://coursia-genai.vault.azure.net/"
    credential = DefaultAzureCredential()
    client = SecretClient(vault_url=vault_url, credential=credential)
    
    try:
        # Récupérer secrets
        openai_key = client.get_secret("openai-api-key").value
        openrouter_key = client.get_secret("openrouter-api-key").value
        
        # Injecter
        os.environ['OPENAI_API_KEY'] = openai_key
        os.environ['OPENROUTER_API_KEY'] = openrouter_key
        
        print("✅ Secrets chargés depuis Azure")
        return True
        
    except Exception as e:
        print(f"❌ Erreur: {e}")
        return False
```

#### Kubernetes Secrets

```yaml
# k8s/secrets.yaml
apiVersion: v1
kind: Secret
metadata:
  name: genai-api-keys
  namespace: coursia-production
type: Opaque
stringData:
  openai-api-key: sk-prod-...
  openrouter-api-key: sk-or-prod-...
```

```python
# Dans pod, secrets montés comme env vars
import os

openai_key = os.environ['OPENAI_API_KEY']
openrouter_key = os.environ['OPENROUTER_API_KEY']
```

---

## 🔒 Sécurité

### 1. API Keys Protection

#### Rotation Automatique

```python
from datetime import datetime, timedelta

class APIKeyRotation:
    """Gestion rotation clés API"""
    
    def __init__(self, rotation_days=90):
        self.rotation_days = rotation_days
        self.last_rotation = self.load_last_rotation()
    
    def needs_rotation(self):
        """Vérifie si rotation nécessaire"""
        if not self.last_rotation:
            return True
        
        age = datetime.now() - self.last_rotation
        return age.days >= self.rotation_days
    
    def rotate_keys(self):
        """Rotate API keys (manuel + notification)"""
        if not self.needs_rotation():
            print("✅ Rotation pas encore nécessaire")
            return
        
        print("⚠️ ROTATION CLÉS API NÉCESSAIRE")
        print("Actions requises:")
        print("1. Créer nouvelles clés sur platforms")
        print("2. Mettre à jour secrets manager")
        print("3. Tester en staging")
        print("4. Déployer en production")
        print("5. Révoquer anciennes clés après 7 jours")
        
        # Envoyer notification
        self.send_rotation_alert()
    
    def send_rotation_alert(self):
        """Envoie alerte rotation"""
        # Email, Slack, etc.
        pass
```

#### Rate Limiting par Clé

```python
from collections import defaultdict
from datetime import datetime, timedelta

class APIKeyRateLimiter:
    """Rate limiter par clé API"""
    
    def __init__(self):
        self.usage = defaultdict(list)
        self.limits = {
            'requests_per_minute': 20,
            'daily_budget': 50.0
        }
    
    def can_proceed(self, api_key_hash, cost=0):
        """Vérifie si requête autorisée"""
        now = datetime.now()
        
        # Nettoyer anciennes entrées
        self.usage[api_key_hash] = [
            entry for entry in self.usage[api_key_hash]
            if now - entry['timestamp'] < timedelta(minutes=1)
        ]
        
        # Vérifier limite requêtes
        if len(self.usage[api_key_hash]) >= self.limits['requests_per_minute']:
            return False, "Rate limit exceeded"
        
        # Vérifier budget journalier
        daily_cost = sum(
            entry['cost'] for entry in self.usage[api_key_hash]
            if now - entry['timestamp'] < timedelta(days=1)
        )
        
        if daily_cost + cost > self.limits['daily_budget']:
            return False, "Daily budget exceeded"
        
        return True, "OK"
    
    def log_request(self, api_key_hash, cost):
        """Log requête"""
        self.usage[api_key_hash].append({
            'timestamp': datetime.now(),
            'cost': cost
        })
```

---

### 2. Network Security

#### HTTPS Obligatoire

```python
from flask import Flask, request, abort

app = Flask(__name__)

@app.before_request
def enforce_https():
    """Force HTTPS en production"""
    if not request.is_secure and app.config['ENV'] == 'production':
        abort(403, "HTTPS required")
```

#### CORS Configuration

```python
from flask_cors import CORS

# Configuration stricte production
CORS(app, resources={
    r"/api/*": {
        "origins": [
            "https://coursia.ai",
            "https://app.coursia.ai"
        ],
        "methods": ["GET", "POST"],
        "allow_headers": ["Content-Type", "Authorization"],
        "max_age": 3600
    }
})
```

#### Input Validation

```python
from pydantic import BaseModel, validator, Field

class ImageGenerationRequest(BaseModel):
    """Validation requête génération"""
    
    prompt: str = Field(..., min_length=10, max_length=1000)
    size: str = Field(default="1024x1024")
    quality: str = Field(default="standard")
    
    @validator('prompt')
    def validate_prompt(cls, v):
        """Valide prompt (sécurité)"""
        # Bloquer contenus dangereux
        forbidden = ['hack', 'exploit', 'inject']
        if any(word in v.lower() for word in forbidden):
            raise ValueError("Prompt contains forbidden content")
        return v
    
    @validator('size')
    def validate_size(cls, v):
        """Valide taille"""
        allowed = ['1024x1024', '1024x1792', '1792x1024']
        if v not in allowed:
            raise ValueError(f"Size must be one of {allowed}")
        return v
    
    @validator('quality')
    def validate_quality(cls, v):
        """Valide qualité"""
        if v not in ['standard', 'hd']:
            raise ValueError("Quality must be 'standard' or 'hd'")
        return v
```

---

### 3. Audit Logging

```python
import logging
import json
from datetime import datetime

class AuditLogger:
    """Logger audit production"""
    
    def __init__(self):
        self.logger = logging.getLogger('audit')
        
        # Handler JSON structuré
        handler = logging.FileHandler('logs/audit.log')
        handler.setFormatter(self.JsonFormatter())
        self.logger.addHandler(handler)
        self.logger.setLevel(logging.INFO)
    
    class JsonFormatter(logging.Formatter):
        """Format JSON pour logs"""
        def format(self, record):
            return json.dumps({
                'timestamp': datetime.utcnow().isoformat(),
                'level': record.levelname,
                'message': record.getMessage(),
                'extra': getattr(record, 'extra', {})
            })
    
    def log_api_call(self, user_id, endpoint, params, response_code, cost=0):
        """Log appel API"""
        self.logger.info(
            "API call",
            extra={
                'user_id': user_id,
                'endpoint': endpoint,
                'params': params,
                'response_code': response_code,
                'cost': cost
            }
        )
    
    def log_error(self, user_id, error_type, error_msg):
        """Log erreur"""
        self.logger.error(
            "Error occurred",
            extra={
                'user_id': user_id,
                'error_type': error_type,
                'error_msg': error_msg
            }
        )

# Usage
audit = AuditLogger()
audit.log_api_call(
    user_id='user123',
    endpoint='/api/generate',
    params={'prompt': 'test', 'size': '1024x1024'},
    response_code=200,
    cost=0.040
)
```

---

## 📊 Monitoring et Alerting

### 1. Health Checks

```python
from flask import Flask, jsonify
import time

app = Flask(__name__)

@app.route('/health')
def health_check():
    """Endpoint health check"""
    
    checks = {
        'status': 'healthy',
        'timestamp': time.time(),
        'checks': {}
    }
    
    # Vérifier APIs externes
    checks['checks']['openai'] = check_openai_api()
    checks['checks']['openrouter'] = check_openrouter_api()
    
    # Vérifier cache
    checks['checks']['cache'] = check_cache_connection()
    
    # Vérifier stockage
    checks['checks']['storage'] = check_storage_available()
    
    # Status global
    all_healthy = all(
        c['status'] == 'ok' 
        for c in checks['checks'].values()
    )
    
    checks['status'] = 'healthy' if all_healthy else 'degraded'
    
    return jsonify(checks), 200 if all_healthy else 503

def check_openai_api():
    """Vérifie OpenAI API"""
    try:
        from openai import OpenAI
        client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        client.models.list()
        return {'status': 'ok', 'latency_ms': 50}
    except Exception as e:
        return {'status': 'error', 'error': str(e)}
```

---

### 2. Métriques

```python
from prometheus_client import Counter, Histogram, Gauge
import time

# Métriques Prometheus
api_requests_total = Counter(
    'genai_api_requests_total',
    'Total API requests',
    ['endpoint', 'status']
)

api_request_duration = Histogram(
    'genai_api_request_duration_seconds',
    'API request duration',
    ['endpoint']
)

api_cost_total = Counter(
    'genai_api_cost_total_dollars',
    'Total API cost',
    ['model']
)

active_generations = Gauge(
    'genai_active_generations',
    'Number of active image generations'
)

class MetricsMiddleware:
    """Middleware métriques"""
    
    def __init__(self, app):
        self.app = app
    
    def __call__(self, environ, start_response):
        """Capture métriques par requête"""
        
        start = time.time()
        path = environ.get('PATH_INFO', '')
        
        def custom_start_response(status, headers):
            status_code = int(status.split()[0])
            duration = time.time() - start
            
            # Enregistrer métriques
            api_requests_total.labels(
                endpoint=path,
                status=status_code
            ).inc()
            
            api_request_duration.labels(
                endpoint=path
            ).observe(duration)
            
            return start_response(status, headers)
        
        return self.app(environ, custom_start_response)
```

---

### 3. Alerting

#### Configuration Alertes

```yaml
# alerting/rules.yaml
groups:
  - name: genai_alerts
    interval: 30s
    rules:
      # Erreur rate élevé
      - alert: HighErrorRate
        expr: |
          rate(genai_api_requests_total{status=~"5.."}[5m]) > 0.05
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Taux d'erreur élevé ({{ $value }})"
          
      # Budget dépassé
      - alert: BudgetExceeded
        expr: |
          genai_api_cost_total_dollars > 45
        labels:
          severity: critical
        annotations:
          summary: "Budget journalier 90% atteint"
          
      # Latence élevée
      - alert: HighLatency
        expr: |
          histogram_quantile(0.95, 
            rate(genai_api_request_duration_seconds_bucket[5m])
          ) > 60
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Latence p95 > 60s"
```

#### Notifications

```python
import requests

class AlertManager:
    """Gestionnaire alertes"""
    
    def __init__(self):
        self.slack_webhook = os.getenv("SLACK_WEBHOOK_URL")
        self.email_api = os.getenv("EMAIL_API_URL")
    
    def send_slack_alert(self, message, severity='warning'):
        """Envoie alerte Slack"""
        
        colors = {
            'info': '#36a64f',
            'warning': '#ff9900',
            'critical': '#ff0000'
        }
        
        payload = {
            'attachments': [{
                'color': colors.get(severity, '#808080'),
                'title': f'🚨 GenAI Alert - {severity.upper()}',
                'text': message,
                'ts': int(time.time())
            }]
        }
        
        try:
            response = requests.post(
                self.slack_webhook,
                json=payload,
                timeout=5
            )
            return response.ok
        except Exception as e:
            print(f"Erreur Slack: {e}")
            return False
    
    def send_email_alert(self, subject, body, recipients):
        """Envoie alerte email"""
        
        payload = {
            'to': recipients,
            'subject': subject,
            'body': body,
            'priority': 'high'
        }
        
        try:
            response = requests.post(
                self.email_api,
                json=payload,
                headers={'Authorization': f'Bearer {os.getenv("EMAIL_API_KEY")}'},
                timeout=5
            )
            return response.ok
        except Exception as e:
            print(f"Erreur email: {e}")
            return False

# Usage
alerts = AlertManager()

# Budget warning
if daily_cost > daily_budget * 0.8:
    alerts.send_slack_alert(
        f"⚠️ Budget à 80%: ${daily_cost:.2f} / ${daily_budget:.2f}",
        severity='warning'
    )
```

---

## 💾 Backup et Restore

### 1. Stratégie Backup

```python
from pathlib import Path
import shutil
import json
from datetime import datetime

class BackupManager:
    """Gestionnaire backups"""
    
    def __init__(self, backup_dir="backups"):
        self.backup_dir = Path(backup_dir)
        self.backup_dir.mkdir(exist_ok=True)
    
    def create_backup(self):
        """Crée backup complet"""
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup_name = f"genai_backup_{timestamp}"
        backup_path = self.backup_dir / backup_name
        backup_path.mkdir()
        
        print(f"📦 Création backup: {backup_name}")
        
        # Backup configuration
        self.backup_config(backup_path)
        
        # Backup generated images
        self.backup_outputs(backup_path)
        
        # Backup logs
        self.backup_logs(backup_path)
        
        # Backup cache
        self.backup_cache(backup_path)
        
        # Créer archive
        archive_path = shutil.make_archive(
            str(backup_path),
            'gztar',
            self.backup_dir,
            backup_name
        )
        
        # Nettoyer dossier temporaire
        shutil.rmtree(backup_path)
        
        print(f"✅ Backup créé: {archive_path}")
        return archive_path
    
    def backup_config(self, backup_path):
        """Backup configuration (sans secrets)"""
        config_backup = backup_path / "config"
        config_backup.mkdir()
        
        # Copier fichiers config (hors .env)
        for config_file in ['.env.example', 'requirements.txt']:
            src = Path(config_file)
            if src.exists():
                shutil.copy(src, config_backup / config_file)
    
    def backup_outputs(self, backup_path):
        """Backup images générées"""
        outputs_src = Path("outputs")
        if outputs_src.exists():
            shutil.copytree(
                outputs_src,
                backup_path / "outputs"
            )
    
    def restore_backup(self, backup_archive):
        """Restore depuis backup"""
        
        print(f"🔄 Restoration backup: {backup_archive}")
        
        # Extraire archive
        shutil.unpack_archive(backup_archive, self.backup_dir)
        
        backup_name = Path(backup_archive).stem
        backup_path = self.backup_dir / backup_name
        
        # Restore outputs
        outputs_backup = backup_path / "outputs"
        if outputs_backup.exists():
            shutil.copytree(
                outputs_backup,
                "outputs",
                dirs_exist_ok=True
            )
        
        print("✅ Restoration complétée")

# Automatisation backups
def schedule_backups():
    """Schedule backups réguliers"""
    import schedule
    
    manager = BackupManager()
    
    # Backup quotidien à 2h du matin
    schedule.every().day.at("02:00").do(manager.create_backup)
    
    # Cleanup anciens backups (>30 jours)
    schedule.every().week.do(lambda: manager.cleanup_old_backups(days=30))
    
    while True:
        schedule.run_pending()
        time.sleep(60)
```

---

## 📈 Scaling Strategies

### 1. Horizontal Scaling

```python
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue

class ImageGenerationPool:
    """Pool workers pour génération parallèle"""
    
    def __init__(self, max_workers=5):
        self.max_workers = max_workers
        self.queue = queue.Queue()
        self.results = {}
    
    def submit_batch(self, prompts):
        """Soumet batch de génération"""
        
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            # Soumettre tous les prompts
            future_to_prompt = {
                executor.submit(self.generate_one, prompt): prompt
                for prompt in prompts
            }
            
            # Collecter résultats
            for future in as_completed(future_to_prompt):
                prompt = future_to_prompt[future]
                try:
                    result = future.result()
                    self.results[prompt] = result
                except Exception as e:
                    print(f"❌ Erreur {prompt}: {e}")
        
        return self.results
    
    def generate_one(self, prompt):
        """Génère une image"""
        from openai import OpenAI
        
        client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        response = client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size="1024x1024"
        )
        
        return {
            'url': response.data[0].url,
            'revised_prompt': response.data[0].revised_prompt
        }
```

---

### 2. Queue-Based Architecture

```python
import redis
import json
from enum import Enum

class JobStatus(Enum):
    PENDING = "pending"
    PROCESSING = "processing"
    COMPLETED = "completed"
    FAILED = "failed"

class JobQueue:
    """Queue Redis pour jobs asynchrones"""
    
    def __init__(self, redis_url='redis://localhost:6379'):
        self.redis = redis.from_url(redis_url)
        self.queue_name = 'genai:jobs'
    
    def enqueue(self, job_data):
        """Ajoute job à la queue"""
        
        job_id = f"job:{int(time.time()*1000)}"
        
        job = {
            'id': job_id,
            'status': JobStatus.PENDING.value,
            'data': job_data,
            'created_at': time.time()
        }
        
        # Stocker job
        self.redis.hset(
            f'job:{job_id}',
            mapping={k: json.dumps(v) for k, v in job.items()}
        )
        
        # Ajouter à queue
        self.redis.lpush(self.queue_name, job_id)
        
        return job_id
    
    def dequeue(self, timeout=5):
        """Récupère job de la queue"""
        
        result = self.redis.brpop(self.queue_name, timeout=timeout)
        if not result:
            return None
        
        _, job_id = result
        job_data = self.redis.hgetall(f'job:{job_id}')
        
        return {
            k.decode(): json.loads(v.decode())
            for k, v in job_data.items()
        }
    
    def update_status(self, job_id, status, result=None):
        """Met à jour status job"""
        
        updates = {
            'status': json.dumps(status.value),
            'updated_at': json.dumps(time.time())
        }
        
        if result:
            updates['result'] = json.dumps(result)
        
        self.redis.hset(f'job:{job_id}', mapping=updates)
    
    def get_job(self, job_id):
        """Récupère infos job"""
        
        job_data = self.redis.hgetall(f'job:{job_id}')
        
        if not job_data:
            return None
        
        return {
            k.decode(): json.loads(v.decode())
            for k, v in job_data.items()
        }

# Worker
def worker():
    """Worker process génération"""
    
    queue = JobQueue()
    
    while True:
        # Récupérer job
        job = queue.dequeue(timeout=5)
        if not job:
            continue
        
        job_id = job['id']
        print(f"⚙️ Processing {job_id}")
        
        # Marquer en cours
        queue.update_status(job_id, JobStatus.PROCESSING)
        
        try:
            # Générer image
            result = generate_image(job['data'])
            
            # Marquer complété
            queue.update_status(job_id, JobStatus.COMPLETED, result)
            print(f"✅ Completed {job_id}")
            
        except Exception as e:
            # Marquer échoué
            queue.update_status(job_id, JobStatus.FAILED, {'error': str(e)})
            print(f"❌ Failed {job_id}: {e}")
```

---

## 🔄 CI/CD Pipelines

### GitHub Actions

```yaml
# .github/workflows/deploy-production.yml
name: Deploy to Production

on:
  push:
    branches: [main]
    paths:
      - 'MyIA.AI.Notebooks/GenAI/**'

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      
      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install pytest pytest-cov
      
      - name: Run tests
        env:
          OPENAI_API_KEY: ${{ secrets.OPENAI_API_KEY_TEST }}
        run: pytest tests/ --cov
      
      - name: Upload coverage
        uses: codecov/codecov-action@v3
  
  deploy:
    needs: test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Deploy to production
        env:
          DEPLOY_KEY: ${{ secrets.DEPLOY_KEY }}
        run: |
          ./scripts/deploy.sh production
      
      - name: Run smoke tests
        run: |
          pytest tests/smoke/ --env=production
      
      - name: Notify Slack
        if: success()
        uses: 8398a7/action-slack@v3
        with:
          status: ${{ job.status }}
          text: '✅ Deployment successful'
          webhook_url: ${{ secrets.SLACK_WEBHOOK }}
```

---

## 💰 Cost Optimization

### Stratégies Production

```python
class CostOptimizer:
    """Optimiseur coûts production"""
    
    def __init__(self):
        self.cache = ImageCache()
        self.costs = []
    
    def optimize_request(self, prompt, size='1024x1024', quality='standard'):
        """Optimise requête pour minimiser coûts"""
        
        # 1. Vérifier cache
        cached = self.cache.get(prompt, size, quality)
        if cached:
            print("💾 Cache hit - $0.00")
            return cached
        
        # 2. Downgrade qualité si possible
        if quality == 'hd' and self.can_use_standard(prompt):
            print("⬇️ Downgrade HD→Standard - Économie $0.04")
            quality = 'standard'
        
        # 3. Réduire résolution si acceptable
        if size in ['1024x1792', '1792x1024'] and self.can_use_square(prompt):
            print("⬇️ Réduction résolution - Économie $0.04")
            size = '1024x1024'
        
        # 4. Génération
        result = self.generate(prompt, size, quality)
        
        # 5. Cache résultat
        self.cache.set(prompt, size, quality, result)
        
        return result
    
    def can_use_standard(self, prompt):
        """Détermine si standard quality suffisante"""
        # Pour éducatif, standard souvent suffisant
        educational_keywords = [
            'diagramme', 'schéma', 'illustration pédagogique'
        ]
        return any(kw in prompt.lower() for kw in educational_keywords)
    
    def can_use_square(self, prompt):
        """Détermine si format carré acceptable"""
        # Éviter square pour paysages/portraits explicites
        requires_portrait = any(
            word in prompt.lower() 
            for word in ['portrait', 'vertical', 'tall']
        )
        requires_landscape = any(
            word in prompt.lower()
            for word in ['paysage', 'horizontal', 'wide', 'panorama']
        )
        return not (requires_portrait or requires_landscape)
```

---

## 🔧 Maintenance

### Tâches Régulières

```python
import schedule

def daily_maintenance():
    """Maintenance quotidienne"""
    print("🔧 Maintenance quotidienne...")
    
    # 1. Cleanup cache ancien
    cleanup_old_cache(days=7)
    
    # 2. Backup
    BackupManager().create_backup()
    
    # 3. Rotation logs
    rotate_logs()
    
    # 4. Rapport coûts
    generate_cost_report()
    
    print("✅ Maintenance terminée")

def weekly_maintenance():
    """Maintenance hebdomadaire"""
    print("🔧 Maintenance hebdomadaire...")
    
    # 1. Check API keys expiration
    check_api_keys_expiration()
    
    # 2. Performance review
    analyze_performance_metrics()
    
    # 3. Cleanup anciens backups
    cleanup_old_backups(days=30)
    
    print("✅ Maintenance terminée")

# Schedule
schedule.every().day.at("03:00").do(daily_maintenance)
schedule.every().monday.at("04:00").do(weekly_maintenance)
```

---

## 🆘 Disaster Recovery

### Plan de Reprise

```python
class DisasterRecovery:
    """Plan reprise activité"""
    
    def __init__(self):
        self.backup_manager = BackupManager()
        self.alerts = AlertManager()
    
    def detect_outage(self):
        """Détecte panne système"""
        
        checks = [
            self.check_api_connectivity(),
            self.check_service_health(),
            self.check_database_connection()
        ]
        
        if not all(checks):
            print("🚨 PANNE DÉTECTÉE")
            return True
        
        return False
    
    def execute_recovery(self):
        """Exécute procédure recovery"""
        
        print("🔄 Démarrage procédure recovery...")
        
        # 1. Notifier équipe
        self.alerts.send_email_alert(
            subject="🚨 DR Procedure Started",
            body="Disaster recovery en cours...",
            recipients=['ops@coursia.ai']
        )
        
        # 2. Restore dernier backup
        latest_backup = self.find_latest_backup()
        if latest_backup:
            self.backup_manager.restore_backup(latest_backup)
        
        # 3. Restart services
        self.restart_services()
        
        # 4. Verify health
        if self.verify_recovery():
            print("✅ Recovery réussie")
            self.alerts.send_slack_alert("✅ Services restored")
        else:
            print("❌ Recovery échouée - escalation")
            self.escalate_to_oncall()
    
    def escalate_to_oncall(self):
        """Escalade vers on-call"""
        # PagerDuty, OpsGenie, etc.
        pass
```

---

## 📚 Checklist Déploiement

### Pre-Deployment

- [ ] Tests unitaires passés
- [ ] Tests intégration passés
- [ ] Configuration production validée
- [ ] Secrets configurés
- [ ] Backup récent disponible
- [ ] Monitoring configuré
- [ ] Alerting testé
- [ ] Documentation à jour

### Deployment

- [ ] Déploiement staging réussi
- [ ] Smoke tests staging OK
- [ ] Déploiement production
- [ ] Health checks verts
- [ ] Smoke tests production OK

### Post-Deployment

- [ ] Monitoring actif 24h
- [ ] Métriques normales
- [ ] Pas d'alertes critiques
- [ ] Retours utilisateurs positifs
- [ ] Documentation déploiement mise à jour

---

**Version** : 1.0.0  
**Dernière mise à jour** : 2025-10-08  
**Équipe** : DevOps CoursIA

---

🚀 **Production Ready - GenAI Images CoursIA**