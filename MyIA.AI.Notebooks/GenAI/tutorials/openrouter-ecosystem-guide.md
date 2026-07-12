# Tutorial Complet : OpenRouter Écosystème pour CoursIA

## Table des Matières
1. [Introduction](#introduction)
2. [Configuration Endpoints Multiples](#configuration-endpoints)
3. [Switching entre Modèles](#switching-modeles)
4. [Rate Limiting et Cost Optimization](#rate-limiting-cost)
5. [API Management et Monitoring](#api-management)
6. [Error Handling et Retry Strategies](#error-handling)
7. [Production Best Practices](#production-best-practices)
8. [Integration Patterns CoursIA](#integration-patterns)

---

## Introduction

OpenRouter unifie l'accès à plus de 200 modèles d'IA (OpenAI, Anthropic, Google, etc.) via une API unique. Ce guide couvre l'écosystème complet pour CoursIA avec focus sur les APIs externes configurées.

### Modèles Disponibles CoursIA
- **GPT-5 Preview** : Analyse multimodale avancée
- **GPT-4 Turbo** : Génération texte haute qualité
- **DALL-E 3** : Génération images (via OpenAI direct)
- **Qwen-Image-Edit-2509** : Édition images (via proxy)
- **Claude 3.5 Sonnet** : Raisonnement complexe
- **Gemini Pro Vision** : Alternative multimodale

### Avantages OpenRouter
- **Unified API** : Une interface pour tous modèles
- **Cost optimization** : Comparaison prix automatique
- **Fallback automatique** : Si modèle indisponible
- **Usage analytics** : Dashboard intégré
- **Rate limiting intelligent** : Gestion quotas par modèle
- **Credits système** : Facturation unifiée

---

## Configuration Endpoints Multiples

### Setup Unifié

```python
import os
from openai import OpenAI
from typing import Optional, Dict, List
from dataclasses import dataclass
from enum import Enum

class ModelProvider(Enum):
    """Providers supportés"""
    OPENAI = "openai"
    OPENROUTER = "openrouter"
    ANTHROPIC = "anthropic"
    GOOGLE = "google"

@dataclass
class ModelConfig:
    """Configuration d'un modèle"""
    model_id: str
    provider: ModelProvider
    base_url: str
    api_key_env: str
    cost_per_1k_input: float
    cost_per_1k_output: float
    context_window: int
    capabilities: List[str]

# Configuration centralisée
MODEL_REGISTRY = {
    # OpenRouter models
    "gpt-5-preview": ModelConfig(
        model_id="openai/gpt-5-preview",
        provider=ModelProvider.OPENROUTER,
        base_url="https://openrouter.ai/api/v1",
        api_key_env="OPENROUTER_API_KEY",
        cost_per_1k_input=0.01,
        cost_per_1k_output=0.03,
        context_window=200000,
        capabilities=["text", "vision", "json", "function_calling"]
    ),
    
    "gpt-4-turbo": ModelConfig(
        model_id="openai/gpt-4-turbo",
        provider=ModelProvider.OPENROUTER,
        base_url="https://openrouter.ai/api/v1",
        api_key_env="OPENROUTER_API_KEY",
        cost_per_1k_input=0.01,
        cost_per_1k_output=0.03,
        context_window=128000,
        capabilities=["text", "json", "function_calling"]
    ),
    
    "claude-3.5-sonnet": ModelConfig(
        model_id="anthropic/claude-3.5-sonnet",
        provider=ModelProvider.OPENROUTER,
        base_url="https://openrouter.ai/api/v1",
        api_key_env="OPENROUTER_API_KEY",
        cost_per_1k_input=0.003,
        cost_per_1k_output=0.015,
        context_window=200000,
        capabilities=["text", "json", "artifacts"]
    ),
    
    "gemini-pro-vision": ModelConfig(
        model_id="google/gemini-pro-vision",
        provider=ModelProvider.OPENROUTER,
        base_url="https://openrouter.ai/api/v1",
        api_key_env="OPENROUTER_API_KEY",
        cost_per_1k_input=0.00025,
        cost_per_1k_output=0.0005,
        context_window=32000,
        capabilities=["text", "vision"]
    ),
    
    # OpenAI direct (pour DALL-E)
    "dalle-3": ModelConfig(
        model_id="dall-e-3",
        provider=ModelProvider.OPENAI,
        base_url="https://api.openai.com/v1",
        api_key_env="OPENAI_API_KEY",
        cost_per_1k_input=0.0,  # Image pricing
        cost_per_1k_output=0.0,
        context_window=0,
        capabilities=["image_generation"]
    )
}

class UnifiedModelClient:
    """Client unifié pour tous modèles"""
    
    def __init__(self):
        self.clients = {}
        self._initialize_clients()
    
    def _initialize_clients(self):
        """Initialise clients pour chaque provider"""
        # Client OpenRouter
        self.clients[ModelProvider.OPENROUTER] = OpenAI(
            api_key=os.getenv("OPENROUTER_API_KEY"),
            base_url="https://openrouter.ai/api/v1"
        )
        
        # Client OpenAI direct
        self.clients[ModelProvider.OPENAI] = OpenAI(
            api_key=os.getenv("OPENAI_API_KEY")
        )
    
    def get_client(self, model_name: str) -> OpenAI:
        """Récupère client approprié pour modèle"""
        config = MODEL_REGISTRY.get(model_name)
        if not config:
            raise ValueError(f"Model {model_name} not configured")
        
        return self.clients[config.provider]
    
    def get_config(self, model_name: str) -> ModelConfig:
        """Récupère configuration modèle"""
        config = MODEL_REGISTRY.get(model_name)
        if not config:
            raise ValueError(f"Model {model_name} not configured")
        return config
    
    def list_available_models(self, capability: Optional[str] = None) -> List[str]:
        """Liste modèles disponibles avec capacité optionnelle"""
        models = []
        for name, config in MODEL_REGISTRY.items():
            if capability is None or capability in config.capabilities:
                models.append(name)
        return models

# Instance globale
unified_client = UnifiedModelClient()
```

### Validation Configuration

```python
def validate_all_endpoints():
    """Valide tous endpoints configurés"""
    results = {}
    
    for model_name in MODEL_REGISTRY.keys():
        print(f"\n🔍 Testing {model_name}...")
        
        try:
            config = unified_client.get_config(model_name)
            client = unified_client.get_client(model_name)
            
            # Test simple selon capacités
            if "text" in config.capabilities:
                response = client.chat.completions.create(
                    model=config.model_id,
                    messages=[{"role": "user", "content": "Test"}],
                    max_tokens=5
                )
                results[model_name] = {
                    'status': 'OK',
                    'response': response.choices[0].message.content
                }
                print(f"✅ {model_name} operational")
            
            elif "image_generation" in config.capabilities:
                # Test génération (coûteux, skip en validation)
                results[model_name] = {
                    'status': 'SKIP',
                    'reason': 'Image generation test skipped'
                }
                print(f"⏭️ {model_name} skipped (image gen)")
        
        except Exception as e:
            results[model_name] = {
                'status': 'ERROR',
                'error': str(e)
            }
            print(f"❌ {model_name} failed: {e}")
    
    return results
```

---

## Switching entre Modèles

### Router Automatique

```python
class IntelligentModelRouter:
    """Route requêtes vers modèle optimal"""
    
    def __init__(self):
        self.client = UnifiedModelClient()
        self.usage_stats = {}
    
    def select_model(self, 
                     task_type: str,
                     has_vision: bool = False,
                     max_cost: Optional[float] = None,
                     prefer_quality: bool = False) -> str:
        """
        Sélectionne modèle optimal selon critères
        
        Args:
            task_type: Type tâche (text, vision, generation)
            has_vision: Nécessite capacité vision
            max_cost: Budget maximum par 1K tokens
            prefer_quality: Prioriser qualité vs coût
        
        Returns:
            Nom du modèle sélectionné
        """
        # Filtrage capacités
        if task_type == "vision" or has_vision:
            candidates = self.client.list_available_models(capability="vision")
        elif task_type == "generation":
            candidates = self.client.list_available_models(capability="image_generation")
        else:
            candidates = self.client.list_available_models(capability="text")
        
        # Filtrage coût
        if max_cost:
            candidates = [
                m for m in candidates
                if self.client.get_config(m).cost_per_1k_output <= max_cost
            ]
        
        if not candidates:
            raise ValueError("No model matches criteria")
        
        # Sélection
        if prefer_quality:
            # Tri par coût décroissant (plus cher = meilleur)
            candidates.sort(
                key=lambda m: self.client.get_config(m).cost_per_1k_output,
                reverse=True
            )
        else:
            # Tri par coût croissant (économique)
            candidates.sort(
                key=lambda m: self.client.get_config(m).cost_per_1k_output
            )
        
        selected = candidates[0]
        print(f"🎯 Selected model: {selected}")
        return selected
    
    def execute_with_routing(self,
                            prompt: str,
                            task_type: str = "text",
                            **routing_kwargs):
        """Execute avec routing automatique"""
        model = self.select_model(task_type, **routing_kwargs)
        config = self.client.get_config(model)
        client = self.client.get_client(model)
        
        # Exécution
        response = client.chat.completions.create(
            model=config.model_id,
            messages=[{"role": "user", "content": prompt}],
            max_tokens=500
        )
        
        # Stats
        self._track_usage(model, response.usage.total_tokens)
        
        return {
            'model': model,
            'response': response.choices[0].message.content,
            'tokens': response.usage.total_tokens,
            'estimated_cost': self._calculate_cost(model, response.usage)
        }
    
    def _track_usage(self, model: str, tokens: int):
        """Track utilisation modèle"""
        if model not in self.usage_stats:
            self.usage_stats[model] = {'calls': 0, 'total_tokens': 0}
        
        self.usage_stats[model]['calls'] += 1
        self.usage_stats[model]['total_tokens'] += tokens
    
    def _calculate_cost(self, model: str, usage):
        """Calcule coût réel"""
        config = self.client.get_config(model)
        
        input_cost = (usage.prompt_tokens / 1000) * config.cost_per_1k_input
        output_cost = (usage.completion_tokens / 1000) * config.cost_per_1k_output
        
        return input_cost + output_cost
    
    def get_usage_report(self):
        """Rapport utilisation tous modèles"""
        total_cost = 0
        report = []
        
        for model, stats in self.usage_stats.items():
            config = self.client.get_config(model)
            
            # Estimation coût (approximative)
            avg_cost_per_call = (
                (stats['total_tokens'] / 1000) * 
                (config.cost_per_1k_input + config.cost_per_1k_output) / 
                max(stats['calls'], 1)
            )
            total_model_cost = avg_cost_per_call * stats['calls']
            total_cost += total_model_cost
            
            report.append({
                'model': model,
                'calls': stats['calls'],
                'tokens': stats['total_tokens'],
                'cost': total_model_cost
            })
        
        return {
            'total_cost': total_cost,
            'by_model': report
        }
```

### Fallback Automatique

```python
class FallbackHandler:
    """Gestion fallback entre modèles"""
    
    def __init__(self):
        self.router = IntelligentModelRouter()
        self.fallback_chains = {
            "vision": ["gpt-5-preview", "gemini-pro-vision", "gpt-4-turbo"],
            "text": ["gpt-4-turbo", "claude-3.5-sonnet", "gpt-5-preview"]
        }
    
    def execute_with_fallback(self,
                             prompt: str,
                             task_type: str = "text",
                             max_retries: int = 3):
        """
        Exécute avec fallback automatique si échec
        
        Args:
            prompt: Requête
            task_type: Type tâche (vision, text)
            max_retries: Nombre max tentatives
        """
        chain = self.fallback_chains.get(task_type, self.fallback_chains["text"])
        
        last_error = None
        for i, model in enumerate(chain[:max_retries]):
            try:
                print(f"🔄 Attempt {i+1}/{max_retries}: {model}")
                
                config = unified_client.get_config(model)
                client = unified_client.get_client(model)
                
                response = client.chat.completions.create(
                    model=config.model_id,
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=500,
                    timeout=30
                )
                
                print(f"✅ Success with {model}")
                return {
                    'success': True,
                    'model': model,
                    'response': response.choices[0].message.content,
                    'attempts': i + 1
                }
            
            except Exception as e:
                last_error = e
                print(f"⚠️ {model} failed: {e}")
                continue
        
        return {
            'success': False,
            'error': str(last_error),
            'attempts': max_retries
        }
```

---

## Rate Limiting et Cost Optimization

### Rate Limiter

```python
import time
from datetime import datetime, timedelta
from collections import defaultdict
from threading import Lock

class RateLimiter:
    """Gestion rate limiting par modèle"""
    
    def __init__(self):
        self.limits = {
            "gpt-5-preview": {"rpm": 500, "tpm": 200000},  # OpenRouter
            "gpt-4-turbo": {"rpm": 500, "tpm": 150000},
            "claude-3.5-sonnet": {"rpm": 1000, "tpm": 400000},
            "gemini-pro-vision": {"rpm": 60, "tpm": 32000},
            "dalle-3": {"rpm": 5, "tpm": 0}  # Images
        }
        
        self.usage = defaultdict(lambda: {
            'requests': [],
            'tokens': []
        })
        self.lock = Lock()
    
    def check_limit(self, model: str, tokens: int = 0) -> bool:
        """Vérifie si requête autorisée"""
        with self.lock:
            limits = self.limits.get(model, {"rpm": 100, "tpm": 10000})
            usage = self.usage[model]
            
            now = datetime.now()
            minute_ago = now - timedelta(minutes=1)
            
            # Nettoyage ancien usage
            usage['requests'] = [t for t in usage['requests'] if t > minute_ago]
            usage['tokens'] = [t for t in usage['tokens'] if t[0] > minute_ago]
            
            # Vérification limites
            current_rpm = len(usage['requests'])
            current_tpm = sum(t[1] for t in usage['tokens'])
            
            if current_rpm >= limits['rpm']:
                return False, "RPM limit reached"
            
            if tokens > 0 and current_tpm + tokens >= limits['tpm']:
                return False, "TPM limit reached"
            
            return True, "OK"
    
    def record_usage(self, model: str, tokens: int):
        """Enregistre utilisation"""
        with self.lock:
            now = datetime.now()
            self.usage[model]['requests'].append(now)
            if tokens > 0:
                self.usage[model]['tokens'].append((now, tokens))
    
    def wait_if_needed(self, model: str, tokens: int = 0) -> float:
        """Attend si nécessaire, retourne temps d'attente"""
        start = time.time()
        
        while True:
            allowed, reason = self.check_limit(model, tokens)
            if allowed:
                self.record_usage(model, tokens)
                wait_time = time.time() - start
                if wait_time > 0:
                    print(f"⏳ Waited {wait_time:.2f}s for rate limit")
                return wait_time
            
            time.sleep(0.5)

# Instance globale
rate_limiter = RateLimiter()
```

### Cost Optimizer

```python
class CostOptimizer:
    """Optimise coûts selon budget"""
    
    def __init__(self, daily_budget: float = 10.0):
        self.daily_budget = daily_budget
        self.daily_usage = 0.0
        self.usage_date = datetime.now().date()
        self.router = IntelligentModelRouter()
    
    def reset_if_new_day(self):
        """Reset compteur si nouveau jour"""
        today = datetime.now().date()
        if today > self.usage_date:
            self.daily_usage = 0.0
            self.usage_date = today
            print(f"📅 Reset daily budget: ${self.daily_budget}")
    
    def get_remaining_budget(self) -> float:
        """Budget restant aujourd'hui"""
        self.reset_if_new_day()
        return max(0, self.daily_budget - self.daily_usage)
    
    def select_affordable_model(self, 
                               task_type: str,
                               estimated_tokens: int = 1000,
                               **routing_kwargs) -> Optional[str]:
        """Sélectionne modèle dans budget"""
        remaining = self.get_remaining_budget()
        
        if remaining <= 0:
            print("⚠️ Daily budget exhausted!")
            return None
        
        # Calcul coût max par token
        max_cost_per_1k = (remaining / (estimated_tokens / 1000)) * 0.5  # 50% marge
        
        try:
            model = self.router.select_model(
                task_type=task_type,
                max_cost=max_cost_per_1k,
                **routing_kwargs
            )
            return model
        except ValueError:
            print(f"⚠️ No affordable model for budget ${remaining:.2f}")
            return None
    
    def execute_within_budget(self,
                             prompt: str,
                             task_type: str = "text",
                             **kwargs):
        """Exécute si budget disponible"""
        model = self.select_affordable_model(task_type, **kwargs)
        
        if not model:
            return {
                'success': False,
                'error': 'Budget exhausted or no affordable model'
            }
        
        # Rate limiting
        rate_limiter.wait_if_needed(model)
        
        # Exécution
        result = self.router.execute_with_routing(
            prompt,
            task_type=task_type,
            **kwargs
        )
        
        # Update budget
        self.daily_usage += result['estimated_cost']
        
        print(f"💰 Cost: ${result['estimated_cost']:.4f} | Remaining: ${self.get_remaining_budget():.2f}")
        
        return result
```

---

## API Management et Monitoring

### Health Checker

```python
import requests
from dataclasses import dataclass
from typing import Dict
import json

@dataclass
class HealthStatus:
    """Status santé d'un endpoint"""
    endpoint: str
    status: str  # "healthy", "degraded", "down"
    response_time: float
    last_check: datetime
    error: Optional[str] = None

class APIHealthMonitor:
    """Monitoring santé APIs"""
    
    def __init__(self, check_interval: int = 300):
        self.check_interval = check_interval
        self.health_status: Dict[str, HealthStatus] = {}
    
    def check_endpoint(self, model_name: str) -> HealthStatus:
        """Vérifie santé d'un endpoint"""
        config = unified_client.get_config(model_name)
        
        start = time.time()
        try:
            # Test simple
            if "text" in config.capabilities:
                client = unified_client.get_client(model_name)
                response = client.chat.completions.create(
                    model=config.model_id,
                    messages=[{"role": "user", "content": "test"}],
                    max_tokens=1,
                    timeout=10
                )
                
                response_time = time.time() - start
                
                # Classification status
                if response_time < 2:
                    status = "healthy"
                elif response_time < 5:
                    status = "degraded"
                else:
                    status = "slow"
                
                return HealthStatus(
                    endpoint=model_name,
                    status=status,
                    response_time=response_time,
                    last_check=datetime.now()
                )
        
        except Exception as e:
            return HealthStatus(
                endpoint=model_name,
                status="down",
                response_time=time.time() - start,
                last_check=datetime.now(),
                error=str(e)
            )
    
    def check_all_endpoints(self) -> Dict[str, HealthStatus]:
        """Vérifie tous endpoints"""
        results = {}
        
        for model in MODEL_REGISTRY.keys():
            if "image_generation" in MODEL_REGISTRY[model].capabilities:
                continue  # Skip image gen (coûteux)
            
            print(f"🏥 Checking {model}...")
            status = self.check_endpoint(model)
            results[model] = status
            self.health_status[model] = status
        
        return results
    
    def get_healthy_models(self, capability: Optional[str] = None) -> List[str]:
        """Liste modèles sains avec capacité optionnelle"""
        healthy = []
        
        for model, status in self.health_status.items():
            if status.status in ["healthy", "degraded"]:
                if capability is None:
                    healthy.append(model)
                else:
                    config = unified_client.get_config(model)
                    if capability in config.capabilities:
                        healthy.append(model)
        
        return healthy
    
    def generate_report(self) -> str:
        """Génère rapport santé Markdown"""
        report = ["# API Health Report", ""]
        report.append(f"**Generated**: {datetime.now().isoformat()}")
        report.append("")
        report.append("| Endpoint | Status | Response Time | Last Check |")
        report.append("|----------|--------|---------------|------------|")
        
        for model, status in self.health_status.items():
            status_emoji = {
                "healthy": "✅",
                "degraded": "⚠️",
                "slow": "🐌",
                "down": "❌"
            }.get(status.status, "❓")
            
            report.append(
                f"| {model} | {status_emoji} {status.status} | "
                f"{status.response_time:.2f}s | {status.last_check.strftime('%H:%M:%S')} |"
            )
        
        return "\n".join(report)
```

### Usage Tracker

```python
class UsageTracker:
    """Track utilisation détaillée"""
    
    def __init__(self, log_file: str = "logs/api_usage.jsonl"):
        self.log_file = log_file
        os.makedirs(os.path.dirname(log_file), exist_ok=True)
    
    def log_request(self,
                   model: str,
                   prompt_tokens: int,
                   completion_tokens: int,
                   cost: float,
                   metadata: Optional[Dict] = None):
        """Log une requête"""
        entry = {
            'timestamp': datetime.now().isoformat(),
            'model': model,
            'prompt_tokens': prompt_tokens,
            'completion_tokens': completion_tokens,
            'total_tokens': prompt_tokens + completion_tokens,
            'cost': cost,
            'metadata': metadata or {}
        }
        
        with open(self.log_file, 'a') as f:
            f.write(json.dumps(entry) + '\n')
    
    def get_daily_stats(self, date: Optional[datetime] = None) -> Dict:
        """Statistiques journalières"""
        target_date = (date or datetime.now()).date()
        
        stats = {
            'total_requests': 0,
            'total_tokens': 0,
            'total_cost': 0.0,
            'by_model': defaultdict(lambda: {
                'requests': 0,
                'tokens': 0,
                'cost': 0.0
            })
        }
        
        with open(self.log_file, 'r') as f:
            for line in f:
                entry = json.loads(line)
                entry_date = datetime.fromisoformat(entry['timestamp']).date()
                
                if entry_date == target_date:
                    stats['total_requests'] += 1
                    stats['total_tokens'] += entry['total_tokens']
                    stats['total_cost'] += entry['cost']
                    
                    model = entry['model']
                    stats['by_model'][model]['requests'] += 1
                    stats['by_model'][model]['tokens'] += entry['total_tokens']
                    stats['by_model'][model]['cost'] += entry['cost']
        
        return dict(stats)
    
    def export_report(self, output_file: str, days: int = 7):
        """Exporte rapport période"""
        import pandas as pd
        
        records = []
        cutoff_date = datetime.now() - timedelta(days=days)
        
        with open(self.log_file, 'r') as f:
            for line in f:
                entry = json.loads(line)
                if datetime.fromisoformat(entry['timestamp']) >= cutoff_date:
                    records.append(entry)
        
        df = pd.DataFrame(records)
        
        # Excel export
        with pd.ExcelWriter(output_file, engine='openpyxl') as writer:
            df.to_excel(writer, sheet_name='Raw Data', index=False)
            
            # Summary by model
            summary = df.groupby('model').agg({
                'total_tokens': 'sum',
                'cost': 'sum',
                'timestamp': 'count'
            }).rename(columns={'timestamp': 'requests'})
            
            summary.to_excel(writer, sheet_name='Summary by Model')
        
        print(f"✅ Report exported: {output_file}")
```

---

## Error Handling et Retry Strategies

### Robust Executor

```python
from tenacity import (
    retry,
    stop_after_attempt,
    wait_exponential,
    retry_if_exception_type
)
import openai

class RobustAPIExecutor:
    """Exécution robuste avec retry intelligent"""
    
    def __init__(self):
        self.router = IntelligentModelRouter()
        self.fallback = FallbackHandler()
    
    @retry(
        stop=stop_after_attempt(3),
        wait=wait_exponential(multiplier=1, min=2, max=60),
        retry=retry_if_exception_type((
            openai.APIError,
            openai.APIConnectionError,
            openai.RateLimitError
        ))
    )
    def execute_with_retry(self,
                          model: str,
                          messages: List[Dict],
                          **kwargs):
        """Exécute avec retry exponentiel"""
        config = unified_client.get_config(model)
        client = unified_client.get_client(model)
        
        # Rate limiting
        estimated_tokens = sum(len(m.get('content', '')) for m in messages) * 1.3
        rate_limiter.wait_if_needed(model, int(estimated_tokens))
        
        # Exécution
        response = client.chat.completions.create(
            model=config.model_id,
            messages=messages,
            **kwargs
        )
        
        return response
    
    def execute_with_fallback_and_retry(self,
                                       prompt: str,
                                       task_type: str = "text",
                                       preferred_model: Optional[str] = None):
        """Combine fallback ET retry"""
        # Tentative modèle préféré
        if preferred_model:
            try:
                print(f"🎯 Trying preferred model: {preferred_model}")
                messages = [{"role": "user", "content": prompt}]
                response = self.execute_with_retry(
                    preferred_model,
                    messages,
                    max_tokens=500
                )
                
                return {
                    'success': True,
                    'model': preferred_model,
                    'response': response.choices[0].message.content
                }
            
            except Exception as e:
                print(f"⚠️ Preferred model failed: {e}")
        
        # Fallback chain
        print("🔄 Attempting fallback chain...")
        result = self.fallback.execute_with_fallback(prompt, task_type)
        
        return result

# Instance globale
robust_executor = RobustAPIExecutor()
```

### Error Classifier

```python
class ErrorClassifier:
    """Classifie et gère différents types d'erreurs"""
    
    ERROR_TYPES = {
        'rate_limit': {
            'keywords': ['rate_limit', '429', 'too many requests'],
            'action': 'wait_and_retry',
            'wait_time': 60
        },
        'timeout': {
            'keywords': ['timeout', 'timed out', 'connection'],
            'action': 'retry_immediate',
            'wait_time': 0
        },
        'quota_exceeded': {
            'keywords': ['quota', 'exceeded', 'insufficient'],
            'action': 'switch_model',
            'wait_time': 0
        },
        'invalid_request': {
            'keywords': ['invalid', '400', 'bad request'],
            'action': 'fix_request',
            'wait_time': 0
        },
        'server_error': {
            'keywords': ['500', '502', '503', 'server error'],
            'action': 'retry_exponential',
            'wait_time': 5
        }
    }
    
    @staticmethod
    def classify(error: Exception) -> Dict:
        """Classifie erreur et suggère action"""
        error_str = str(error).lower()
        
        for error_type, config in ErrorClassifier.ERROR_TYPES.items():
            if any(kw in error_str for kw in config['keywords']):
                return {
                    'type': error_type,
                    'action': config['action'],
                    'wait_time': config['wait_time'],
                    'original_error': str(error)
                }
        
        # Type inconnu
        return {
            'type': 'unknown',
            'action': 'manual_review',
            'wait_time': 0,
            'original_error': str(error)
        }
    
    @staticmethod
    def handle_error(error: Exception, context: Dict) -> Dict:
        """Gère erreur selon classification"""
        classification = ErrorClassifier.classify(error)
        
        print(f"🔍 Error type: {classification['type']}")
        print(f"📋 Suggested action: {classification['action']}")
        
        if classification['action'] == 'wait_and_retry':
            print(f"⏳ Waiting {classification['wait_time']}s...")
            time.sleep(classification['wait_time'])
            return {'retry': True, 'switch_model': False}
        
        elif classification['action'] == 'switch_model':
            print("🔄 Switching to alternative model...")
            return {'retry': True, 'switch_model': True}
        
        elif classification['action'] == 'retry_immediate':
            return {'retry': True, 'switch_model': False}
        
        elif classification['action'] == 'retry_exponential':
            return {'retry': True, 'switch_model': False, 'exponential': True}
        
        else:
            return {'retry': False, 'switch_model': False, 'manual': True}
```

---

## Production Best Practices

### Configuration Management

```python
import yaml
from pathlib import Path

class ConfigurationManager:
    """Gestion configuration production"""
    
    def __init__(self, config_file: str = "config/openrouter_prod.yaml"):
        self.config_file = Path(config_file)
        self.config = self.load_config()
    
    def load_config(self) -> Dict:
        """Charge configuration depuis YAML"""
        if self.config_file.exists():
            with open(self.config_file) as f:
                return yaml.safe_load(f)
        
        # Configuration par défaut
        default_config = {
            'production': {
                'rate_limiting': True,
                'cost_optimization': True,
                'daily_budget': 50.0,
                'fallback_enabled': True,
                'health_check_interval': 300,
                'default_timeout': 30,
                'retry_max_attempts': 3,
                'preferred_models': {
                    'text': 'gpt-4-turbo',
                    'vision': 'gpt-5-preview',
                    'cheap': 'claude-3.5-sonnet'
                }
            },
            'development': {
                'rate_limiting': False,
                'cost_optimization': True,
                'daily_budget': 5.0,
                'fallback_enabled': True,
                'health_check_interval': 600,
                'default_timeout': 60,
                'retry_max_attempts': 2,
                'preferred_models': {
                    'text': 'claude-3.5-sonnet',
                    'vision': 'gemini-pro-vision',
                    'cheap': 'claude-3.5-sonnet'
                }
            }
        }
        
        # Sauvegarde configuration par défaut
        self.save_config(default_config)
        return default_config
    
    def save_config(self, config: Dict):
        """Sauvegarde configuration"""
        self.config_file.parent.mkdir(parents=True, exist_ok=True)
        with open(self.config_file, 'w') as f:
            yaml.dump(config, f, default_flow_style=False)
    
    def get(self, key: str, environment: str = "production", default=None):
        """Récupère valeur configuration"""
        env_config = self.config.get(environment, {})
        return env_config.get(key, default)
    
    def update(self, key: str, value, environment: str = "production"):
        """Met à jour configuration"""
        if environment not in self.config:
            self.config[environment] = {}
        
        self.config[environment][key] = value
        self.save_config(self.config)
```

### Production Pipeline

```python
class ProductionPipeline:
    """Pipeline production complet"""
    
    def __init__(self, environment: str = "production"):
        self.environment = environment
        self.config = ConfigurationManager().config[environment]
        
        # Composants
        self.router = IntelligentModelRouter()
        self.rate_limiter = rate_limiter
        self.cost_optimizer = CostOptimizer(
            daily_budget=self.config['daily_budget']
        )
        self.health_monitor = APIHealthMonitor(
            check_interval=self.config['health_check_interval']
        )
        self.usage_tracker = UsageTracker()
        self.executor = RobustAPIExecutor()
    
    def execute(self,
               prompt: str,
               task_type: str = "text",
               preferred_model: Optional[str] = None,
               **kwargs):
        """
        Exécution production complète
        
        - Health check
        - Cost optimization
        - Rate limiting
        - Retry + Fallback
        - Usage tracking
        """
        try:
            # 1. Health check
            if self.config.get('health_check_before_request', True):
                healthy_models = self.health_monitor.get_healthy_models(
                    capability="text" if task_type == "text" else "vision"
                )
                
                if preferred_model and preferred_model not in healthy_models:
                    print(f"⚠️ {preferred_model} unhealthy, selecting alternative")
                    preferred_model = None
            
            # 2. Cost optimization
            if not preferred_model and self.config.get('cost_optimization'):
                preferred_model = self.cost_optimizer.select_affordable_model(
                    task_type=task_type,
                    estimated_tokens=len(prompt) * 1.5
                )
                
                if not preferred_model:
                    return {
                        'success': False,
                        'error': 'Budget exhausted'
                    }
            
            # 3. Execution with retry + fallback
            result = self.executor.execute_with_fallback_and_retry(
                prompt=prompt,
                task_type=task_type,
                preferred_model=preferred_model
            )
            
            # 4. Usage tracking
            if result['success'] and 'response' in result:
                self.usage_tracker.log_request(
                    model=result['model'],
                    prompt_tokens=len(prompt) // 4,  # Approximation
                    completion_tokens=len(result['response']) // 4,
                    cost=0.01,  # Estimation
                    metadata={
                        'task_type': task_type,
                        'environment': self.environment
                    }
                )
            
            return result
        
        except Exception as e:
            return {
                'success': False,
                'error': str(e),
                'traceback': traceback.format_exc()
            }
    
    def batch_execute(self, requests: List[Dict]) -> List[Dict]:
        """Exécution batch optimisée"""
        results = []
        
        for i, req in enumerate(requests):
            print(f"\n{'='*60}")
            print(f"Request {i+1}/{len(requests)}")
            
            result = self.execute(**req)
            results.append(result)
            
            # Pause entre requêtes
            if i < len(requests) - 1:
                time.sleep(1)
        
        return results
    
    def generate_daily_report(self):
        """Génère rapport journalier"""
        # Usage stats
        usage_stats = self.usage_tracker.get_daily_stats()
        
        # Health status
        health_report = self.health_monitor.generate_report()
        
        # Cost report
        budget_status = {
            'daily_budget': self.cost_optimizer.daily_budget,
            'used': self.cost_optimizer.daily_usage,
            'remaining': self.cost_optimizer.get_remaining_budget()
        }
        
        # Combine reports
        report = f"""# OpenRouter Daily Report - {datetime.now().date()}

## Budget Status
- Daily Budget: ${budget_status['daily_budget']:.2f}
- Used: ${budget_status['used']:.2f}
- Remaining: ${budget_status['remaining']:.2f}

## Usage Statistics
- Total Requests: {usage_stats['total_requests']}
- Total Tokens: {usage_stats['total_tokens']:,}
- Total Cost: ${usage_stats['total_cost']:.2f}

{health_report}
"""
        
        # Sauvegarde
        report_file = f"reports/daily_report_{datetime.now().date()}.md"
        os.makedirs('reports', exist_ok=True)
        with open(report_file, 'w') as f:
            f.write(report)
        
        print(f"✅ Daily report saved: {report_file}")
        return report
```

---

## Integration Patterns CoursIA

### Pattern 1: Educational Content Generator

```python
class EducationalContentGenerator:
    """Générateur contenu pédagogique optimisé"""
    
    def __init__(self):
        self.pipeline = ProductionPipeline(environment="production")
    
    def generate_lesson_materials(self,
                                 topic: str,
                                 grade_level: str,
                                 material_types: List[str]):
        """
        Génère ensemble supports de cours
        
        Args:
            topic: Sujet du cours
            grade_level: Niveau scolaire
            material_types: Types matériel (text, image, quiz, etc.)
        """
        materials = {}
        
        for material_type in material_types:
            if material_type == "text":
                prompt = f"""Crée contenu pédagogique sur '{topic}' pour niveau {grade_level}:

1. Introduction engageante
2. Concepts clés (3-5)
3. Exemples concrets
4. Analogies simples
5. Points à retenir

Format: Markdown, français pédagogique."""
                
                result = self.pipeline.execute(
                    prompt=prompt,
                    task_type="text",
                    preferred_model="gpt-4-turbo"
                )
                
                materials['lesson_text'] = result
            
            elif material_type == "quiz":
                prompt = f"""Génère 5 questions QCM sur '{topic}' niveau {grade_level}:

Pour chaque question:
- Question claire
- 4 options (1 correcte)
- Explication réponse
- Niveau difficulté

Format: JSON structuré."""
                
                result = self.pipeline.execute(
                    prompt=prompt,
                    task_type="text",
                    preferred_model="claude-3.5-sonnet"
                )
                
                materials['quiz'] = result
            
            elif material_type == "visual_description":
                prompt = f"""Décris 3 visuels pédagogiques pour illustrer '{topic}':

Pour chaque visuel:
- Description détaillée pour génération DALL-E
- Objectif pédagogique
- Éléments essentiels à inclure
- Style recommandé

Format: Liste structurée."""
                
                result = self.pipeline.execute(
                    prompt=prompt,
                    task_type="text",
                    preferred_model="gpt-5-preview"
                )
                
                materials['visual_descriptions'] = result
        
        return materials
```

### Pattern 2: Multimodal Learning Assistant

```python
class MultimodalLearningAssistant:
    """Assistant apprentissage multimodal"""
    
    def __init__(self):
        self.pipeline = ProductionPipeline()
        self.conversation_history = []
    
    def analyze_student_work(self,
                           image_path: str,
                           assignment_type: str):
        """Analyse travail étudiant avec image"""
        prompt = f"""Analyse ce travail d'étudiant ({assignment_type}):

Évalue:
1. Compréhension concepts (0-10)
2. Exactitude (liste erreurs)
3. Qualité présentation
4. Points forts
5. Suggestions amélioration (3 concrètes)

Format: Feedback constructif, français pédagogique."""
        
        # Utilise GPT-5 pour vision
        result = self.pipeline.execute(
            prompt=prompt,
            task_type="vision",
            preferred_model="gpt-5-preview"
        )
        
        return result
    
    def interactive_tutoring(self,
                           student_question: str,
                           subject: str):
        """Tutorat interactif adaptatif"""
        # Contexte conversation
        self.conversation_history.append({
            "role": "user",
            "content": student_question
        })
        
        # Prompt tutorat
        system_prompt = f"""Tu es tuteur pédagogue en {subject}.

Principes:
- Questions socratiques pour guider
- Explications progressives
- Encouragement positif
- Adaptation niveau élève
- Exemples concrets français

Historique conversation inclus ci-dessus."""
        
        result = self.pipeline.execute(
            prompt=system_prompt + "\n\n" + student_question,
            task_type="text",
            preferred_model="claude-3.5-sonnet"
        )
        
        if result['success']:
            self.conversation_history.append({
                "role": "assistant",
                "content": result['response']
            })
        
        return result
```

---

## Ressources Complémentaires

### Documentation
- [OpenRouter Docs](https://openrouter.ai/docs)
- [OpenRouter Models](https://openrouter.ai/models)
- [OpenRouter Dashboard](https://openrouter.ai/dashboard)

### Notebooks CoursIA
- `00-3-API-Endpoints-Configuration.ipynb` : Configuration APIs
- `04-2-Creative-Workflows.ipynb` : Workflows multi-modèles
- `04-3-Production-Integration.ipynb` : Intégration production

### Configuration Files
- `.env` : Variables environnement
- `config/openrouter_prod.yaml` : Configuration production
- `logs/api_usage.jsonl` : Logs utilisation

---

**Version**: 1.0.0  
**Dernière mise à jour**: 2025-10-08  
**Auteur**: Équipe CoursIA  
**Licence**: Projet Éducatif CoursIA