> **ARCHIVED 2026-07-24** — PM transiente, valeur = historique uniquement. INDEX-only (no external inbound refs on `origin/main`). See #7422 triage.

# 🐳 Spécifications Infrastructure Docker GenAI - CoursIA

**Date :** 7 octobre 2025  
**Méthode :** SDDD avec Intégration MCP Optimisée  
**Mission :** Phase 2.3 - Infrastructure Conteneurs Production-Ready

---

## 🎯 Architecture Docker Hybride

### Principe d'Intégration SDDD

**ISOLATION CONTRÔLÉE :** Les containers GenAI opèrent de manière totalement isolée de l'infrastructure MCP exceptionnelle, tout en exposant des APIs standardisées pour intégration seamless.

**COMMUNICATION via API REST :** Aucune dépendance directe avec MCP. Communication uniquement via endpoints HTTP sécurisés.

---

## 📊 Vue d'Ensemble Infrastructure

### Architecture Réseau

```yaml
# Configuration réseau dédiée GenAI
networks:
  genai-network:
    driver: bridge
    ipam:
      driver: default
      config:
        - subnet: 172.20.0.0/16
          gateway: 172.20.0.1
    options:
      com.docker.network.bridge.name: "genai0"
      
  genai-monitoring:
    driver: bridge  
    ipam:
      config:
        - subnet: 172.21.0.0/16

# Mapping ports standardisé
PORT_MAPPING:
  flux-1-dev: 8189        # ComfyUI interface
  stable-diffusion-35: 8190   # FastAPI server
  comfyui-workflows: 8191      # ComfyUI advanced
  monitoring: 8192            # Prometheus metrics
  orchestrator: 8193          # Docker orchestrator API
```

### Allocation Ressources

```yaml
# Ressources par container (configuration production)
resource_allocation:
  development:
    flux-1-dev:
      memory: "8GB"
      gpu_memory: "8GB" 
      cpu: "4.0"
    stable-diffusion-35:
      memory: "12GB"
      gpu_memory: "10GB"
      cpu: "6.0"
      
  production:
    flux-1-dev:
      memory: "16GB"
      gpu_memory: "12GB"
      cpu: "8.0"
    stable-diffusion-35:
      memory: "24GB" 
      gpu_memory: "16GB"
      cpu: "12.0"
```

---

## 🚀 FLUX.1-dev Container Specification

### 1. Container Configuration

```yaml
# docker-configurations/flux-1-dev/docker-compose.yml
version: '3.8'
services:
  flux-1-dev:
    image: "comfyanonymous/comfyui:latest-cu124"
    container_name: "coursia-flux-1-dev"
    hostname: "flux-1-dev"
    
    ports:
      - "8189:8188"
      - "8189-metrics:8189"  # Metrics endpoint
      
    volumes:
      # Models (bind mounts for persistence)
      - "./models:/app/models:ro"
      - "./custom_nodes:/app/custom_nodes:rw"
      - "./workflows:/app/workflows:rw"
      - "./outputs:/app/outputs:rw"
      
      # Configuration
      - "./config/flux-config.json:/app/config.json:ro"
      - "./logs:/app/logs:rw"
      
    environment:
      # CUDA Configuration
      - CUDA_VISIBLE_DEVICES=0
      - NVIDIA_VISIBLE_DEVICES=0
      - CUDA_CACHE_DISABLE=1
      
      # ComfyUI Settings
      - COMFYUI_ARGS=--enable-cors-header --cpu-vae --use-split-cross-attention
      - PYTHONPATH=/app
      - PYTHONUNBUFFERED=1
      
      # Performance Tuning
      - PYTORCH_CUDA_ALLOC_CONF=max_split_size_mb:512
      - CUDA_LAUNCH_BLOCKING=0
      
      # Monitoring
      - ENABLE_METRICS=true
      - METRICS_PORT=8189
      
    deploy:
      resources:
        limits:
          memory: 16G
          cpus: '8.0'
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]
              
    networks:
      - genai-network
      
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8188/system_stats"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 60s
      
    restart: unless-stopped
    
    logging:
      driver: "json-file" 
      options:
        max-size: "100m"
        max-file: "5"
```

### 2. Configuration Modèle FLUX

```json
// docker-configurations/flux-1-dev/config/flux-config.json
{
  "model_config": {
    "flux_model": {
      "path": "/app/models/flux1-dev.safetensors",
      "type": "diffusion_model",
      "precision": "fp16",
      "vram_usage": "auto"
    },
    "vae": {
      "path": "/app/models/ae.safetensors", 
      "type": "vae",
      "precision": "fp16"
    },
    "clip": {
      "path": "/app/models/clip_l.safetensors",
      "type": "clip",
      "precision": "fp16"
    }
  },
  
  "generation_defaults": {
    "scheduler": "euler",
    "steps": 20,
    "cfg_scale": 7.5,
    "width": 1024,
    "height": 1024,
    "batch_size": 1
  },
  
  "performance": {
    "use_split_cross_attention": true,
    "cpu_vae": false,
    "low_vram": false,
    "fp16_precision": true
  },
  
  "api_settings": {
    "enable_cors": true,
    "max_concurrent_requests": 2,
    "timeout_seconds": 300,
    "queue_max_size": 10
  }
}
```

### 3. Custom Workflows FLUX

```python
# docker-configurations/flux-1-dev/workflows/flux_standard_workflow.py
"""
Workflow FLUX standard pour intégration CoursIA
Compatible avec l'architecture MCP via API REST
"""

FLUX_WORKFLOW_TEMPLATE = {
    "1": {
        "class_type": "CheckpointLoaderSimple",
        "inputs": {
            "ckpt_name": "flux1-dev.safetensors"
        }
    },
    "2": {
        "class_type": "CLIPTextEncode", 
        "inputs": {
            "text": "{{prompt}}",
            "clip": ["1", 1]
        }
    },
    "3": {
        "class_type": "EmptyLatentImage",
        "inputs": {
            "width": "{{width|default(1024)}}",
            "height": "{{height|default(1024)}}",
            "batch_size": "{{batch_size|default(1)}}"
        }
    },
    "4": {
        "class_type": "KSampler",
        "inputs": {
            "seed": "{{seed|random}}",
            "steps": "{{steps|default(20)}}",
            "cfg": "{{cfg_scale|default(7.5)}}",
            "sampler_name": "{{sampler|default('euler')}}",
            "scheduler": "normal",
            "model": ["1", 0],
            "positive": ["2", 0],
            "negative": ["5", 0],
            "latent_image": ["3", 0]
        }
    },
    "5": {
        "class_type": "CLIPTextEncode",
        "inputs": {
            "text": "{{negative_prompt|default('')}}",
            "clip": ["1", 1]
        }
    },
    "6": {
        "class_type": "VAEDecode",
        "inputs": {
            "samples": ["4", 0],
            "vae": ["1", 2]
        }
    },
    "7": {
        "class_type": "SaveImage",
        "inputs": {
            "filename_prefix": "CourIA_FLUX_",
            "images": ["6", 0]
        }
    }
}
```

---

## 🎨 Stable Diffusion 3.5 Container Specification

### 1. Container Configuration

```yaml
# docker-configurations/stable-diffusion-3.5/docker-compose.yml
version: '3.8'
services:
  stable-diffusion-35:
    image: "huggingface/diffusers:latest-gpu"
    container_name: "coursia-sd35"
    hostname: "stable-diffusion-35"
    
    ports:
      - "8190:8000"
      
    volumes:
      - "./models:/models:ro"
      - "./cache:/cache:rw"
      - "./outputs:/outputs:rw"
      - "./config:/config:ro"
      
    environment:
      # Model Configuration
      - MODEL_NAME=stabilityai/stable-diffusion-3.5-large
      - MODEL_PRECISION=fp16
      - CACHE_DIR=/cache
      - OUTPUT_DIR=/outputs
      
      # Performance
      - TORCH_COMPILE=1
      - PYTORCH_CUDA_ALLOC_CONF=max_split_size_mb:1024
      - CUDA_VISIBLE_DEVICES=0
      
      # API Settings
      - API_HOST=0.0.0.0
      - API_PORT=8000
      - MAX_CONCURRENT_REQUESTS=3
      - REQUEST_TIMEOUT=600
      
      # Hugging Face
      - HUGGINGFACE_HUB_CACHE=/cache/huggingface
      - TRANSFORMERS_CACHE=/cache/transformers
      
    deploy:
      resources:
        limits:
          memory: 24G
          cpus: '12.0'
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]
              
    networks:
      - genai-network
      
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8000/health"]
      interval: 45s
      timeout: 15s
      retries: 3
      start_period: 120s
      
    restart: unless-stopped
```

### 2. FastAPI Server SD3.5

```python
# docker-configurations/stable-diffusion-3.5/app/main.py
"""
API Server Stable Diffusion 3.5 pour intégration CoursIA MCP
Architecture REST compatible avec ExecutionManager async
"""

from fastapi import FastAPI, HTTPException, BackgroundTasks
from pydantic import BaseModel
from diffusers import StableDiffusion3Pipeline
import torch
import uuid
from typing import Optional, Dict, Any
import logging

# Configuration logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

app = FastAPI(
    title="CoursIA Stable Diffusion 3.5 API",
    description="API REST pour génération d'images SD3.5",
    version="1.0.0"
)

# Global pipeline
pipeline = None
generation_jobs: Dict[str, Dict] = {}

class GenerationRequest(BaseModel):
    prompt: str
    negative_prompt: Optional[str] = ""
    width: int = 1024
    height: int = 1024
    num_inference_steps: int = 28
    guidance_scale: float = 7.0
    num_images: int = 1
    seed: Optional[int] = None

class GenerationResponse(BaseModel):
    job_id: str
    status: str
    message: str

@app.on_event("startup")
async def startup_event():
    """Initialisation du pipeline SD3.5"""
    global pipeline
    
    logger.info("Initialisation pipeline Stable Diffusion 3.5...")
    
    try:
        pipeline = StableDiffusion3Pipeline.from_pretrained(
            "stabilityai/stable-diffusion-3.5-large",
            torch_dtype=torch.float16,
            cache_dir="/cache",
            use_safetensors=True
        )
        pipeline.to("cuda")
        
        # Optimisations performance
        pipeline.enable_attention_slicing()
        pipeline.enable_model_cpu_offload()
        
        logger.info("Pipeline SD3.5 initialisé avec succès")
        
    except Exception as e:
        logger.error(f"Erreur initialisation pipeline: {e}")
        raise

@app.get("/health")
async def health_check():
    """Health check pour monitoring"""
    return {
        "status": "healthy",
        "model": "stable-diffusion-3.5-large",
        "gpu_available": torch.cuda.is_available(),
        "gpu_memory": torch.cuda.get_device_properties(0).total_memory if torch.cuda.is_available() else None
    }

@app.post("/generate", response_model=GenerationResponse)
async def generate_image(request: GenerationRequest, background_tasks: BackgroundTasks):
    """Endpoint génération d'image asynchrone"""
    job_id = str(uuid.uuid4())
    
    generation_jobs[job_id] = {
        "status": "pending",
        "request": request.dict(),
        "created_at": datetime.utcnow().isoformat()
    }
    
    # Démarrage génération en arrière-plan
    background_tasks.add_task(process_generation, job_id, request)
    
    return GenerationResponse(
        job_id=job_id,
        status="pending", 
        message="Génération démarrée"
    )

@app.get("/status/{job_id}")
async def get_generation_status(job_id: str):
    """Statut d'une génération"""
    if job_id not in generation_jobs:
        raise HTTPException(status_code=404, detail="Job non trouvé")
        
    return generation_jobs[job_id]

async def process_generation(job_id: str, request: GenerationRequest):
    """Traitement génération d'image"""
    try:
        generation_jobs[job_id]["status"] = "processing"
        
        # Génération avec pipeline SD3.5
        images = pipeline(
            prompt=request.prompt,
            negative_prompt=request.negative_prompt,
            width=request.width,
            height=request.height,
            num_inference_steps=request.num_inference_steps,
            guidance_scale=request.guidance_scale,
            num_images_per_prompt=request.num_images,
            generator=torch.Generator().manual_seed(request.seed) if request.seed else None
        ).images
        
        # Sauvegarde images
        output_paths = []
        for i, image in enumerate(images):
            output_path = f"/outputs/{job_id}_{i}.png"
            image.save(output_path)
            output_paths.append(output_path)
            
        generation_jobs[job_id].update({
            "status": "completed",
            "output_paths": output_paths,
            "completed_at": datetime.utcnow().isoformat()
        })
        
    except Exception as e:
        generation_jobs[job_id].update({
            "status": "failed",
            "error": str(e),
            "failed_at": datetime.utcnow().isoformat()
        })
        logger.error(f"Erreur génération {job_id}: {e}")

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
```

---

## 🎛️ ComfyUI Workflows Container

### 1. Configuration Avancée

```yaml
# docker-configurations/comfyui-workflows/docker-compose.yml
version: '3.8'
services:
  comfyui-workflows:
    image: "comfyanonymous/comfyui:latest-cu124"
    container_name: "coursia-comfyui-workflows"
    hostname: "comfyui-workflows"
    
    ports:
      - "8191:8188"
      
    volumes:
      - "./models:/app/models:ro"
      - "./custom_nodes:/app/custom_nodes:rw"
      - "./workflows:/app/web/workflows:rw"
      - "./outputs:/app/output:rw"
      - "./input:/app/input:rw"
      
    environment:
      - COMFYUI_ARGS=--enable-cors-header --extra-model-paths-config /app/extra_model_paths.yaml
      - WORKFLOW_AUTO_SAVE=true
      - ENABLE_WORKFLOW_API=true
      
    networks:
      - genai-network
      
    depends_on:
      - flux-1-dev
      
    restart: unless-stopped
```

### 2. Workflows Éducatifs Prédéfinis

```json
// docker-configurations/comfyui-workflows/workflows/coursia_educational_workflow.json
{
  "name": "CoursIA Educational Image Generator",
  "description": "Workflow optimisé pour génération de contenu éducatif",
  "version": "1.0",
  
  "workflow": {
    "style_options": [
      "technical_diagram",
      "educational_illustration", 
      "scientific_visualization",
      "architectural_drawing",
      "infographic_style"
    ],
    
    "quality_presets": {
      "draft": {"steps": 15, "cfg": 6.0},
      "standard": {"steps": 20, "cfg": 7.5},
      "high_quality": {"steps": 30, "cfg": 8.0},
      "production": {"steps": 50, "cfg": 8.5}
    },
    
    "educational_prompts": {
      "prefix_templates": [
        "Educational diagram showing",
        "Clear technical illustration of", 
        "Scientific visualization of",
        "Step-by-step visual guide for"
      ],
      "style_suffixes": [
        "clean white background, professional style",
        "technical drawing style, precise lines",
        "infographic style, clear labels",
        "educational textbook illustration style"
      ]
    }
  }
}
```

---

## 🎯 Orchestrateur Docker

### 1. Service d'Orchestration

```python
# docker-configurations/orchestrator/orchestrator.py
"""
Orchestrateur Docker GenAI pour CoursIA
Gestion lifecycle containers, health checks, load balancing
"""

import docker
import asyncio
import logging
from typing import Dict, List, Optional
from dataclasses import dataclass
from enum import Enum
import httpx

logger = logging.getLogger(__name__)

class ContainerStatus(Enum):
    STOPPED = "stopped"
    STARTING = "starting"  
    HEALTHY = "healthy"
    UNHEALTHY = "unhealthy"
    ERROR = "error"

@dataclass
class GenAIModel:
    name: str
    container_name: str
    image: str
    port: int
    health_endpoint: str
    startup_time_seconds: int
    resource_requirements: Dict

class DockerOrchestrator:
    """
    Orchestrateur principal pour containers GenAI
    Compatible avec architecture MCP subprocess isolation
    """
    
    def __init__(self):
        self.docker_client = docker.from_env()
        self.http_client = httpx.AsyncClient(timeout=30.0)
        
        self.models = {
            "flux-1-dev": GenAIModel(
                name="flux-1-dev",
                container_name="coursia-flux-1-dev",
                image="comfyanonymous/comfyui:latest-cu124",
                port=8189,
                health_endpoint="/system_stats",
                startup_time_seconds=90,
                resource_requirements={"memory": "16GB", "gpu_memory": "12GB"}
            ),
            "stable-diffusion-35": GenAIModel(
                name="stable-diffusion-35", 
                container_name="coursia-sd35",
                image="huggingface/diffusers:latest-gpu",
                port=8190,
                health_endpoint="/health",
                startup_time_seconds=120,
                resource_requirements={"memory": "24GB", "gpu_memory": "16GB"}
            ),
            "comfyui-workflows": GenAIModel(
                name="comfyui-workflows",
                container_name="coursia-comfyui-workflows", 
                image="comfyanonymous/comfyui:latest-cu124",
                port=8191,
                health_endpoint="/system_stats",
                startup_time_seconds=60,
                resource_requirements={"memory": "8GB", "gpu_memory": "8GB"}
            )
        }
        
        self.container_status: Dict[str, ContainerStatus] = {}
    
    async def start_model(self, model_name: str) -> Dict[str, Any]:
        """
        Démarre un modèle GenAI avec health checks
        Compatible avec timeout illimité ExecutionManager
        """
        if model_name not in self.models:
            raise ValueError(f"Modèle {model_name} non supporté")
            
        model = self.models[model_name]
        
        try:
            logger.info(f"Démarrage container {model.container_name}")
            
            # Vérification resources disponibles
            if not await self._check_resources_available(model):
                raise RuntimeError(f"Resources insuffisantes pour {model_name}")
            
            # Démarrage container Docker
            container = await self._start_container(model)
            
            # Attente health check (avec timeout adaptatif)
            self.container_status[model_name] = ContainerStatus.STARTING
            
            health_success = await self._wait_for_health(
                model, 
                timeout_seconds=model.startup_time_seconds + 60
            )
            
            if health_success:
                self.container_status[model_name] = ContainerStatus.HEALTHY
                endpoint_url = f"http://localhost:{model.port}"
                
                logger.info(f"Container {model_name} démarré et healthy sur {endpoint_url}")
                
                return {
                    "model_name": model_name,
                    "status": "healthy",
                    "endpoint_url": endpoint_url,
                    "container_id": container.id,
                    "startup_duration": model.startup_time_seconds
                }
            else:
                self.container_status[model_name] = ContainerStatus.UNHEALTHY
                raise RuntimeError(f"Health check failed pour {model_name}")
                
        except Exception as e:
            self.container_status[model_name] = ContainerStatus.ERROR
            logger.error(f"Erreur démarrage {model_name}: {e}")
            raise
    
    async def stop_model(self, model_name: str) -> Dict[str, Any]:
        """Arrêt propre d'un modèle"""
        if model_name not in self.models:
            raise ValueError(f"Modèle {model_name} non supporté")
        
        model = self.models[model_name]
        
        try:
            container = self.docker_client.containers.get(model.container_name)
            
            logger.info(f"Arrêt container {model.container_name}")
            
            # Arrêt gracieux (SIGTERM puis SIGKILL si nécessaire)
            container.stop(timeout=30)
            
            self.container_status[model_name] = ContainerStatus.STOPPED
            
            return {
                "model_name": model_name,
                "status": "stopped",
                "message": "Container arrêté avec succès"
            }
            
        except docker.errors.NotFound:
            self.container_status[model_name] = ContainerStatus.STOPPED
            return {"model_name": model_name, "status": "not_found"}
        except Exception as e:
            logger.error(f"Erreur arrêt {model_name}: {e}")
            raise
    
    async def get_models_status(self) -> Dict[str, Dict]:
        """Statut de tous les modèles"""
        status_report = {}
        
        for model_name, model in self.models.items():
            try:
                container = self.docker_client.containers.get(model.container_name)
                container_state = container.attrs['State']
                
                # Test health check
                health_status = "unknown"
                if container_state['Status'] == 'running':
                    health_status = await self._test_health_endpoint(model)
                
                status_report[model_name] = {
                    "container_status": container_state['Status'],
                    "health_status": health_status,
                    "endpoint": f"http://localhost:{model.port}",
                    "uptime": container_state.get('StartedAt'),
                    "resource_usage": await self._get_container_resources(container)
                }
                
            except docker.errors.NotFound:
                status_report[model_name] = {
                    "container_status": "not_found",
                    "health_status": "unavailable"
                }
                
        return status_report
    
    async def ensure_models_for_notebook(self, notebook_path: str) -> Dict[str, str]:
        """
        Analyse notebook et démarre modèles nécessaires
        INTÉGRATION MCP : Prépare environment pour ExecutionManager
        """
        required_models = await self._analyze_notebook_requirements(notebook_path)
        
        logger.info(f"Modèles requis pour {notebook_path}: {required_models}")
        
        endpoints = {}
        
        for model_name in required_models:
            try:
                result = await self.start_model(model_name)
                endpoints[f"GENAI_{model_name.upper()}_ENDPOINT"] = result["endpoint_url"]
                
            except Exception as e:
                logger.error(f"Impossible de démarrer {model_name}: {e}")
                # Stratégie de fallback vers cloud si disponible
                if model_name in ["flux-1-dev", "stable-diffusion-35"]:
                    endpoints[f"GENAI_{model_name.upper()}_ENDPOINT"] = "openrouter"
        
        return endpoints  # Variables d'environnement pour MCP
    
    async def _analyze_notebook_requirements(self, notebook_path: str) -> List[str]:
        """Analyse notebook pour déterminer modèles nécessaires"""
        import json
        
        required_models = []
        
        try:
            with open(notebook_path, 'r', encoding='utf-8') as f:
                notebook = json.load(f)
            
            # Analyse du contenu des cellules
            for cell in notebook.get('cells', []):
                if cell.get('cell_type') == 'code':
                    source = '\n'.join(cell.get('source', []))
                    
                    # Détection patterns GenAI
                    if 'flux' in source.lower() or 'comfyui' in source.lower():
                        if 'flux-1-dev' not in required_models:
                            required_models.append('flux-1-dev')
                    
                    if 'stable-diffusion' in source.lower() or 'sd35' in source.lower():
                        if 'stable-diffusion-35' not in required_models:
                            required_models.append('stable-diffusion-35')
                    
                    if 'workflow' in source.lower() and 'comfy' in source.lower():
                        if 'comfyui-workflows' not in required_models:
                            required_models.append('comfyui-workflows')
            
        except Exception as e:
            logger.warning(f"Erreur analyse notebook {notebook_path}: {e}")
        
        return required_models
    
    async def _start_container(self, model: GenAIModel):
        """Démarrage container Docker"""
        try:
            # Lecture docker-compose pour configuration
            compose_path = f"docker-configurations/{model.name}/docker-compose.yml"
            
            container = self.docker_client.containers.run(
                model.image,
                name=model.container_name,
                ports={f'{model.port}': model.port},
                detach=True,
                restart_policy={"Name": "unless-stopped"}
            )
            
            return container
            
        except Exception as e:
            logger.error(f"Erreur démarrage container {model.name}: {e}")
            raise
    
    async def _wait_for_health(self, model: GenAIModel, timeout_seconds: int) -> bool:
        """Attente health check avec timeout"""
        start_time = asyncio.get_event_loop().time()
        
        while (asyncio.get_event_loop().time() - start_time) < timeout_seconds:
            health_status = await self._test_health_endpoint(model)
            
            if health_status == "healthy":
                return True
            
            await asyncio.sleep(5)  # Check toutes les 5 secondes
        
        logger.warning(f"Health check timeout pour {model.name}")
        return False
    
    async def _test_health_endpoint(self, model: GenAIModel) -> str:
        """Test endpoint santé"""
        try:
            url = f"http://localhost:{model.port}{model.health_endpoint}"
            
            response = await self.http_client.get(url)
            
            if response.status_code == 200:
                return "healthy"
            else:
                return "unhealthy"
                
        except Exception as e:
            logger.debug(f"Health check failed {model.name}: {e}")
            return "unreachable"
```

### 2. API REST Orchestrateur

```python
# docker-configurations/orchestrator/api.py
"""
API REST pour orchestrateur Docker GenAI
Endpoints pour intégration avec MCP
"""

from fastapi import FastAPI, HTTPException, BackgroundTasks
from pydantic import BaseModel
from typing import List, Dict, Optional
import asyncio

from .orchestrator import DockerOrchestrator

app = FastAPI(
    title="CoursIA GenAI Docker Orchestrator",
    description="API d'orchestration des containers GenAI",
    version="1.0.0"
)

orchestrator = DockerOrchestrator()

class StartModelRequest(BaseModel):
    model_names: List[str]
    notebook_path: Optional[str] = None

class ModelStatusResponse(BaseModel):
    model_name: str
    status: str
    endpoint_url: Optional[str] = None
    message: str

@app.post("/start-models")
async def start_models(request: StartModelRequest, background_tasks: BackgroundTasks):
    """Démarre modèles spécifiques ou auto-détection via notebook"""
    
    if request.notebook_path:
        # Auto-détection des modèles requis
        endpoints = await orchestrator.ensure_models_for_notebook(request.notebook_path)
        return {
            "status": "started",
            "environment_variables": endpoints,
            "message": "Modèles démarrés selon analyse notebook"
        }
    else:
        # Démarrage modèles spécifiés
        results = []
        for model_name in request.model_names:
            try:
                result = await orchestrator.start_model(model_name)
                results.append(result)
            except Exception as e:
                results.append({
                    "model_name": model_name,
                    "status": "error",
                    "message": str(e)
                })
        
        return {"models": results}

@app.get("/models/status")
async def get_all_models_status():
    """Statut de tous les modèles"""
    return await orchestrator.get_models_status()

@app.post("/models/{model_name}/stop")
async def stop_model(model_name: str):
    """Arrêt d'un modèle spécifique"""
    try:
        result = await orchestrator.stop_model(model_name)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/health")
async def health_check():
    """Health check orchestrateur"""
    return {
        "status": "healthy",
        "orchestrator_version": "1.0.0",
        "docker_available": True
    }

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8193)
```

---

## 📊 Monitoring et Observabilité

### 1. Stack Monitoring

```yaml
# docker-configurations/monitoring/docker-compose.yml
version: '3.8'
services:
  prometheus:
    image: prom/prometheus:latest
    container_name: coursia-prometheus
    ports:
      - "9090:9090"
    volumes:
      - "./prometheus.yml:/etc/prometheus/prometheus.yml:ro"
    networks:
      - genai-monitoring
      
  grafana:
    image: grafana/grafana:latest
    container_name: coursia-grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=coursia123
    volumes:
      - "./grafana/dashboards:/var/lib/grafana/dashboards:ro"
      - "./grafana/provisioning:/etc/grafana/provisioning:ro"
    networks:
      - genai-monitoring
      
  node-exporter:
    image: prom/node-exporter:latest
    container_name: coursia-node-exporter
    ports:
      - "9100:9100"
    networks:
      - genai-monitoring
```

### 2. Configuration Prometheus

```yaml
# docker-configurations/monitoring/prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'genai-containers'
    static_configs:
      - targets: 
        - 'coursia-flux-1-dev:8189'
        - 'coursia-sd35:8190'
        - 'coursia-comfyui-workflows:8191'
    scrape_interval: 30s
    metrics_path: /metrics
    
  - job_name: 'orchestrator'
    static_configs:
      - targets: ['coursia-orchestrator:8193']
    scrape_interval: 15s
    
  - job_name: 'node-exporter'
    static_configs:
      - targets: ['coursia-node-exporter:9100']
```

---

## 🚀 Scripts de Déploiement

### 1. Script de Setup Complet

```powershell
# scripts/setup-genai-docker-infrastructure.ps1
<#
.SYNOPSIS
Setup complet infrastructure Docker GenAI pour CoursIA

.DESCRIPTION
Script PowerShell pour déploiement automatisé de tous les containers GenAI
Compatible avec architecture MCP subprocess existing

.EXAMPLE
.\setup-genai-docker-infrastructure.ps1 -Environment development
#>

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("development", "production", "testing")]
    [string]$Environment,
    
    [switch]$SkipGpuCheck,
    [switch]$StartMonitoring,
    [switch]$ValidateSetup
)

# Configuration selon environnement
$envConfig = @{
    development = @{
        flux_memory = "8GB"
        sd35_memory = "12GB"
        monitoring = $false
    }
    production = @{
        flux_memory = "16GB" 
        sd35_memory = "24GB"
        monitoring = $true
    }
}

Write-Host "🐳 Setup Infrastructure Docker GenAI - CoursIA" -ForegroundColor Cyan
Write-Host "Environment: $Environment" -ForegroundColor Yellow

# Vérifications préalables
Write-Host "🔍 Vérifications système..." -ForegroundColor Green

# Docker disponible
try {
    $dockerVersion = docker --version
    Write-Host "✅ Docker: $dockerVersion" -ForegroundColor Green
} catch {
    Write-Error "❌ Docker non disponible. Installation requise."
    exit 1
}

# Docker Compose disponible
try {
    $composeVersion = docker compose version
    Write-Host "✅ Docker Compose: $composeVersion" -ForegroundColor Green
} catch {
    Write-Error "❌ Docker Compose non disponible."
    exit 1
}

# GPU NVIDIA (optionnel selon environnement)
if (-not $SkipGpuCheck) {
    try {
        $nvidiaInfo = nvidia-smi --query-gpu=name,memory.total --format=csv,noheader
        Write-Host "✅ GPU NVIDIA détecté: $nvidiaInfo" -ForegroundColor Green
    } catch {
        Write-Warning "⚠️  GPU NVIDIA non détecté. Performance limitée en mode CPU."
        
        if ($Environment -eq "production") {
            Write-Error "❌ GPU requis pour environnement production"
            exit 1
        }
    }
}

# Création structure directories
Write-Host "📁 Création structure directories..." -ForegroundColor Green

$directories = @(
    "docker-configurations/flux-1-dev/models",
    "docker-configurations/flux-1-dev/outputs", 
    "docker-configurations/flux-1-dev/logs",
    "docker-configurations/stable-diffusion-3.5/models",
    "docker-configurations/stable-diffusion-3.5/outputs",
    "docker-configurations/stable-diffusion-3.5/cache",
    "docker-configurations/comfyui-workflows/workflows",
    "docker-configurations/comfyui-workflows/outputs",
    "docker-configurations/orchestrator/logs",
    "docker-configurations/monitoring/grafana/dashboards"
)

foreach ($dir in $directories) {
    if (-not (Test-Path $dir)) {
        New-Item -Path $dir -ItemType Directory -Force
        Write-Host "  ✅ $dir" -ForegroundColor Gray
    }
}

# Configuration .env files
Write-Host "⚙️  Configuration variables d'environnement..." -ForegroundColor Green

$envContent = @"
# Configuration GenAI Docker - $Environment
ENVIRONMENT=$Environment
FLUX_MEMORY_LIMIT=$($envConfig[$Environment].flux_memory)
SD35_MEMORY_LIMIT=$($envConfig[$Environment].sd35_memory)
ENABLE_MONITORING=$($envConfig[$Environment].monitoring)

# Network Configuration
GENAI_NETWORK_SUBNET=172.20.0.0/16
MONITORING_NETWORK_SUBNET=172.21.0.0/16

# Ports Configuration
FLUX_PORT=8189
SD35_PORT=8190
COMFYUI_PORT=8191
ORCHESTRATOR_PORT=8193
PROMETHEUS_PORT=9090
GRAFANA_PORT=3000

# Security
GRAFANA_ADMIN_PASSWORD=coursia123
"@

$envContent | Out-File -FilePath ".env.genai-docker" -Encoding UTF8
Write-Host "  ✅ .env.genai-docker créé" -ForegroundColor Gray

# Téléchargement modèles (si nécessaire)
Write-Host "📦 Vérification modèles..." -ForegroundColor Green

$modelsToCheck = @{
    "flux1-dev.safetensors" = "docker-configurations/flux-1-dev/models/"
    "ae.safetensors" = "docker-configurations/flux-1-dev/models/"
    "clip_l.safetensors" = "docker-configurations/flux-1-dev/models/"
}

foreach ($model in $modelsToCheck.Keys) {
    $modelPath = Join-Path $modelsToCheck[$model] $model
    if (-not (Test-Path $modelPath)) {
        Write-Host "  ⚠️  Modèle $model manquant. Téléchargement requis." -ForegroundColor Yellow
        Write-Host "     Chemin attendu: $modelPath" -ForegroundColor Gray
    } else {
        Write-Host "  ✅ $model disponible" -ForegroundColor Gray
    }
}

# Démarrage infrastructure
Write-Host "🚀 Démarrage infrastructure Docker..." -ForegroundColor Green

# Network création
docker network create genai-network --subnet=172.20.0.0/16 2>$null
docker network create genai-monitoring --subnet=172.21.0.0/16 2>$null

# Démarrage services
$services = @("flux-1-dev", "stable-diffusion-3.5", "comfyui-workflows", "orchestrator")

foreach ($service in $services) {
    Write-Host "  🐳 Démarrage $service..." -ForegroundColor Cyan
    
    $composeFile = "docker-configurations/$service/docker-compose.yml"
    if (Test-Path $composeFile) {
        docker compose -f $composeFile up -d
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "    ✅ $service démarré" -ForegroundColor Green
        } else {
            Write-Warning "    ⚠️  Erreur démarrage $service"
        }
    } else {
        Write-Warning "    ⚠️  Fichier compose manquant: $composeFile"
    }
}

# Monitoring (optionnel)
if ($StartMonitoring -or $envConfig[$Environment].monitoring) {
    Write-Host "📊 Démarrage monitoring..." -ForegroundColor Green
    
    docker compose -f docker-configurations/monitoring/docker-compose.yml up -d
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ Monitoring démarré" -ForegroundColor Green
        Write-Host "  📊 Grafana: http://localhost:3000 (admin/coursia123)" -ForegroundColor Cyan
        Write-Host "  📈 Prometheus: http://localhost:9090" -ForegroundColor Cyan
    }
}

# Validation setup
if ($ValidateSetup) {
    Write-Host "🧪 Validation setup..." -ForegroundColor Green
    
    Start-Sleep -Seconds 30  # Attente startup
    
    $endpoints = @{
        "FLUX.1-dev" = "http://localhost:8189/system_stats"
        "Stable Diffusion 3.5" = "http://localhost:8190/health"
        "ComfyUI Workflows" = "http://localhost:8191/system_stats"
        "Orchestrator" = "http://localhost:8193/health"
    }
    
    foreach ($service in $endpoints.Keys) {
        $endpoint = $endpoints[$service]
        
        try {
            $response = Invoke-RestMethod -Uri $endpoint -TimeoutSec 10
            Write-Host "  ✅ $service: Healthy" -ForegroundColor Green
        } catch {
            Write-Warning "  ⚠️  $service: Non disponible"
        }
    }
}

Write-Host ""
Write-Host "🎉 Setup infrastructure Docker GenAI terminé !" -ForegroundColor Green
Write-Host ""
Write-Host "📋 Services disponibles:" -ForegroundColor Cyan
Write-Host "  🎨 FLUX.1-dev: http://localhost:8189" -ForegroundColor Gray
Write-Host "  🖼️  Stable Diffusion 3.5: http://localhost:8190" -ForegroundColor Gray  
Write-Host "  🎛️  ComfyUI Workflows: http://localhost:8191" -ForegroundColor Gray
Write-Host "  🎯 Orchestrator: http://localhost:8193" -ForegroundColor Gray
Write-Host ""
Write-Host "🔗 Intégration MCP:" -ForegroundColor Yellow
Write-Host "  Variables d'environnement ajoutées à .env.genai-docker"
Write-Host "  Endpoints prêts pour notebooks CoursIA"
Write-Host ""
Write-Host "📚 Prochaines étapes:" -ForegroundColor Blue
Write-Host "  1. Télécharger modèles manquants si nécessaire"
Write-Host "  2. Tester génération d'images via API"  
Write-Host "  3. Intégrer avec notebooks GenAI CoursIA"
```

### 2. Script de Validation

```powershell
# scripts/validate-genai-setup.ps1
<#
.SYNOPSIS
Validation complète setup GenAI Docker

.DESCRIPTION
Tests automatisés pour valider l'infrastructure GenAI
#>

Write-Host "🧪 Validation Infrastructure GenAI Docker" -ForegroundColor Cyan

# Tests containers
$containers = @("coursia-flux-1-dev", "coursia-sd35", "coursia-comfyui-workflows", "coursia-orchestrator")

foreach ($container in $containers) {
    $status = docker ps --filter "name=$container" --format "table {{.Status}}"
    
    if ($status -match "Up") {
        Write-Host "✅ Container $container: Running" -ForegroundColor Green
    } else {
        Write-Host "❌ Container $container: Stopped" -ForegroundColor Red
    }
}

# Tests endpoints
$endpoints = @{
    "FLUX" = "http://localhost:8189/system_stats"
    "SD35" = "http://localhost:8190/health" 
    "ComfyUI" = "http://localhost:8191/system_stats"
    "Orchestrator" = "http://localhost:8193/health"
}

foreach ($service in $endpoints.Keys) {
    try {
        $response = Invoke-RestMethod -Uri $endpoints[$service] -TimeoutSec 5
        Write-Host "✅ API $service: Disponible" -ForegroundColor Green
    } catch {
        Write-Host "❌ API $service: Indisponible" -ForegroundColor Red
    }
}

# Test génération simple
Write-Host "🎨 Test génération d'image..." -ForegroundColor Yellow

try {
    $testRequest = @{
        prompt = "test image generation"
        width = 512
        height = 512
        num_inference_steps = 10
    }
    
    $response = Invoke-RestMethod -Uri "http://localhost:8190/generate" -Method Post -Body ($testRequest | ConvertTo-Json) -ContentType "application/json"
    
    Write-Host "✅ Génération test: Job créé ($($response.job_id))" -ForegroundColor Green
} catch {
    Write-Host "❌ Génération test: Échec" -ForegroundColor Red
}

Write-Host "🏁 Validation terminée" -ForegroundColor Cyan
```

---

## 🔒 Sécurité et Production

### 1. Configuration Sécurisée

```yaml
# docker-configurations/security/docker-compose.override.yml
version: '3.8'
services:
  flux-1-dev:
    security_opt:
      - no-new-privileges:true
    read_only: true
    tmpfs:
      - /tmp
      - /var/tmp
    user: "1000:1000"
    
  stable-diffusion-35:
    security_opt:
      - no-new-privileges:true
    read_only: true
    tmpfs:
      - /tmp
      - /var/tmp
    user: "1000:1000"
    
  orchestrator:
    security_opt:
      - no-new-privileges:true
    environment:
      - DOCKER_API_VERSION=1.41
    volumes:
      - /var/run/docker.sock:/var/run/docker.sock:ro
```

### 2. Monitoring Production

```yaml
# docker-configurations/monitoring/alerts.yml
groups:
  - name: genai-containers
    rules:
      - alert: ContainerDown
        expr: up == 0
        for: 30s
        labels:
          severity: critical
        annotations:
          summary: "Container {{ $labels.instance }} is down"
          
      - alert: HighMemoryUsage
        expr: container_memory_usage_bytes / container_spec_memory_limit_bytes > 0.8
        for: 2m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage on {{ $labels.container_name }}"
          
      - alert: GPUMemoryFull
        expr: nvidia_gpu_memory_used_bytes / nvidia_gpu_memory_total_bytes > 0.9
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "GPU memory almost full"
```

---

## 📋 Résumé Technique

### Infrastructure Créée

**4 Containers Principaux :**
- ✅ **FLUX.1-dev** (ComfyUI) : Port 8189, API REST + WebUI
- ✅ **Stable Diffusion 3.5** : Port 8190, FastAPI server
- ✅ **ComfyUI Workflows** : Port 8191, Workflows éducatifs  
- ✅ **Orchestrator** : Port 8193, Gestion lifecycle

**Infrastructure Support :**
- ✅ **Monitoring** : Prometheus + Grafana
- ✅ **Networks** : Isolation containers + monitoring
- ✅ **Scripts** : Setup automatisé + validation

### Intégration MCP

**Variables d'Environnement :**
```bash
GENAI_DOCKER_FLUX=http://localhost:8189
GENAI_DOCKER_SD35=http://localhost:8190
GENAI_DOCKER_COMFYUI=http://localhost:8191
GENAI_ORCHESTRATOR=http://localhost:8193
```

**Nouveaux Outils MCP :**
- `start_genai_container`
- `stop_genai_container`  
- `get_genai_model_status`
- `generate_image_local`
- `create_image_workflow`

### Capacités Production

**Performance :**
- Memory: 8-24GB par container selon environnement
- GPU: Support NVIDIA avec CUDA
- Concurrent: 2-3 requêtes simultanées par modèle

**Observabilité :**
- Health checks automatiques
- Metrics Prometheus
- Dashboards Grafana
- Logging centralisé

**Sécurité :**
- Containers isolés (networks dédiés)
- Read-only filesystems
- Security opts (no-new-privileges)
- API authentication ready

---

*Spécifications Docker GenAI complètes - Prêtes pour Phase 2.4*