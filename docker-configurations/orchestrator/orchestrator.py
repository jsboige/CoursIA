#!/usr/bin/env python3
"""
=============================================================================
CoursIA GenAI - Docker Services Orchestrator
=============================================================================
Orchestrateur pour la gestion du lifecycle des services GenAI Docker

Fonctionnalités:
  - Health monitoring des services GenAI
  - API REST pour contrôle des services
  - Métriques Prometheus
  - Load balancing basique

Endpoints:
  - GET  /health         : Health check de l'orchestrateur
  - GET  /services       : Liste tous les services et leur statut
  - GET  /services/{id}  : Détails d'un service spécifique
  - POST /services/{id}/start  : Démarre un service
  - POST /services/{id}/stop   : Arrête un service
  - GET  /metrics        : Métriques Prometheus
=============================================================================
"""

import os
import logging
from typing import Dict, List, Optional
from datetime import datetime

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import docker
from prometheus_client import Counter, Gauge, generate_latest
from fastapi.responses import Response

# ===== CONFIGURATION =====
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")
GENAI_ENVIRONMENT = os.getenv("GENAI_ENVIRONMENT", "development")

# ===== LOGGING SETUP =====
logging.basicConfig(
    level=LOG_LEVEL,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger("orchestrator")

# ===== DOCKER CLIENT =====
try:
    docker_client = docker.from_env()
    logger.info("✅ Docker client initialized successfully")
except Exception as e:
    logger.error(f"❌ Failed to initialize Docker client: {e}")
    docker_client = None

# ===== FASTAPI APP =====
app = FastAPI(
    title="CoursIA GenAI Orchestrator",
    description="Orchestrateur pour services de génération d'images GenAI",
    version="1.0.0",
)

# ===== CORS CONFIGURATION =====
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# ===== PROMETHEUS METRICS =====
service_health = Gauge('genai_service_health', 'Service health status (1=healthy, 0=unhealthy)', ['service'])
requests_total = Counter('genai_requests_total', 'Total requests', ['endpoint', 'method'])

# ===== MODELS =====
class ServiceStatus(BaseModel):
    name: str
    container_id: str
    status: str
    health: Optional[str] = None
    created: str
    ports: Dict[str, str]

class HealthResponse(BaseModel):
    status: str
    timestamp: str
    environment: str
    services_count: int

# ===== KNOWN SERVICES =====
GENAI_SERVICES = {
    "flux-1-dev": "coursia-flux-1-dev",
    "stable-diffusion-35": "coursia-sd35",
    "comfyui-workflows": "coursia-comfyui-workflows",
}

# ===== HELPER FUNCTIONS =====
def get_container_info(container_name: str) -> Optional[Dict]:
    """Récupère les informations d'un container Docker"""
    if not docker_client:
        return None
    
    try:
        container = docker_client.containers.get(container_name)
        
        # Extract port mappings
        ports = {}
        if container.attrs.get('NetworkSettings', {}).get('Ports'):
            for container_port, host_bindings in container.attrs['NetworkSettings']['Ports'].items():
                if host_bindings:
                    ports[container_port] = host_bindings[0]['HostPort']
        
        return {
            "name": container.name,
            "container_id": container.short_id,
            "status": container.status,
            "health": container.attrs.get('State', {}).get('Health', {}).get('Status'),
            "created": container.attrs.get('Created'),
            "ports": ports,
        }
    except docker.errors.NotFound:
        logger.warning(f"Container {container_name} not found")
        return None
    except Exception as e:
        logger.error(f"Error getting container info: {e}")
        return None

def check_service_health(service_name: str) -> bool:
    """Vérifie la santé d'un service"""
    info = get_container_info(GENAI_SERVICES.get(service_name))
    if not info:
        service_health.labels(service=service_name).set(0)
        return False
    
    is_healthy = info['status'] == 'running' and (
        info['health'] in ['healthy', None]  # None = pas de healthcheck défini
    )
    service_health.labels(service=service_name).set(1 if is_healthy else 0)
    return is_healthy

# ===== API ENDPOINTS =====
@app.get("/health", response_model=HealthResponse)
async def health_check():
    """Health check de l'orchestrateur"""
    requests_total.labels(endpoint="/health", method="GET").inc()
    
    services_count = len([s for s in GENAI_SERVICES.keys() if check_service_health(s)])
    
    return HealthResponse(
        status="healthy",
        timestamp=datetime.utcnow().isoformat(),
        environment=GENAI_ENVIRONMENT,
        services_count=services_count
    )

@app.get("/services", response_model=List[ServiceStatus])
async def list_services():
    """Liste tous les services GenAI et leur statut"""
    requests_total.labels(endpoint="/services", method="GET").inc()
    
    services = []
    for service_name, container_name in GENAI_SERVICES.items():
        info = get_container_info(container_name)
        if info:
            services.append(ServiceStatus(**info))
    
    return services

@app.get("/services/{service_name}", response_model=ServiceStatus)
async def get_service(service_name: str):
    """Récupère les détails d'un service spécifique"""
    requests_total.labels(endpoint=f"/services/{service_name}", method="GET").inc()
    
    if service_name not in GENAI_SERVICES:
        raise HTTPException(status_code=404, detail=f"Service {service_name} not found")
    
    container_name = GENAI_SERVICES[service_name]
    info = get_container_info(container_name)
    
    if not info:
        raise HTTPException(status_code=404, detail=f"Container {container_name} not found")
    
    return ServiceStatus(**info)

@app.post("/services/{service_name}/start")
async def start_service(service_name: str):
    """Démarre un service"""
    requests_total.labels(endpoint=f"/services/{service_name}/start", method="POST").inc()
    
    if service_name not in GENAI_SERVICES:
        raise HTTPException(status_code=404, detail=f"Service {service_name} not found")
    
    if not docker_client:
        raise HTTPException(status_code=500, detail="Docker client not available")
    
    try:
        container = docker_client.containers.get(GENAI_SERVICES[service_name])
        container.start()
        logger.info(f"✅ Service {service_name} started")
        return {"status": "started", "service": service_name}
    except Exception as e:
        logger.error(f"❌ Failed to start service {service_name}: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/services/{service_name}/stop")
async def stop_service(service_name: str):
    """Arrête un service"""
    requests_total.labels(endpoint=f"/services/{service_name}/stop", method="POST").inc()
    
    if service_name not in GENAI_SERVICES:
        raise HTTPException(status_code=404, detail=f"Service {service_name} not found")
    
    if not docker_client:
        raise HTTPException(status_code=500, detail="Docker client not available")
    
    try:
        container = docker_client.containers.get(GENAI_SERVICES[service_name])
        container.stop()
        logger.info(f"✅ Service {service_name} stopped")
        return {"status": "stopped", "service": service_name}
    except Exception as e:
        logger.error(f"❌ Failed to stop service {service_name}: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/metrics")
async def metrics():
    """Expose Prometheus metrics"""
    return Response(content=generate_latest(), media_type="text/plain")

# ===== STARTUP =====
@app.on_event("startup")
async def startup_event():
    logger.info("=" * 80)
    logger.info("CoursIA GenAI Orchestrator - Starting")
    logger.info(f"Environment: {GENAI_ENVIRONMENT}")
    logger.info(f"Log Level: {LOG_LEVEL}")
    logger.info("=" * 80)
    
    # Check all services at startup
    for service_name in GENAI_SERVICES.keys():
        is_healthy = check_service_health(service_name)
        status = "✅ healthy" if is_healthy else "❌ unhealthy"
        logger.info(f"Service {service_name}: {status}")

# ===== MAIN =====
if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8193, log_level=LOG_LEVEL.lower())