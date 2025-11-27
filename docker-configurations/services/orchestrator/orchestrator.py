#!/usr/bin/env python3
"""
Orchestrateur GenAI pour la gestion des services d'IA
Gère le cycle de vie des services, monitoring et load balancing
"""

import json
import yaml
import logging
import requests
import time
import os
import sys
from datetime import datetime, timedelta
from typing import Dict, List, Optional
import threading
import http.server
import socketserver
from urllib.parse import urlparse

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

class GenAIOrchestrator:
    """Orchestrateur principal pour les services GenAI"""
    
    def __init__(self, config_path: str = "/app/config/services.yml"):
        self.config_path = config_path
        self.services = {}
        self.service_status = {}
        self.load_config()
        self.start_monitoring()
    
    def load_config(self):
        """Charge la configuration des services depuis le fichier YAML"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                config = yaml.safe_load(f)
                self.services = config.get('services', {})
                logger.info(f"Configuration chargée: {len(self.services)} services")
                
                # Initialiser le statut des services
                for service_id, service_config in self.services.items():
                    self.service_status[service_id] = {
                        'status': 'unknown',
                        'last_check': None,
                        'uptime': 0,
                        'error_count': 0,
                        'last_error': None
                    }
                    
        except Exception as e:
            logger.error(f"Erreur lors du chargement de la configuration: {e}")
            sys.exit(1)
    
    def check_service_health(self, service_id: str, service_config: Dict) -> bool:
        """Vérifie la santé d'un service spécifique"""
        try:
            container_name = service_config.get('container')
            port = service_config.get('port')
            health_endpoint = service_config.get('healthcheck_endpoint', '/health')
            
            # Construire l'URL du service
            service_url = f"http://localhost:{port}{health_endpoint}"
            
            # Tenter de contacter le service
            response = requests.get(
                service_url,
                timeout=10,
                headers={'User-Agent': 'GenAI-Orchestrator/1.0'}
            )
            
            if response.status_code == 200:
                self.service_status[service_id].update({
                    'status': 'healthy',
                    'last_check': datetime.now(),
                    'error_count': 0,
                    'last_error': None
                })
                return True
            else:
                raise Exception(f"HTTP {response.status_code}")
                
        except requests.exceptions.RequestException as e:
            self.service_status[service_id]['error_count'] += 1
            self.service_status[service_id]['last_error'] = str(e)
            self.service_status[service_id]['last_check'] = datetime.now()
            self.service_status[service_id]['status'] = 'unhealthy'
            
            logger.warning(f"Service {service_id} indisponible: {e}")
            return False
        except Exception as e:
            logger.error(f"Erreur lors du check du service {service_id}: {e}")
            return False
    
    def start_service(self, service_id: str) -> bool:
        """Démarre un service spécifique via Docker"""
        try:
            import subprocess
            
            service_config = self.services[service_id]
            container_name = service_config.get('container')
            
            # Commande Docker pour démarrer le conteneur
            cmd = [
                'docker', 'start', container_name
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                logger.info(f"Service {service_id} démarré avec succès")
                # Attendre un peu pour que le service démarre
                time.sleep(5)
                return True
            else:
                logger.error(f"Erreur lors du démarrage du service {service_id}: {result.stderr}")
                return False
                
        except Exception as e:
            logger.error(f"Exception lors du démarrage du service {service_id}: {e}")
            return False
    
    def stop_service(self, service_id: str) -> bool:
        """Arrête un service spécifique via Docker"""
        try:
            import subprocess
            
            service_config = self.services[service_id]
            container_name = service_config.get('container')
            
            # Commande Docker pour arrêter le conteneur
            cmd = [
                'docker', 'stop', container_name
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                logger.info(f"Service {service_id} arrêté avec succès")
                return True
            else:
                logger.error(f"Erreur lors de l'arrêt du service {service_id}: {result.stderr}")
                return False
                
        except Exception as e:
            logger.error(f"Exception lors de l'arrêt du service {service_id}: {e}")
            return False
    
    def restart_service(self, service_id: str) -> bool:
        """Redémarre un service spécifique"""
        logger.info(f"Redémarrage du service {service_id}")
        
        if self.stop_service(service_id):
            time.sleep(2)
            return self.start_service(service_id)
        
        return False
    
    def get_service_for_request(self, request_type: str, priority: bool = True) -> Optional[str]:
        """Sélectionne le meilleur service disponible pour une requête"""
        available_services = []
        
        for service_id, service_config in self.services.items():
            if self.service_status[service_id]['status'] == 'healthy':
                capabilities = service_config.get('capabilities', [])
                
                # Vérifier si le service peut gérer ce type de requête
                if request_type == 'text-to-image':
                    if 'text-to-image' in capabilities:
                        available_services.append((service_id, service_config))
                elif request_type == 'workflow':
                    if 'advanced-workflows' in capabilities or 'custom-pipelines' in capabilities:
                        available_services.append((service_id, service_config))
                elif request_type == 'versatile':
                    if 'versatile-generation' in capabilities or 'production-ready' in capabilities:
                        available_services.append((service_id, service_config))
        
        if not available_services:
            return None
        
        # Trier par priorité si demandé
        if priority:
            available_services.sort(key=lambda x: x[1].get('priority', 999))
        
        # Retourner le service avec la plus haute priorité
        return available_services[0][0]
    
    def monitor_services(self):
        """Boucle de monitoring des services"""
        while True:
            try:
                for service_id, service_config in self.services.items():
                    self.check_service_health(service_id, service_config)
                
                # Log du statut global
                healthy_count = sum(1 for status in self.service_status.values() 
                                if status['status'] == 'healthy')
                total_count = len(self.services)
                
                logger.info(f"Monitoring: {healthy_count}/{total_count} services sains")
                
                # Attendre avant le prochain check
                time.sleep(30)
                
            except Exception as e:
                logger.error(f"Erreur dans la boucle de monitoring: {e}")
                time.sleep(10)
    
    def start_monitoring(self):
        """Démarre le thread de monitoring"""
        monitor_thread = threading.Thread(target=self.monitor_services, daemon=True)
        monitor_thread.start()
        logger.info("Thread de monitoring démarré")
    
    def get_system_status(self) -> Dict:
        """Retourne le statut complet du système"""
        return {
            "orchestrator": {
                "status": "running",
                "timestamp": datetime.now().isoformat(),
                "version": "1.0.0",
                "uptime": "unknown"  # À implémenter
            },
            "services": {
                service_id: {
                    **self.services[service_id],
                    **self.service_status[service_id]
                }
                for service_id in self.services.keys()
            },
            "summary": {
                "total_services": len(self.services),
                "healthy_services": sum(1 for status in self.service_status.values() 
                                      if status['status'] == 'healthy'),
                "unhealthy_services": sum(1 for status in self.service_status.values() 
                                        if status['status'] == 'unhealthy'),
                "unknown_services": sum(1 for status in self.service_status.values() 
                                      if status['status'] == 'unknown')
            }
        }

class OrchestratorAPI(http.server.SimpleHTTPRequestHandler):
    """Handler HTTP pour l'API de l'orchestrateur"""
    
    def __init__(self, orchestrator: GenAIOrchestrator, *args, **kwargs):
        self.orchestrator = orchestrator
        super().__init__(*args, **kwargs)
    
    def do_GET(self):
        """Gère les requêtes GET"""
        try:
            if self.path == "/health":
                self.handle_health()
            elif self.path == "/status":
                self.handle_status()
            elif self.path == "/services":
                self.handle_services()
            elif self.path.startswith("/service/"):
                service_id = self.path[9:]  # Remove "/service/" prefix
                self.handle_service_info(service_id)
            elif self.path.startswith("/start/"):
                service_id = self.path[7:]  # Remove "/start/" prefix
                self.handle_start_service(service_id)
            elif self.path.startswith("/stop/"):
                service_id = self.path[6:]  # Remove "/stop/" prefix
                self.handle_stop_service(service_id)
            elif self.path.startswith("/restart/"):
                service_id = self.path[9:]  # Remove "/restart/" prefix
                self.handle_restart_service(service_id)
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b'Endpoint not found')
        except Exception as e:
            logger.error(f"Erreur lors du traitement GET {self.path}: {e}")
            self.send_response(500)
            self.end_headers()
            self.wfile.write(b'Internal server error')
    
    def do_POST(self):
        """Gère les requêtes POST"""
        try:
            if self.path == "/route_request":
                self.handle_route_request()
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b'Endpoint not found')
        except Exception as e:
            logger.error(f"Erreur lors du traitement POST {self.path}: {e}")
            self.send_response(500)
            self.end_headers()
            self.wfile.write(b'Internal server error')
    
    def handle_health(self):
        """Endpoint de santé de l'orchestrateur"""
        response = {
            "status": "healthy",
            "service": "GenAI-Orchestrator",
            "timestamp": datetime.now().isoformat()
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_status(self):
        """Retourne le statut complet du système"""
        status = self.orchestrator.get_system_status()
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(status, indent=2).encode())
    
    def handle_services(self):
        """Retourne la liste des services"""
        services = []
        for service_id, service_config in self.orchestrator.services.items():
            services.append({
                "id": service_id,
                "name": service_config.get('name'),
                "type": service_config.get('type'),
                "model": service_config.get('model'),
                "port": service_config.get('port'),
                "status": self.orchestrator.service_status[service_id]['status'],
                "capabilities": service_config.get('capabilities', [])
            })
        
        response = {
            "services": services,
            "total": len(services),
            "timestamp": datetime.now().isoformat()
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_service_info(self, service_id: str):
        """Retourne les détails d'un service spécifique"""
        if service_id not in self.orchestrator.services:
            self.send_response(404)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": f"Service {service_id} not found"}
            self.wfile.write(json.dumps(error_response).encode())
            return
        
        service_config = self.orchestrator.services[service_id]
        service_status = self.orchestrator.service_status[service_id]
        
        response = {
            "id": service_id,
            **service_config,
            **service_status
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_start_service(self, service_id: str):
        """Démarre un service spécifique"""
        if service_id not in self.orchestrator.services:
            self.send_response(404)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": f"Service {service_id} not found"}
            self.wfile.write(json.dumps(error_response).encode())
            return
        
        success = self.orchestrator.start_service(service_id)
        
        response = {
            "service": service_id,
            "action": "start",
            "success": success,
            "timestamp": datetime.now().isoformat()
        }
        
        status_code = 200 if success else 500
        self.send_response(status_code)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_stop_service(self, service_id: str):
        """Arrête un service spécifique"""
        if service_id not in self.orchestrator.services:
            self.send_response(404)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": f"Service {service_id} not found"}
            self.wfile.write(json.dumps(error_response).encode())
            return
        
        success = self.orchestrator.stop_service(service_id)
        
        response = {
            "service": service_id,
            "action": "stop",
            "success": success,
            "timestamp": datetime.now().isoformat()
        }
        
        status_code = 200 if success else 500
        self.send_response(status_code)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_restart_service(self, service_id: str):
        """Redémarre un service spécifique"""
        if service_id not in self.orchestrator.services:
            self.send_response(404)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": f"Service {service_id} not found"}
            self.wfile.write(json.dumps(error_response).encode())
            return
        
        success = self.orchestrator.restart_service(service_id)
        
        response = {
            "service": service_id,
            "action": "restart",
            "success": success,
            "timestamp": datetime.now().isoformat()
        }
        
        status_code = 200 if success else 500
        self.send_response(status_code)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_route_request(self):
        """Route une requête vers le service approprié"""
        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        
        try:
            request_data = json.loads(post_data.decode('utf-8'))
            
            request_type = request_data.get('type', 'text-to-image')
            use_priority = request_data.get('priority', True)
            
            selected_service = self.orchestrator.get_service_for_request(
                request_type, use_priority
            )
            
            if selected_service:
                service_config = self.orchestrator.services[selected_service]
                response = {
                    "status": "routed",
                    "selected_service": selected_service,
                    "service_info": {
                        "name": service_config.get('name'),
                        "type": service_config.get('type'),
                        "port": service_config.get('port'),
                        "capabilities": service_config.get('capabilities')
                    },
                    "timestamp": datetime.now().isoformat()
                }
            else:
                response = {
                    "status": "no_service_available",
                    "error": f"No healthy service available for request type: {request_type}",
                    "timestamp": datetime.now().isoformat()
                }
                self.send_response(503)
                self.send_header("Content-type", "application/json")
                self.end_headers()
                self.wfile.write(json.dumps(response).encode())
                return
            
            self.send_response(200)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps(response, indent=2).encode())
            
        except json.JSONDecodeError:
            self.send_response(400)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": "Invalid JSON in request body"}
            self.wfile.write(json.dumps(error_response).encode())
        except Exception as e:
            logger.error(f"Erreur lors du routage: {e}")
            self.send_response(500)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": "Internal server error during routing"}
            self.wfile.write(json.dumps(error_response).encode())
    
    def log_message(self, format, *args):
        """Override pour éviter le logging par défaut du serveur HTTP"""
        pass

def create_handler(orchestrator: GenAIOrchestrator):
    """Crée un handler avec l'orchestrateur injecté"""
    def handler(*args, **kwargs):
        return OrchestratorAPI(orchestrator, *args, **kwargs)
    return handler

def main():
    """Fonction principale de l'orchestrateur"""
    port = int(os.environ.get('ORCHESTRATOR_PORT', 8090))
    config_path = os.environ.get('CONFIG_PATH', '/app/config/services.yml')
    
    logger.info(f"Démarrage de l'orchestrateur GenAI sur le port {port}")
    
    # Initialiser l'orchestrateur
    orchestrator = GenAIOrchestrator(config_path)
    
    # Créer le serveur HTTP
    handler_class = create_handler(orchestrator)
    
    try:
        with socketserver.TCPServer(("", port), handler_class) as httpd:
            logger.info(f"Orchestrateur démarré et écoute sur le port {port}")
            httpd.serve_forever()
    except KeyboardInterrupt:
        logger.info("Arrêt de l'orchestrateur")
    except Exception as e:
        logger.error(f"Erreur lors du démarrage de l'orchestrateur: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()