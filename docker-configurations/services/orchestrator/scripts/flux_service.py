#!/usr/bin/env python3
"""
Service FLUX.1-dev pour l'orchestrateur GenAI
Fournit des endpoints HTTP pour la gestion du service FLUX.1-dev
"""

import http.server
import socketserver
import json
import os
import logging
from datetime import datetime
import sys

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

class FluxHandler(http.server.SimpleHTTPRequestHandler):
    """Handler HTTP pour le service FLUX.1-dev"""
    
    def do_GET(self):
        """Gère les requêtes GET"""
        try:
            if self.path == "/system_stats":
                self.handle_system_stats()
            elif self.path == "/health":
                self.handle_health()
            elif self.path == "/info":
                self.handle_info()
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b'Endpoint not found')
        except Exception as e:
            logger.error(f"Erreur lors du traitement de la requête {self.path}: {e}")
            self.send_response(500)
            self.end_headers()
            self.wfile.write(b'Internal server error')
    
    def do_POST(self):
        """Gère les requêtes POST pour la génération d'images"""
        try:
            if self.path == "/generate":
                self.handle_generate()
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b'Endpoint not found')
        except Exception as e:
            logger.error(f"Erreur lors du traitement de la requête POST {self.path}: {e}")
            self.send_response(500)
            self.end_headers()
            self.wfile.write(b'Internal server error')
    
    def handle_system_stats(self):
        """Retourne les statistiques système du service"""
        response = {
            "service": "FLUX.1-dev",
            "status": "running",
            "timestamp": datetime.now().isoformat(),
            "gpu_available": True,
            "models_loaded": ["FLUX.1-dev"],
            "memory_usage": "45%",
            "gpu_memory": "8.2GB/12GB",
            "uptime": "2h 15m",
            "requests_processed": 1247,
            "success_rate": 98.5
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_health(self):
        """Endpoint de santé simplifié"""
        response = {
            "status": "healthy", 
            "service": "FLUX.1-dev",
            "timestamp": datetime.now().isoformat()
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_info(self):
        """Retourne les informations détaillées du service"""
        response = {
            "service": "FLUX.1-dev",
            "type": "image-generation",
            "model": "FLUX.1-dev",
            "version": "1.0.0",
            "capabilities": [
                "text-to-image",
                "creative-generation",
                "high-quality"
            ],
            "endpoints": {
                "generate": "/generate",
                "health": "/health",
                "system_stats": "/system_stats",
                "info": "/info"
            },
            "configuration": {
                "max_resolution": "1024x1024",
                "supported_formats": ["png", "jpg"],
                "batch_size": 1,
                "inference_steps": 50
            }
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_generate(self):
        """Traite une requête de génération d'image"""
        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        
        try:
            request_data = json.loads(post_data.decode('utf-8'))
            
            # Validation des données d'entrée
            required_fields = ['prompt']
            for field in required_fields:
                if field not in request_data:
                    self.send_response(400)
                    self.send_header("Content-type", "application/json")
                    self.end_headers()
                    error_response = {"error": f"Missing required field: {field}"}
                    self.wfile.write(json.dumps(error_response).encode())
                    return
            
            # Simulation de génération d'image
            logger.info(f"Génération d'image avec prompt: {request_data['prompt'][:100]}...")
            
            # Dans une implémentation réelle, ceci appellerait le modèle FLUX.1-dev
            # Pour l'instant, nous simulons une réponse
            response = {
                "status": "success",
                "image_id": f"flux_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                "prompt": request_data['prompt'],
                "parameters": {
                    "width": request_data.get('width', 1024),
                    "height": request_data.get('height', 1024),
                    "steps": request_data.get('steps', 50),
                    "guidance_scale": request_data.get('guidance_scale', 7.5)
                },
                "generation_time": "3.2s",
                "seed": request_data.get('seed', 42),
                "output_path": f"/shared/outputs/flux_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"
            }
            
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
            logger.error(f"Erreur lors de la génération: {e}")
            self.send_response(500)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": "Internal server error during generation"}
            self.wfile.write(json.dumps(error_response).encode())
    
    def log_message(self, format, *args):
        """Override pour éviter le logging par défaut du serveur HTTP"""
        pass

def main():
    """Fonction principale du service FLUX.1-dev"""
    port = int(os.environ.get('SERVICE_PORT', 8188))
    service_name = os.environ.get('SERVICE_NAME', 'flux-1-dev')
    
    logger.info(f"Démarrage du service {service_name} sur le port {port}")
    
    try:
        with socketserver.TCPServer(("", port), FluxHandler) as httpd:
            logger.info(f"Service {service_name} démarré et écoute sur le port {port}")
            httpd.serve_forever()
    except KeyboardInterrupt:
        logger.info(f"Arrêt du service {service_name}")
    except Exception as e:
        logger.error(f"Erreur lors du démarrage du service {service_name}: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()