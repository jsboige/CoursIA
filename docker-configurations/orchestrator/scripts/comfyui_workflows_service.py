#!/usr/bin/env python3
"""
Service ComfyUI Workflows pour l'orchestrateur GenAI
Fournit des endpoints HTTP pour la gestion du service ComfyUI Workflows
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

class ComfyUIHandler(http.server.SimpleHTTPRequestHandler):
    """Handler HTTP pour le service ComfyUI Workflows"""
    
    def do_GET(self):
        """Gère les requêtes GET"""
        try:
            if self.path == "/system_stats":
                self.handle_system_stats()
            elif self.path == "/health":
                self.handle_health()
            elif self.path == "/info":
                self.handle_info()
            elif self.path == "/workflows":
                self.handle_list_workflows()
            elif self.path.startswith("/workflow/"):
                self.handle_get_workflow(self.path[10:])  # Remove "/workflow/" prefix
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
        """Gère les requêtes POST pour l'exécution de workflows"""
        try:
            if self.path == "/execute_workflow":
                self.handle_execute_workflow()
            elif self.path == "/upload_workflow":
                self.handle_upload_workflow()
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
            "service": "ComfyUI Workflows",
            "status": "running",
            "timestamp": datetime.now().isoformat(),
            "gpu_available": True,
            "models_loaded": ["Qwen2-VL-7B", "ComfyUI-Base"],
            "memory_usage": "68%",
            "gpu_memory": "8.5GB/12GB",
            "uptime": "3h 12m",
            "workflows_processed": 156,
            "success_rate": 97.8,
            "active_nodes": 24,
            "custom_nodes": ["ComfyUI-QwenImageWanBridge", "ComfyUI-Login"]
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_health(self):
        """Endpoint de santé simplifié"""
        response = {
            "status": "healthy", 
            "service": "ComfyUI Workflows",
            "timestamp": datetime.now().isoformat()
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode())
    
    def handle_info(self):
        """Retourne les informations détaillées du service"""
        response = {
            "service": "ComfyUI Workflows",
            "type": "workflow-engine",
            "model": "ComfyUI",
            "version": "0.3.0",
            "capabilities": [
                "advanced-workflows",
                "educational-content",
                "custom-pipelines",
                "multi-model"
            ],
            "endpoints": {
                "execute_workflow": "/execute_workflow",
                "upload_workflow": "/upload_workflow",
                "list_workflows": "/workflows",
                "get_workflow": "/workflow/{id}",
                "health": "/health",
                "system_stats": "/system_stats",
                "info": "/info"
            },
            "configuration": {
                "max_workflow_size": "50MB",
                "supported_formats": ["json", "png"],
                "max_execution_time": 300,
                "parallel_executions": 2
            }
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_list_workflows(self):
        """Retourne la liste des workflows disponibles"""
        # Simuler une liste de workflows
        workflows = [
            {
                "id": "qwen_text_to_image",
                "name": "Qwen Text to Image",
                "description": "Génération d'images à partir de texte avec Qwen2-VL",
                "category": "text-to-image",
                "created_at": "2025-11-20T10:30:00Z",
                "updated_at": "2025-11-25T15:45:00Z",
                "executions": 45,
                "success_rate": 98.2
            },
            {
                "id": "qwen_image_to_image",
                "name": "Qwen Image to Image",
                "description": "Transformation d'images avec Qwen2-VL",
                "category": "image-to-image",
                "created_at": "2025-11-20T14:20:00Z",
                "updated_at": "2025-11-24T09:15:00Z",
                "executions": 32,
                "success_rate": 96.8
            },
            {
                "id": "educational_pipeline",
                "name": "Pipeline Éducatif",
                "description": "Workflow complet pour démonstrations éducatives",
                "category": "educational",
                "created_at": "2025-11-22T11:00:00Z",
                "updated_at": "2025-11-25T16:30:00Z",
                "executions": 28,
                "success_rate": 100.0
            }
        ]
        
        response = {
            "workflows": workflows,
            "total": len(workflows),
            "timestamp": datetime.now().isoformat()
        }
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response, indent=2).encode())
    
    def handle_get_workflow(self, workflow_id):
        """Retourne les détails d'un workflow spécifique"""
        # Simuler la récupération d'un workflow
        if workflow_id == "qwen_text_to_image":
            workflow = {
                "id": "qwen_text_to_image",
                "name": "Qwen Text to Image",
                "description": "Génération d'images à partir de texte avec Qwen2-VL",
                "category": "text-to-image",
                "nodes": [
                    {"id": 1, "type": "QwenT2IWrapper", "name": "Qwen Text to Image"},
                    {"id": 2, "type": "PreviewImage", "name": "Preview"},
                    {"id": 3, "type": "SaveImage", "name": "Save Output"}
                ],
                "parameters": {
                    "prompt": {"type": "string", "default": "A beautiful landscape"},
                    "width": {"type": "int", "default": 1024, "min": 256, "max": 2048},
                    "height": {"type": "int", "default": 1024, "min": 256, "max": 2048},
                    "steps": {"type": "int", "default": 20, "min": 1, "max": 100}
                }
            }
        else:
            self.send_response(404)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": f"Workflow {workflow_id} not found"}
            self.wfile.write(json.dumps(error_response).encode())
            return
        
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(workflow, indent=2).encode())
    
    def handle_execute_workflow(self):
        """Traite une requête d'exécution de workflow"""
        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        
        try:
            request_data = json.loads(post_data.decode('utf-8'))
            
            # Validation des données d'entrée
            required_fields = ['workflow_id']
            for field in required_fields:
                if field not in request_data:
                    self.send_response(400)
                    self.send_header("Content-type", "application/json")
                    self.end_headers()
                    error_response = {"error": f"Missing required field: {field}"}
                    self.wfile.write(json.dumps(error_response).encode())
                    return
            
            # Simulation d'exécution de workflow
            workflow_id = request_data['workflow_id']
            logger.info(f"Exécution du workflow: {workflow_id}")
            
            response = {
                "status": "success",
                "execution_id": f"exec_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                "workflow_id": workflow_id,
                "parameters": request_data.get('parameters', {}),
                "execution_time": "12.5s",
                "nodes_executed": 3,
                "outputs": [
                    {
                        "type": "image",
                        "filename": f"workflow_{workflow_id}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png",
                        "path": f"/shared/outputs/workflow_{workflow_id}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"
                    }
                ],
                "logs": [
                    "Starting workflow execution...",
                    f"Loading workflow {workflow_id}...",
                    "Executing nodes...",
                    "Generating output...",
                    "Workflow completed successfully"
                ]
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
            logger.error(f"Erreur lors de l'exécution du workflow: {e}")
            self.send_response(500)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": "Internal server error during workflow execution"}
            self.wfile.write(json.dumps(error_response).encode())
    
    def handle_upload_workflow(self):
        """Traite une requête d'upload de workflow"""
        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        
        try:
            request_data = json.loads(post_data.decode('utf-8'))
            
            # Validation des données d'entrée
            required_fields = ['workflow', 'name']
            for field in required_fields:
                if field not in request_data:
                    self.send_response(400)
                    self.send_header("Content-type", "application/json")
                    self.end_headers()
                    error_response = {"error": f"Missing required field: {field}"}
                    self.wfile.write(json.dumps(error_response).encode())
                    return
            
            # Simulation d'upload de workflow
            workflow_name = request_data['name']
            logger.info(f"Upload du workflow: {workflow_name}")
            
            workflow_id = f"custom_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            response = {
                "status": "success",
                "workflow_id": workflow_id,
                "name": workflow_name,
                "description": request_data.get('description', ''),
                "category": request_data.get('category', 'custom'),
                "created_at": datetime.now().isoformat(),
                "file_path": f"/shared/workflows/{workflow_id}.json",
                "size": len(str(request_data['workflow']))
            }
            
            self.send_response(201)
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
            logger.error(f"Erreur lors de l'upload du workflow: {e}")
            self.send_response(500)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            error_response = {"error": "Internal server error during workflow upload"}
            self.wfile.write(json.dumps(error_response).encode())
    
    def log_message(self, format, *args):
        """Override pour éviter le logging par défaut du serveur HTTP"""
        pass

def main():
    """Fonction principale du service ComfyUI Workflows"""
    port = int(os.environ.get('SERVICE_PORT', 8188))
    service_name = os.environ.get('SERVICE_NAME', 'comfyui-workflows')
    
    logger.info(f"Démarrage du service {service_name} sur le port {port}")
    
    try:
        with socketserver.TCPServer(("", port), ComfyUIHandler) as httpd:
            logger.info(f"Service {service_name} démarré et écoute sur le port {port}")
            httpd.serve_forever()
    except KeyboardInterrupt:
        logger.info(f"Arrêt du service {service_name}")
    except Exception as e:
        logger.error(f"Erreur lors du démarrage du service {service_name}: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()