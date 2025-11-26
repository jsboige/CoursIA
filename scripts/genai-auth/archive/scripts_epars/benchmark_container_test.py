#!/usr/bin/env python3
"""
Script de benchmark pour ComfyUI Qwen - Version conteneur direct
Test simple avec modèle SDXL de base
"""

import json
import time
import websocket
import uuid
import subprocess
import threading
import os
import sys
import base64
from datetime import datetime
from statistics import mean
import argparse

class ComfyUIBenchmarkContainer:
    def __init__(self, server_address="127.0.0.1:8188", workflow=None):
        self.server_address = server_address
        self.client_id = str(uuid.uuid4())
        self.workflow = workflow
        self.generation_times = []
        self.gpu_monitoring_data = []
        self.monitoring_active = False
        self.generation_complete = False
        
    def generate_image(self):
        """Génère une image et mesure le temps"""
        try:
            # Créer le prompt avec un client_id unique
            prompt = self.workflow.copy()
            prompt["client_id"] = self.client_id
            self.current_prompt_id = str(uuid.uuid4())
            
            # Envoyer le prompt via WebSocket
            ws_message = {
                "prompt": prompt,
                "prompt_id": self.current_prompt_id
            }
            
            print(f"📤 Prompt envoyé (ID: {self.current_prompt_id[:8]}...)")
            
            # Attendre la fin de la génération
            timeout = 120  # 2 minutes maximum
            start_wait = time.time()
            
            while not self.generation_complete and (time.time() - start_wait) < timeout:
                time.sleep(0.5)
            
            if not self.generation_complete:
                print("⚠ Timeout: la génération a pris trop de temps")
                return False
            
            return True
            
        except Exception as e:
            print(f"✗ Erreur lors de la génération: {e}")
            return False
    
    def run_benchmark(self, iterations=1):
        """Exécute le benchmark complet"""
        print(f"🚀 Démarrage du benchmark ComfyUI Qwen ({iterations} itération)")
        print(f"📡 Serveur: {self.server_address}")
        print(f"📄 Workflow: {json.dumps(self.workflow, indent=2)}")
        print("-" * 50)
        
        # Se connecter à ComfyUI (sans authentification)
        ws_url = f"ws://{self.server_address}/ws?clientId={self.client_id}"
        
        try:
            self.ws = websocket.WebSocketApp(
                ws_url,
                on_open=self.on_open,
                on_message=self.on_message,
                on_error=self.on_error,
                on_close=self.on_close
            )
            
            # Démarrer la connexion dans un thread séparé
            ws_thread = threading.Thread(target=self.ws.run_forever, daemon=True)
            ws_thread.start()
            
            # Attendre que la connexion soit établie
            time.sleep(2)
            
            # Envoyer le prompt
            success = self.generate_image()
            
            if not success:
                print(f"✗ Échec de l'itération 1")
                return False
            
            # Fermer la connexion
            self.ws.close()
            
        except Exception as e:
            print(f"✗ Erreur de connexion: {e}")
            return False
    
    def on_message(self, ws, message):
        """Gère les messages WebSocket reçus"""
        message = json.loads(message)
        
        if message['type'] == 'executing':
            data = message['data']
            if data['node'] is None and data['prompt_id'] == self.current_prompt_id:
                # La génération est terminée
                end_time = time.time()
                generation_time = end_time - self.start_time
                self.generation_times.append(generation_time)
                self.generation_complete = True
                print(f"✓ Génération terminée en {generation_time:.2f} secondes")
        
        elif message['type'] == 'progress':
            data = message['data']
            if data.get('prompt_id') == self.current_prompt_id:
                progress = data.get('value', 0)
                if progress > 0:
                    print(f"🔄 Progression: {progress}%")
    
    def on_error(self, ws, error):
        """Gère les erreurs WebSocket"""
        print(f"✗ Erreur WebSocket: {error}")
    
    def on_close(self, ws, close_status_code, close_msg):
        """Gère la fermeture WebSocket"""
        print("🔌 Connexion WebSocket fermée")
    
    def on_open(self, ws):
        """Gère l'ouverture WebSocket"""
        print("🔌 Connexion WebSocket établie")

def main():
    parser = argparse.ArgumentParser(description='Benchmark ComfyUI Qwen (Container)')
    parser.add_argument('--server', default='127.0.0.1:8188',
                       help='Adresse du serveur ComfyUI (défaut: 127.0.0.1:8188)')
    parser.add_argument('--iterations', type=int, default=1,
                       help='Nombre ditérations (défaut: 1)')
    
    args = parser.parse_args()
    
    # Workflow de test simple avec SDXL
    workflow = {
        "prompt": {
            "3": {
                "class_type": "CheckpointLoaderSimple",
                "inputs": {
                    "ckpt_name": "sd_xl_base_1.0.safetensors"
                }
            },
            "6": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "text": "a simple test image",
                    "width": 512,
                    "height": 512
                }
            },
            "9": {
                "class_type": "KSampler",
                "inputs": {
                    "seed": 42,
                    "steps": 20,
                    "cfg": 7.0,
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "denoise": 0.8
                }
            },
            "10": {
                "class_type": "EmptyLatentImage",
                "inputs": {
                    "width": 512,
                    "height": 512,
                    "batch_size": 1
                }
            },
            "11": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": [
                        "6"
                    ]
                }
            },
            "12": {
                "class_type": "SaveImage",
                "inputs": {
                    "images": [
                        "10"
                    ],
                    "filename_prefix": "test_simple"
                }
            }
        }
    }
    
    # Créer et exécuter le benchmark
    benchmark = ComfyUIBenchmarkContainer(args.server, workflow)
    
    if benchmark.run_benchmark(args.iterations):
        print("\n📊 BENCHMARK TERMINÉ AVEC SUCCÈS")
        print(f"✅ Test réussi avec le modèle SDXL de base")
        print(f"🎯 Le système ComfyUI Qwen est fonctionnel pour la génération d'images")
        print(f"📝 Prochaine étape : Télécharger les modèles Qwen spécifiques")
    else:
        print("❌ Échec du benchmark")

if __name__ == "__main__":
    main()