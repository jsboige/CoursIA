#!/usr/bin/env python3
"""
Script de benchmark pour ComfyUI Qwen
Mesure les temps de génération d'images et monitor l'utilisation du GPU
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

class ComfyUIBenchmark:
    def __init__(self, server_address="127.0.0.1:8188", workflow_file="workflow_benchmark.json",
                 username="admin", password="rZDS3XQa/8!v9L"):
        self.server_address = server_address
        self.client_id = str(uuid.uuid4())
        self.workflow_file = workflow_file
        self.workflow = None
        self.generation_times = []
        self.gpu_monitoring_data = []
        self.monitoring_active = False
        self.generation_complete = False
        self.username = username
        self.password = password
        self.auth_token = None
        
    def authenticate(self):
        """Authentifie auprès de ComfyUI et obtient un token"""
        try:
            import requests
            
            auth_url = f"http://{self.server_address}/user/login"
            auth_data = {
                "username": self.username,
                "password": self.password
            }
            
            response = requests.post(auth_url, json=auth_data, timeout=30)
            if response.status_code == 200:
                result = response.json()
                self.auth_token = result.get('access_token')
                if self.auth_token:
                    print(f"✓ Authentification réussie")
                    return True
                else:
                    print(f"✗ Token non trouvé dans la réponse")
                    return False
            else:
                print(f"✗ Échec de l'authentification: {response.status_code}")
                print(f"   Réponse: {response.text}")
                return False
                
        except Exception as e:
            print(f"✗ Erreur lors de l'authentification: {e}")
            return False

    def load_workflow(self):
        """Charge le workflow depuis le fichier JSON"""
        try:
            with open(self.workflow_file, 'r') as f:
                self.workflow = json.load(f)
            print(f"✓ Workflow chargé depuis {self.workflow_file}")
            return True
        except Exception as e:
            print(f"✗ Erreur lors du chargement du workflow: {e}")
            return False
    
    def monitor_gpu(self):
        """Monitor l'utilisation du GPU en arrière-plan"""
        self.monitoring_active = True
        print("🔍 Démarrage du monitoring GPU...")
        
        while self.monitoring_active:
            try:
                # Exécuter nvidia-smi et capturer la sortie
                result = subprocess.run([
                    'nvidia-smi', '--query-gpu=memory.used,memory.total,utilization.gpu,temperature.gpu',
                    '--format=csv,noheader,nounits'
                ], capture_output=True, text=True, timeout=2)
                
                if result.returncode == 0:
                    lines = result.stdout.strip().split('\n')
                    for line in lines:
                        if line.strip():
                            parts = line.split(', ')
                            if len(parts) >= 4:
                                memory_used = int(parts[0])
                                memory_total = int(parts[1])
                                gpu_util = int(parts[2])
                                temp = int(parts[3])
                                
                                timestamp = datetime.now().isoformat()
                                self.gpu_monitoring_data.append({
                                    'timestamp': timestamp,
                                    'memory_used_mb': memory_used,
                                    'memory_total_mb': memory_total,
                                    'memory_usage_percent': round((memory_used / memory_total) * 100, 2),
                                    'gpu_utilization_percent': gpu_util,
                                    'temperature_celsius': temp
                                })
                
                time.sleep(1)  # Échantillonnage chaque seconde
                
            except subprocess.TimeoutExpired:
                continue
            except Exception as e:
                print(f"⚠ Erreur monitoring GPU: {e}")
                time.sleep(1)
    
    def start_gpu_monitoring(self):
        """Démarre le monitoring GPU dans un thread séparé"""
        self.monitoring_thread = threading.Thread(target=self.monitor_gpu, daemon=True)
        self.monitoring_thread.start()
    
    def stop_gpu_monitoring(self):
        """Arrête le monitoring GPU"""
        self.monitoring_active = False
        if hasattr(self, 'monitoring_thread'):
            self.monitoring_thread.join(timeout=2)
    
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
                
                # Arrêter le monitoring GPU après un court délai pour capturer les dernières métriques
                time.sleep(1)
                self.stop_gpu_monitoring()
    
    def on_error(self, ws, error):
        """Gère les erreurs WebSocket"""
        print(f"✗ Erreur WebSocket: {error}")
    
    def on_close(self, ws, close_status_code, close_msg):
        """Gère la fermeture WebSocket"""
        print("🔌 Connexion WebSocket fermée")
    
    def on_open(self, ws):
        """Gère l'ouverture WebSocket"""
        print("🔌 Connexion WebSocket établie")
    
    def generate_image(self):
        """Génère une image et mesure le temps"""
        try:
            # Créer le prompt avec un client_id unique
            prompt = self.workflow.copy()
            prompt["client_id"] = self.client_id
            self.current_prompt_id = str(uuid.uuid4())
            
            # Démarrer le monitoring GPU
            self.start_gpu_monitoring()
            time.sleep(1)  # Laisser le monitoring démarrer
            
            # Envoyer le prompt
            self.start_time = time.time()
            self.generation_complete = False
            
            ws_message = {
                "prompt": prompt,
                "prompt_id": self.current_prompt_id
            }
            
            self.ws.send(json.dumps(ws_message))
            print(f"📤 Prompt envoyé (ID: {self.current_prompt_id[:8]}...)")
            
            # Attendre la fin de la génération
            timeout = 300  # 5 minutes maximum
            start_wait = time.time()
            
            while not self.generation_complete and (time.time() - start_wait) < timeout:
                time.sleep(0.5)
            
            if not self.generation_complete:
                print("⚠ Timeout: la génération a pris trop de temps")
                self.stop_gpu_monitoring()
                return False
                
            return True
            
        except Exception as e:
            print(f"✗ Erreur lors de la génération: {e}")
            self.stop_gpu_monitoring()
            return False
    
    def run_benchmark(self, iterations=5):
        """Exécute le benchmark complet"""
        print(f"🚀 Démarrage du benchmark ComfyUI Qwen ({iterations} itérations)")
        print(f"📡 Serveur: {self.server_address}")
        print(f"📄 Workflow: {self.workflow_file}")
        print("-" * 50)
        
        # Charger le workflow
        if not self.load_workflow():
            return False
        
        # Se connecter à ComfyUI
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
            
            # Exécuter les itérations
            for i in range(iterations):
                print(f"\n🔄 Itération {i+1}/{iterations}")
                success = self.generate_image()
                
                if not success:
                    print(f"✗ Échec de l'itération {i+1}")
                    continue
                
                # Pause entre les générations
                if i < iterations - 1:
                    print("⏳ Pause de 5 secondes...")
                    time.sleep(5)
            
            # Fermer la connexion
            self.ws.close()
            
        except Exception as e:
            print(f"✗ Erreur de connexion: {e}")
            return False
        
        return True
    
    def analyze_results(self):
        """Analyse et affiche les résultats"""
        print("\n" + "=" * 50)
        print("📊 RÉSULTATS DU BENCHMARK")
        print("=" * 50)
        
        if not self.generation_times:
            print("❌ Aucune génération réussie à analyser")
            return
        
        # Statistiques des temps de génération
        avg_time = mean(self.generation_times)
        min_time = min(self.generation_times)
        max_time = max(self.generation_times)
        
        print(f"\n⏱️  TEMPS DE GÉNÉRATION:")
        print(f"   • Moyenne: {avg_time:.2f} secondes")
        print(f"   • Minimum: {min_time:.2f} secondes")
        print(f"   • Maximum: {max_time:.2f} secondes")
        print(f"   • Écart-type: {(sum((x - avg_time) ** 2 for x in self.generation_times) / len(self.generation_times)) ** 0.5:.2f} secondes")
        
        print(f"\n📈 DÉTAILS PAR ITÉRATION:")
        for i, gen_time in enumerate(self.generation_times, 1):
            print(f"   • Itération {i}: {gen_time:.2f} secondes")
        
        # Analyse GPU
        if self.gpu_monitoring_data:
            print(f"\n🔥 ANALYSE GPU:")
            
            # Calculer les moyennes pour chaque métrique
            avg_memory = mean(d['memory_usage_percent'] for d in self.gpu_monitoring_data)
            max_memory = max(d['memory_usage_percent'] for d in self.gpu_monitoring_data)
            avg_gpu_util = mean(d['gpu_utilization_percent'] for d in self.gpu_monitoring_data)
            max_gpu_util = max(d['gpu_utilization_percent'] for d in self.gpu_monitoring_data)
            avg_temp = mean(d['temperature_celsius'] for d in self.gpu_monitoring_data)
            max_temp = max(d['temperature_celsius'] for d in self.gpu_monitoring_data)
            
            print(f"   • VRAM utilisée: {avg_memory:.1f}% (max: {max_memory:.1f}%)")
            print(f"   • Utilisation GPU: {avg_gpu_util:.1f}% (max: {max_gpu_util:.1f}%)")
            print(f"   • Température: {avg_temp:.1f}°C (max: {max_temp:.1f}°C)")
            print(f"   • Nombre d'échantillons: {len(self.gpu_monitoring_data)}")
        
        # Identifier les problèmes potentiels
        print(f"\n🔍 ANALYSE DES PERFORMANCES:")
        
        if avg_time > 120:
            print("   ⚠️  Temps de génération élevé (>2 minutes)")
        elif avg_time > 60:
            print("   ⚠️  Temps de génération modéré (>1 minute)")
        else:
            print("   ✅ Temps de génération acceptable")
        
        if self.gpu_monitoring_data:
            if avg_gpu_util < 80:
                print("   ⚠️  Utilisation GPU faible (<80%) - possible goulot d'étranglement")
            else:
                print("   ✅ GPU bien utilisé")
            
            if max_temp > 85:
                print("   ⚠️  Température GPU élevée (>85°C) - possible thermal throttling")
            else:
                print("   ✅ Température GPU normale")
    
    def save_results(self, output_file=None):
        """Sauvegarde les résultats dans un fichier JSON"""
        if output_file is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_file = f"benchmark_results_{timestamp}.json"
        
        results = {
            "timestamp": datetime.now().isoformat(),
            "server_address": self.server_address,
            "workflow_file": self.workflow_file,
            "generation_times": self.generation_times,
            "statistics": {
                "count": len(self.generation_times),
                "average_seconds": mean(self.generation_times) if self.generation_times else 0,
                "min_seconds": min(self.generation_times) if self.generation_times else 0,
                "max_seconds": max(self.generation_times) if self.generation_times else 0
            },
            "gpu_monitoring": self.gpu_monitoring_data
        }
        
        try:
            with open(output_file, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"\n💾 Résultats sauvegardés dans: {output_file}")
        except Exception as e:
            print(f"❌ Erreur lors de la sauvegarde: {e}")

def main():
    parser = argparse.ArgumentParser(description='Benchmark ComfyUI Qwen')
    parser.add_argument('--server', default='127.0.0.1:8188',
                       help='Adresse du serveur ComfyUI (défaut: 127.0.0.1:8188)')
    parser.add_argument('--workflow', default='workflow_benchmark.json',
                       help='Fichier workflow JSON (défaut: workflow_benchmark.json)')
    parser.add_argument('--iterations', type=int, default=5,
                       help='Nombre ditérations (défaut: 5)')
    parser.add_argument('--output', help='Fichier de sortie JSON')
    parser.add_argument('--username', default='admin',
                       help='Nom d utilisateur ComfyUI (défaut: admin)')
    parser.add_argument('--password', default='rZDS3XQa/8!v9L',
                       help='Mot de passe ComfyUI (défaut: celui du .env)')
    
    args = parser.parse_args()
    
    # Vérifier si nvidia-smi est disponible
    try:
        subprocess.run(['nvidia-smi'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("❌ nvidia-smi n'est pas disponible. Le monitoring GPU ne fonctionnera pas.")
        return
    
    # Créer et exécuter le benchmark
    benchmark = ComfyUIBenchmark(args.server, args.workflow, args.username, args.password)
    
    if benchmark.run_benchmark(args.iterations):
        benchmark.analyze_results()
        benchmark.save_results(args.output)
    else:
        print("❌ Échec du benchmark")

if __name__ == "__main__":
    main()