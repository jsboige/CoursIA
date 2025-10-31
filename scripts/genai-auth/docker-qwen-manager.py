#!/usr/bin/env python3
"""
Gestionnaire Docker pour ComfyUI Qwen - Script consolidé paramétrique

Ce script consolide les fonctionnalités de gestion Docker pour ComfyUI Qwen :
- Démarrage/arrêt des conteneurs
- Monitoring des ressources
- Validation des configurations
- Gestion des volumes et réseaux
- Diagnostic des problèmes Docker

Auteur: Consolidation des scripts Docker existants
Date: 2025-10-31
Version: 1.0.0
"""

import argparse
import json
import logging
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('docker_qwen_manager.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class DockerQwenManager:
    """Gestionnaire Docker pour ComfyUI Qwen"""
    
    def __init__(self, config_file: Optional[str] = None):
        self.config_file = Path(config_file) if config_file else Path.cwd() / "docker_qwen_config.json"
        self.config = self._load_config()
        
    def _load_config(self) -> Dict[str, Any]:
        """Charge la configuration depuis le fichier"""
        try:
            if self.config_file.exists():
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            else:
                logger.info(f"Création du fichier de configuration: {self.config_file}")
                return self._get_default_config()
        except Exception as e:
            logger.error(f"Erreur chargement configuration: {e}")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict[str, Any]:
        """Retourne la configuration par défaut"""
        return {
            "containers": {
                "comfyui-qwen": {
                    "image": "comfyui-qwen:latest",
                    "container_name": "comfyui-qwen",
                    "ports": ["8188:8188"],
                    "volumes": [
                        "/home/jesse/SD/workspace/comfyui-qwen:/workspace/ComfyUI",
                        "/home/jesse/SD/models:/workspace/ComfyUI/models"
                    ],
                    "environment": {
                        "COMFYUI_LOGIN_ENABLED": "true"
                    },
                    "docker_compose_file": "docker-configurations/comfyui-qwen/docker-compose.yml",
                    "health_check": {
                        "endpoint": "/system_stats",
                        "timeout": 30,
                        "retries": 3
                    }
                }
            },
            "monitoring": {
                "enabled": True,
                "interval": 60,
                "resource_checks": ["cpu", "memory", "disk", "network"],
                "log_retention_days": 7
            },
            "operations": {
                "startup_timeout": 120,
                "shutdown_timeout": 30,
                "restart_delay": 10,
                "backup_enabled": True
            }
        }
    
    def _save_config(self):
        """Sauvegarde la configuration dans le fichier"""
        try:
            with open(self.config_file, 'w', encoding='utf-8') as f:
                json.dump(self.config, f, indent=2)
            logger.info(f"Configuration sauvegardée: {self.config_file}")
        except Exception as e:
            logger.error(f"Erreur sauvegarde configuration: {e}")
    
    def start_container(self, container_name: str) -> bool:
        """Démarre un conteneur Docker"""
        logger.info(f"Démarrage du conteneur: {container_name}")
        
        if container_name not in self.config["containers"]:
            logger.error(f"Conteneur inconnu: {container_name}")
            return False
        
        container_config = self.config["containers"][container_name]
        
        try:
            # Vérifier si le conteneur est déjà en cours
            result = subprocess.run([
                'docker', 'ps', '--filter', f'name={container_name}', '--format', '{{.Status}}'
            ], capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0 and 'Up' in result.stdout:
                logger.info(f"Conteneur {container_name} déjà en cours d'exécution")
                return True
            
            # Démarrer le conteneur
            cmd = [
                'docker-compose', '-f', container_config["docker_compose_file"],
                'up', '-d', container_name
            ]
            
            logger.info(f"Commande: {' '.join(cmd)}")
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=container_config["operations"]["startup_timeout"])
            
            if result.returncode == 0:
                logger.info(f"✅ Conteneur {container_name} démarré avec succès")
                return True
            else:
                logger.error(f"❌ Échec démarrage conteneur {container_name}: {result.stderr}")
                return False
                
        except subprocess.TimeoutExpired:
            logger.error(f"❌ Timeout démarrage conteneur {container_name}")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur démarrage conteneur {container_name}: {e}")
            return False
    
    def stop_container(self, container_name: str) -> bool:
        """Arrête un conteneur Docker"""
        logger.info(f"Arrêt du conteneur: {container_name}")
        
        if container_name not in self.config["containers"]:
            logger.error(f"Conteneur inconnu: {container_name}")
            return False
        
        container_config = self.config["containers"][container_name]
        
        try:
            cmd = [
                'docker-compose', '-f', container_config["docker_compose_file"],
                'stop', container_name
            ]
            
            logger.info(f"Commande: {' '.join(cmd)}")
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=container_config["operations"]["shutdown_timeout"])
            
            if result.returncode == 0:
                logger.info(f"✅ Conteneur {container_name} arrêté avec succès")
                return True
            else:
                logger.error(f"❌ Échec arrêt conteneur {container_name}: {result.stderr}")
                return False
                
        except subprocess.TimeoutExpired:
            logger.error(f"❌ Timeout arrêt conteneur {container_name}")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur arrêt conteneur {container_name}: {e}")
            return False
    
    def restart_container(self, container_name: str) -> bool:
        """Redémarre un conteneur Docker"""
        logger.info(f"Redémarrage du conteneur: {container_name}")
        
        # Arrêter puis démarrer
        if self.stop_container(container_name):
            time.sleep(self.config["operations"]["restart_delay"])
            return self.start_container(container_name)
        else:
            return False
    
    def get_container_status(self, container_name: str) -> Dict[str, Any]:
        """Récupère le statut d'un conteneur"""
        logger.info(f"Vérification du statut du conteneur: {container_name}")
        
        if container_name not in self.config["containers"]:
            logger.error(f"Conteneur inconnu: {container_name}")
            return {"error": f"Conteneur inconnu: {container_name}"}
        
        try:
            result = subprocess.run([
                'docker', 'ps', '--filter', f'name={container_name}',
                '--format', 'table {{.Names}}\t{{.Status}}\t{{.Ports}}'
            ], capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0:
                lines = result.stdout.strip().split('\n')
                for line in lines[1:]:  # Ignorer l'en-tête
                    parts = line.split('\t')
                    if len(parts) >= 2:
                        return {
                            "name": parts[0],
                            "status": parts[1],
                            "ports": parts[2] if len(parts) > 2 else "N/A",
                            "uptime": "running" if parts[1] == "Up" else "stopped"
                        }
            
            return {"error": f"Conteneur {container_name} non trouvé"}
            
        except Exception as e:
            return {"error": f"Erreur vérification statut: {e}"}
    
    def check_container_health(self, container_name: str) -> Dict[str, Any]:
        """Vérifie la santé d'un conteneur"""
        logger.info(f"Vérification de la santé du conteneur: {container_name}")
        
        if container_name not in self.config["containers"]:
            logger.error(f"Conteneur inconnu: {container_name}")
            return {"error": f"Conteneur inconnu: {container_name}"}
        
        container_config = self.config["containers"][container_name]
        health_config = container_config.get("health_check", {})
        
        try:
            # Test de l'endpoint de santé
            import requests
            endpoint = f"http://localhost:{container_config['ports'][0].split(':')[1]}{health_config['endpoint']}"
            response = requests.get(endpoint, timeout=health_config["timeout"])
            
            health_status = {
                "container": container_name,
                "endpoint": endpoint,
                "status_code": response.status_code,
                "response_time": response.elapsed.total_seconds(),
                "timestamp": datetime.now().isoformat(),
                "healthy": response.status_code == 200
            }
            
            if response.status_code == 200:
                logger.info(f"✅ Conteneur {container_name} en bonne santé")
            else:
                logger.warning(f"⚠️ Conteneur {container_name} a des problèmes de santé: {response.status_code}")
            
            return health_status
            
        except Exception as e:
            return {"error": f"Erreur vérification santé: {e}"}
    
    def monitor_resources(self, container_name: str, duration: int = 60) -> Dict[str, Any]:
        """Monitore les ressources d'un conteneur pendant une durée donnée"""
        logger.info(f"Monitoring des ressources du conteneur: {container_name} (durée: {duration}s)")
        
        if container_name not in self.config["containers"]:
            logger.error(f"Conteneur inconnu: {container_name}")
            return {"error": f"Conteneur inconnu: {container_name}"}
        
        try:
            # Stats Docker
            stats_cmd = [
                'docker', 'stats', '--no-stream', '--format', 'json',
                container_name
            ]
            
            stats_result = subprocess.run(stats_cmd, capture_output=True, text=True, timeout=10)
            
            monitoring_data = {
                "container": container_name,
                "start_time": datetime.now().isoformat(),
                "duration": duration,
                "samples": []
            }
            
            if stats_result.returncode == 0:
                try:
                    stats = json.loads(stats_result.stdout)
                    if stats and len(stats) > 0:
                        container_stats = stats[0]
                        
                        monitoring_data.update({
                            "cpu_usage": container_stats.get("cpu_perc", "N/A"),
                            "memory_usage": container_stats.get("mem_usage", "N/A"),
                            "network_io": container_stats.get("net_io", "N/A"),
                            "block_io": container_stats.get("block_io", "N/A")
                        })
                        
                        logger.info(f"Stats Docker récupérées pour {container_name}")
                    else:
                        logger.warning(f"Aucune statistique disponible pour {container_name}")
                except json.JSONDecodeError:
                    logger.error(f"Erreur parsing stats Docker: {stats_result.stderr}")
            else:
                logger.error(f"Erreur récupération stats Docker: {stats_result.stderr}")
            
            # Monitoring en boucle
            end_time = time.time() + duration
            sample_count = 0
            
            while time.time() < end_time:
                try:
                    # Prendre un échantillon
                    if stats_result.returncode == 0:
                        monitoring_data["samples"].append({
                            "timestamp": datetime.now().isoformat(),
                            "sample_id": sample_count
                        })
                        sample_count += 1
                    
                    time.sleep(self.config["monitoring"]["interval"])
                    
                except KeyboardInterrupt:
                    logger.info(f"Monitoring interrompu après {sample_count} échantillons")
                    break
                except Exception as e:
                    logger.error(f"Erreur monitoring: {e}")
                    break
            
            monitoring_data["end_time"] = datetime.now().isoformat()
            monitoring_data["total_samples"] = sample_count
            
            return monitoring_data
            
        except Exception as e:
            return {"error": f"Erreur monitoring: {e}"}
    
    def validate_docker_setup(self) -> Dict[str, Any]:
        """Valide la configuration Docker complète"""
        logger.info("Validation de la configuration Docker...")
        
        validation_results = {
            "validation_timestamp": datetime.now().isoformat(),
            "checks": {},
            "issues": [],
            "recommendations": []
        }
        
        # Vérifier Docker
        try:
            result = subprocess.run(['docker', '--version'], capture_output=True, text=True)
            if result.returncode == 0:
                validation_results["checks"]["docker"] = {
                    "status": "installed",
                    "version": result.stdout.strip()
                }
            else:
                validation_results["checks"]["docker"] = {
                    "status": "not_installed",
                    "error": result.stderr
                }
                validation_results["issues"].append("Docker n'est pas installé")
        except Exception as e:
            validation_results["checks"]["docker"] = {
                "status": "error",
                "error": str(e)
            }
            validation_results["issues"].append(f"Erreur vérification Docker: {e}")
        
        # Vérifier Docker Compose
        try:
            result = subprocess.run(['docker-compose', '--version'], capture_output=True, text=True)
            if result.returncode == 0:
                validation_results["checks"]["docker_compose"] = {
                    "status": "installed",
                    "version": result.stdout.strip()
                }
            else:
                validation_results["checks"]["docker_compose"] = {
                    "status": "not_installed",
                    "error": result.stderr
                }
                validation_results["issues"].append("Docker Compose n'est pas installé")
        except Exception as e:
            validation_results["checks"]["docker_compose"] = {
                "status": "error",
                "error": str(e)
            }
            validation_results["issues"].append(f"Erreur vérification Docker Compose: {e}")
        
        # Vérifier les fichiers de configuration
        for container_name, container_config in self.config["containers"].items():
            compose_file = Path(container_config["docker_compose_file"])
            if not compose_file.exists():
                validation_results["issues"].append(f"Fichier docker-compose manquant: {compose_file}")
        
        return validation_results
    
    def show_config(self):
        """Affiche la configuration actuelle"""
        print("🐳 CONFIGURATION DOCKER QWEN MANAGER")
        print("=" * 50)
        print(json.dumps(self.config, indent=2))
        print("=" * 50)

def main():
    """Fonction principale du gestionnaire Docker"""
    parser = argparse.ArgumentParser(
        description='Gestionnaire Docker pour ComfyUI Qwen - Script consolidé paramétrique',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Démarrer un conteneur
  python docker-qwen-manager.py start --container comfyui-qwen
  
  # Arrêter un conteneur
  python docker-qwen-manager.py stop --container comfyui-qwen
  
  # Redémarrer un conteneur
  python docker-qwen-manager.py restart --container comfyui-qwen
  
  # Vérifier le statut d'un conteneur
  python docker-qwen-manager.py status --container comfyui-qwen
  
  # Vérifier la santé d'un conteneur
  python docker-qwen-manager.py health --container comfyui-qwen
  
  # Monitorer les ressources d'un conteneur
  python docker-qwen-manager.py monitor --container comfyui-qwen --duration 300
  
  # Valider la configuration Docker complète
  python docker-qwen-manager.py validate-setup
  
  # Afficher la configuration actuelle
  python docker-qwen-manager.py show-config
        """
    )
    
    parser.add_argument(
        '--config',
        help='Chemin vers le fichier de configuration (défaut: docker_qwen_config.json)'
    )
    
    subparsers = parser.add_subparsers(dest='action', help='Action à exécuter')
    
    # Sous-commande start
    start_parser = subparsers.add_parser('start', help='Démarrer un conteneur')
    start_parser.add_argument('--container', required=True, help='Nom du conteneur à démarrer')
    
    # Sous-commande stop
    stop_parser = subparsers.add_parser('stop', help='Arrêter un conteneur')
    stop_parser.add_argument('--container', required=True, help='Nom du conteneur à arrêter')
    
    # Sous-commande restart
    restart_parser = subparsers.add_parser('restart', help='Redémarrer un conteneur')
    restart_parser.add_argument('--container', required=True, help='Nom du conteneur à redémarrer')
    
    # Sous-commande status
    status_parser = subparsers.add_parser('status', help='Vérifier le statut d\'un conteneur')
    status_parser.add_argument('--container', required=True, help='Nom du conteneur à vérifier')
    
    # Sous-commande health
    health_parser = subparsers.add_parser('health', help='Vérifier la santé d\'un conteneur')
    health_parser.add_argument('--container', required=True, help='Nom du conteneur à vérifier')
    
    # Sous-commande monitor
    monitor_parser = subparsers.add_parser('monitor', help='Monitorer les ressources d\'un conteneur')
    monitor_parser.add_argument('--container', required=True, help='Nom du conteneur à monitorer')
    monitor_parser.add_argument('--duration', type=int, default=60, help='Durée du monitoring en secondes (défaut: 60)')
    
    # Sous-commande validate-setup
    subparsers.add_parser('validate-setup', help='Valider la configuration Docker complète')
    
    # Sous-commande show-config
    subparsers.add_parser('show-config', help='Afficher la configuration actuelle')
    
    args = parser.parse_args()
    
    # Initialiser le gestionnaire
    manager = DockerQwenManager(args.config)
    
    # Exécuter l'action appropriée
    if args.action == 'start':
        success = manager.start_container(args.container)
        sys.exit(0 if success else 1)
    
    elif args.action == 'stop':
        success = manager.stop_container(args.container)
        sys.exit(0 if success else 1)
    
    elif args.action == 'restart':
        success = manager.restart_container(args.container)
        sys.exit(0 if success else 1)
    
    elif args.action == 'status':
        status = manager.get_container_status(args.container)
        print("\n📊 STATUT DU CONTENEUR:")
        print(json.dumps(status, indent=2))
        sys.exit(0 if "error" not in status else 1)
    
    elif args.action == 'health':
        health = manager.check_container_health(args.container)
        print("\n🏥 SANTÉ DU CONTENEUR:")
        print(json.dumps(health, indent=2))
        sys.exit(0 if "error" not in health else 1)
    
    elif args.action == 'monitor':
        monitoring = manager.monitor_resources(args.container, args.duration)
        print("\n📈 RÉSULTATS DU MONITORING:")
        print(json.dumps(monitoring, indent=2))
        sys.exit(0 if "error" not in monitoring else 1)
    
    elif args.action == 'validate-setup':
        validation = manager.validate_docker_setup()
        print("\n🔍 RÉSULTATS DE LA VALIDATION:")
        print(json.dumps(validation, indent=2))
        sys.exit(0 if not validation["issues"] else 1)
    
    elif args.action == 'show-config':
        manager.show_config()
        sys.exit(0)
    
    else:
        parser.print_help()
        sys.exit(1)

if __name__ == "__main__":
    main()