#!/usr/bin/env python3
"""
Script Transient 14 - Test Final Complet Génération Images Qwen
Phase 29 - Corrections Qwen ComfyUI

Ce script valide le système complet end-to-end :
1. Authentification avec hash bcrypt ComfyUI-Login
2. Génération d'image via workflow Qwen
3. Validation de la présence de l'image générée

Auteur: Phase 29 - Consolidation Finale
Date: 2025-11-02 00:53:00
Version: 1.0.0
"""

import sys
import os
import json
import time
import requests
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, Optional, Tuple

# Ajouter le chemin des scripts consolidés
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent / "scripts" / "genai-auth"))

class QwenSystemFinalTest:
    """Classe de test final complet du système Qwen ComfyUI"""
    
    def __init__(self):
        self.comfyui_url = "http://localhost:8188"
        self.secrets_file = Path(".secrets/qwen-api-user.token")
        self.bcrypt_hash = self._load_bcrypt_hash()
        self.test_results = {
            "timestamp": datetime.now().isoformat(),
            "tests": {}
        }
        
    def _load_bcrypt_hash(self) -> str:
        """Charge le hash bcrypt depuis .secrets"""
        try:
            if self.secrets_file.exists():
                hash_value = self.secrets_file.read_text(encoding='utf-8').strip()
                print(f"✅ Hash bcrypt chargé: {hash_value[:20]}...")
                return hash_value
            else:
                print(f"❌ Fichier .secrets non trouvé: {self.secrets_file}")
                sys.exit(1)
        except Exception as e:
            print(f"❌ Erreur chargement hash: {e}")
            sys.exit(1)
    
    def test_docker_container(self) -> Tuple[bool, Dict[str, Any]]:
        """Test 1: Vérifier que le container Docker est actif"""
        print("\n" + "="*60)
        print("TEST 1: VÉRIFICATION CONTAINER DOCKER")
        print("="*60)
        
        result = {
            "test_name": "docker_container",
            "status": "UNKNOWN",
            "details": {}
        }
        
        try:
            cmd = ["docker", "ps", "--filter", "name=comfyui-qwen", "--format", "{{.Status}}"]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
            
            if proc.returncode == 0 and "Up" in proc.stdout:
                result["status"] = "SUCCESS"
                result["details"]["container_status"] = proc.stdout.strip()
                print(f"✅ Container actif: {proc.stdout.strip()}")
                return True, result
            else:
                result["status"] = "FAILURE"
                result["details"]["error"] = "Container non actif"
                print(f"❌ Container non actif")
                return False, result
                
        except Exception as e:
            result["status"] = "ERROR"
            result["details"]["error"] = str(e)
            print(f"❌ Erreur vérification Docker: {e}")
            return False, result
    
    def test_authentication(self) -> Tuple[bool, Dict[str, Any]]:
        """Test 2: Tester l'authentification ComfyUI-Login"""
        print("\n" + "="*60)
        print("TEST 2: AUTHENTIFICATION COMFYUI-LOGIN")
        print("="*60)
        
        result = {
            "test_name": "authentication",
            "status": "UNKNOWN",
            "details": {}
        }
        
        try:
            headers = {
                "Authorization": f"Bearer {self.bcrypt_hash}",
                "Content-Type": "application/json"
            }
            
            response = requests.get(
                f"{self.comfyui_url}/system_stats",
                headers=headers,
                timeout=10
            )
            
            if response.status_code == 200:
                result["status"] = "SUCCESS"
                data = response.json()
                system = data.get("system", {})
                result["details"]["http_status"] = 200
                result["details"]["comfyui_version"] = system.get("comfyui_version", "N/A")
                result["details"]["ram_total_gb"] = round(system.get("ram_total", 0) / (1024**3), 2)
                
                print(f"✅ Authentification réussie (HTTP 200)")
                print(f"   ComfyUI Version: {system.get('comfyui_version', 'N/A')}")
                print(f"   RAM Totale: {result['details']['ram_total_gb']} GB")
                return True, result
            else:
                result["status"] = "FAILURE"
                result["details"]["http_status"] = response.status_code
                result["details"]["response"] = response.text
                print(f"❌ Authentification échouée (HTTP {response.status_code})")
                return False, result
                
        except Exception as e:
            result["status"] = "ERROR"
            result["details"]["error"] = str(e)
            print(f"❌ Erreur test authentification: {e}")
            return False, result
    
    def test_image_generation(self) -> Tuple[bool, Dict[str, Any]]:
        """Test 3: Générer une image avec workflow Qwen minimal"""
        print("\n" + "="*60)
        print("TEST 3: GÉNÉRATION IMAGE WORKFLOW QWEN")
        print("="*60)
        
        result = {
            "test_name": "image_generation",
            "status": "UNKNOWN",
            "details": {}
        }
        
        # Workflow minimal pour test rapide
        workflow = {
            "3": {
                "inputs": {
                    "seed": int(time.time()),
                    "steps": 10,  # Réduit pour test rapide
                    "cfg": 7.0,
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "denoise": 1.0,
                    "model": ["4", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["5", 0]
                },
                "class_type": "KSampler"
            },
            "4": {
                "inputs": {
                    "ckpt_name": "qwen_vl_v1.safetensors"
                },
                "class_type": "CheckpointLoaderSimple"
            },
            "5": {
                "inputs": {
                    "width": 256,  # Réduit pour test rapide
                    "height": 256,
                    "batch_size": 1
                },
                "class_type": "EmptyLatentImage"
            },
            "6": {
                "inputs": {
                    "text": "a simple test image",
                    "clip": ["4", 1]
                },
                "class_type": "CLIPTextEncode"
            },
            "7": {
                "inputs": {
                    "text": "text, watermark, blurry",
                    "clip": ["4", 1]
                },
                "class_type": "CLIPTextEncode"
            },
            "8": {
                "inputs": {
                    "samples": ["3", 0],
                    "vae": ["4", 2]
                },
                "class_type": "VAEDecode"
            },
            "9": {
                "inputs": {
                    "filename_prefix": "Phase29_Final_Test",
                    "images": ["8", 0]
                },
                "class_type": "SaveImage"
            }
        }
        
        try:
            headers = {
                "Authorization": f"Bearer {self.bcrypt_hash}",
                "Content-Type": "application/json"
            }
            
            # Soumettre le workflow
            print("📤 Soumission du workflow...")
            response = requests.post(
                f"{self.comfyui_url}/prompt",
                headers=headers,
                json={"prompt": workflow},
                timeout=30
            )
            
            if response.status_code != 200:
                result["status"] = "FAILURE"
                result["details"]["http_status"] = response.status_code
                result["details"]["response"] = response.text
                print(f"❌ Soumission échouée (HTTP {response.status_code})")
                return False, result
            
            prompt_data = response.json()
            prompt_id = prompt_data.get("prompt_id")
            
            if not prompt_id:
                result["status"] = "FAILURE"
                result["details"]["error"] = "Pas de prompt_id dans la réponse"
                print(f"❌ Pas de prompt_id reçu")
                return False, result
            
            result["details"]["prompt_id"] = prompt_id
            print(f"✅ Workflow soumis - Prompt ID: {prompt_id}")
            
            # Attendre la génération
            print("⏳ Attente de la génération (max 120s)...")
            max_wait = 120
            start_time = time.time()
            
            while time.time() - start_time < max_wait:
                history_response = requests.get(
                    f"{self.comfyui_url}/history/{prompt_id}",
                    headers=headers,
                    timeout=10
                )
                
                if history_response.status_code == 200:
                    history = history_response.json()
                    
                    if prompt_id in history:
                        prompt_info = history[prompt_id]
                        
                        if "outputs" in prompt_info:
                            result["status"] = "SUCCESS"
                            result["details"]["execution_time"] = round(time.time() - start_time, 2)
                            
                            # Extraire les images générées
                            outputs = prompt_info["outputs"]
                            images = []
                            for node_id, node_output in outputs.items():
                                if "images" in node_output:
                                    for img in node_output["images"]:
                                        images.append({
                                            "filename": img.get("filename", "unknown"),
                                            "subfolder": img.get("subfolder", ""),
                                            "type": img.get("type", "output")
                                        })
                            
                            result["details"]["images_count"] = len(images)
                            result["details"]["images"] = images
                            
                            print(f"✅ Génération terminée en {result['details']['execution_time']}s")
                            print(f"📸 {len(images)} image(s) générée(s):")
                            for img in images:
                                print(f"   • {img['filename']}")
                            
                            return True, result
                
                time.sleep(2)
                print(".", end="", flush=True)
            
            print()
            result["status"] = "TIMEOUT"
            result["details"]["error"] = f"Timeout après {max_wait}s"
            print(f"⏱️ Timeout - Génération n'a pas terminé en {max_wait}s")
            return False, result
            
        except Exception as e:
            result["status"] = "ERROR"
            result["details"]["error"] = str(e)
            print(f"❌ Erreur génération image: {e}")
            import traceback
            traceback.print_exc()
            return False, result
    
    def run_all_tests(self) -> Dict[str, Any]:
        """Exécute tous les tests séquentiellement"""
        print("\n" + "="*60)
        print("SCRIPT TRANSIENT 14 - TEST FINAL PHASE 29")
        print("Test Complet Système Qwen ComfyUI avec Authentification")
        print("="*60)
        print(f"Timestamp: {self.test_results['timestamp']}")
        print(f"URL ComfyUI: {self.comfyui_url}")
        print(f"Hash bcrypt: {self.bcrypt_hash[:20]}...")
        
        # Test 1: Docker container
        success_1, result_1 = self.test_docker_container()
        self.test_results["tests"]["docker_container"] = result_1
        
        if not success_1:
            print("\n⚠️ Arrêt des tests - Container Docker non actif")
            return self.test_results
        
        # Test 2: Authentification
        success_2, result_2 = self.test_authentication()
        self.test_results["tests"]["authentication"] = result_2
        
        if not success_2:
            print("\n⚠️ Arrêt des tests - Authentification échouée")
            return self.test_results
        
        # Test 3: Génération image
        success_3, result_3 = self.test_image_generation()
        self.test_results["tests"]["image_generation"] = result_3
        
        # Résumé final
        print("\n" + "="*60)
        print("RÉSUMÉ FINAL DES TESTS")
        print("="*60)
        
        all_success = success_1 and success_2 and success_3
        
        print(f"\n1️⃣ Container Docker: {'✅ SUCCESS' if success_1 else '❌ FAILURE'}")
        print(f"2️⃣ Authentification: {'✅ SUCCESS' if success_2 else '❌ FAILURE'}")
        print(f"3️⃣ Génération Image: {'✅ SUCCESS' if success_3 else '❌ FAILURE'}")
        
        if all_success:
            print("\n🎉 TOUS LES TESTS RÉUSSIS - Système opérationnel!")
            self.test_results["overall_status"] = "SUCCESS"
        else:
            print("\n⚠️ CERTAINS TESTS ONT ÉCHOUÉ - Voir détails ci-dessus")
            self.test_results["overall_status"] = "FAILURE"
        
        return self.test_results
    
    def save_results(self, output_file: Optional[Path] = None):
        """Sauvegarde les résultats dans un fichier JSON"""
        if output_file is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_file = Path(__file__).parent / "rapports" / f"test-final-phase29-{timestamp}.json"
        
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(self.test_results, f, indent=2, ensure_ascii=False)
        
        print(f"\n💾 Résultats sauvegardés: {output_file}")

def main():
    """Point d'entrée principal"""
    tester = QwenSystemFinalTest()
    
    # Exécuter tous les tests
    results = tester.run_all_tests()
    
    # Sauvegarder les résultats
    tester.save_results()
    
    # Code de sortie
    return 0 if results["overall_status"] == "SUCCESS" else 1

if __name__ == "__main__":
    sys.exit(main())