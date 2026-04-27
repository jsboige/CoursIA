#!/usr/bin/env python3
"""
Script de test simple pour valider le démarrage du container ComfyUI-Qwen
"""
import subprocess
import sys
import time

def main():
    print("🔍 Test de démarrage du container ComfyUI-Qwen...")
    
    try:
        # Démarrer le container
        print("📋 Lancement docker-compose...")
        result = subprocess.run(
            ["docker-compose", "up", "-d"],
            cwd="docker-configurations/services/comfyui-qwen",
            capture_output=True,
            text=True,
            timeout=60
        )
        
        print(f"📋 Sortie docker-compose: {result.returncode}")
        if result.stdout:
            print(f"📋 STDOUT:\n{result.stdout}")
        if result.stderr:
            print(f"📋 STDERR:\n{result.stderr}")
        
        if result.returncode == 0:
            print("✅ Container démarré avec succès")
            
            # Attendre un peu pour le démarrage
            print("⏳ Attente du démarrage de ComfyUI...")
            time.sleep(10)
            
            # Vérifier que le container est en cours d'exécution
            result = subprocess.run(
                ["docker", "ps", "--filter", "name=comfyui-qwen", "--format", "{{.Names}} {{.Status}}"],
                capture_output=True,
                text=True
            )
            
            if "comfyui-qwen" in result.stdout and "Up" in result.stdout:
                print("✅ Container comfyui-qwen est bien démarré (Up)")
                
                # Vérifier les logs récents
                print("📋 Vérification des logs récents...")
                logs_result = subprocess.run(
                    ["docker", "logs", "--tail", "20", "comfyui-qwen"],
                    capture_output=True,
                    text=True
                )
                
                if logs_result.returncode == 0:
                    print("✅ Logs du container accessibles")
                    print("📋 Dernières lignes de logs:")
                    for line in logs_result.stdout.split('\n')[-5:]:
                        print(f"   {line}")
                else:
                    print("❌ Impossible d'accéder aux logs du container")
                
                return True
            else:
                print("❌ Container comfyui-qwen n'est pas en état 'Up'")
                print(f"📋 État du container: {result.stdout}")
                return False
                
        else:
            print(f"❌ Échec du démarrage du container (code: {result.returncode})")
            if result.stderr:
                print(f"❌ Erreur: {result.stderr}")
            return False
            
    except subprocess.TimeoutExpired:
        print("❌ Timeout lors du démarrage du container (>60s)")
        return False
    except Exception as e:
        print(f"❌ Exception lors du test: {e}")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)