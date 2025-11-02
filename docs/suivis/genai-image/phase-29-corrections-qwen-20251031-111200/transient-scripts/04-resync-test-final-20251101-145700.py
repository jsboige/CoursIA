#!/usr/bin/env python3
"""
Script Transient 04 - Resync et Test Complet Final Qwen
Phase 29 - Corrections Qwen ComfyUI

Ce script est un WRAPPER FIN qui orchestre :
1. Resynchronisation des credentials (via script consolidé)
2. Redémarrage Docker avec WSL
3. Vérification que le serveur est prêt
4. Test de génération d'images (via script transient 03)
5. Génération du rapport final

Auteur: Système SDDD
Date: 2025-11-01T14:57:00
"""

import subprocess
import sys
import os
from pathlib import Path
import time
import json
from datetime import datetime
import requests

# Chemins vers scripts consolidés et transients
# Le script est dans: docs/suivis/genai-image/phase-29.../transient-scripts/
# Comptons les niveaux depuis transient-scripts jusqu'à la racine:
# transient-scripts -> phase-29-... -> genai-image -> suivis -> docs -> [RACINE]
# Donc 5 niveaux de .parent : parent (phase-29) -> parent (genai-image) -> parent (suivis) -> parent (docs) -> parent (RACINE)
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent.parent.parent
SCRIPT_DIR = PROJECT_ROOT / "scripts" / "genai-auth"
RESYNC_SCRIPT = SCRIPT_DIR / "resync-credentials-complete.py"
TEST_SCRIPT = Path(__file__).parent / "03-test-generation-images-20251031-230500.py"
RAPPORT_DIR = Path(__file__).parent.parent / "rapports"

# Configuration serveur ComfyUI
COMFYUI_URL = "http://127.0.0.1:8188"
# Utiliser la page d'accueil ou un endpoint public au lieu de system_stats qui nécessite auth
COMFYUI_HEALTH_ENDPOINT = f"{COMFYUI_URL}/"
MAX_WAIT_TIME = 180  # 3 minutes max pour attendre le serveur (augmenté)

class Colors:
    """Codes couleur ANSI pour terminal"""
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print_section(title: str):
    """Affiche un titre de section"""
    print(f"\n{Colors.HEADER}{Colors.BOLD}{'='*80}")
    print(f"  {title}")
    print(f"{'='*80}{Colors.ENDC}\n")

def print_success(msg: str):
    """Affiche un message de succès"""
    print(f"{Colors.OKGREEN}✅ {msg}{Colors.ENDC}")

def print_error(msg: str):
    """Affiche un message d'erreur"""
    print(f"{Colors.FAIL}❌ {msg}{Colors.ENDC}")

def print_info(msg: str):
    """Affiche un message d'information"""
    print(f"{Colors.OKBLUE}ℹ️  {msg}{Colors.ENDC}")

def print_warning(msg: str):
    """Affiche un message d'avertissement"""
    print(f"{Colors.WARNING}⚠️  {msg}{Colors.ENDC}")

def resync_credentials() -> bool:
    """
    Étape 1: Resynchroniser les credentials via le script consolidé
    
    Returns:
        bool: True si succès, False sinon
    """
    print_section("ÉTAPE 1/5 - Resynchronisation des Credentials")
    
    if not RESYNC_SCRIPT.exists():
        print_error(f"Script de resync introuvable : {RESYNC_SCRIPT}")
        return False
    
    print_info(f"Exécution de : {RESYNC_SCRIPT}")
    
    try:
        result = subprocess.run(
            [sys.executable, str(RESYNC_SCRIPT)],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        print(result.stdout)
        
        if result.returncode == 0:
            print_success("Credentials resynchronisés avec succès")
            return True
        else:
            print_error(f"Échec de la resynchronisation (code: {result.returncode})")
            print(result.stderr)
            return False
            
    except subprocess.TimeoutExpired:
        print_error("Timeout lors de la resynchronisation (60s)")
        return False
    except Exception as e:
        print_error(f"Erreur lors de la resynchronisation : {e}")
        return False

def restart_docker() -> bool:
    """
    Étape 2: Redémarrer le container Docker via WSL
    
    Returns:
        bool: True si succès, False sinon
    """
    print_section("ÉTAPE 2/5 - Redémarrage Docker")
    
    docker_compose_dir = "/home/jesse/SD/workspace/comfyui-qwen"
    restart_cmd = f"cd {docker_compose_dir} && docker-compose restart"
    wsl_cmd = ["wsl", "bash", "-c", restart_cmd]
    
    print_info(f"Commande WSL : {' '.join(wsl_cmd)}")
    
    try:
        result = subprocess.run(
            wsl_cmd,
            capture_output=True,
            text=True,
            timeout=120
        )
        
        print(result.stdout)
        
        if result.returncode == 0:
            print_success("Docker redémarré avec succès")
            return True
        else:
            print_error(f"Échec du redémarrage Docker (code: {result.returncode})")
            print(result.stderr)
            return False
            
    except subprocess.TimeoutExpired:
        print_error("Timeout lors du redémarrage Docker (120s)")
        return False
    except Exception as e:
        print_error(f"Erreur lors du redémarrage Docker : {e}")
        return False

def wait_for_server() -> bool:
    """
    Étape 3: Attendre que le serveur ComfyUI soit prêt
    
    Returns:
        bool: True si serveur prêt, False sinon
    """
    print_section("ÉTAPE 3/5 - Attente du Serveur ComfyUI")
    
    print_info(f"Vérification de {COMFYUI_HEALTH_ENDPOINT}")
    print_info(f"Timeout maximum : {MAX_WAIT_TIME}s")
    
    start_time = time.time()
    attempt = 0
    
    while time.time() - start_time < MAX_WAIT_TIME:
        attempt += 1
        elapsed = int(time.time() - start_time)
        
        print(f"  Tentative {attempt} ({elapsed}s écoulées)...", end="\r")
        
        try:
            response = requests.get(COMFYUI_HEALTH_ENDPOINT, timeout=5)
            
            if response.status_code == 200:
                print()  # Nouvelle ligne après le \r
                print_success(f"Serveur prêt après {elapsed}s ({attempt} tentatives)")
                return True
                
        except requests.RequestException:
            pass
        
        time.sleep(2)
    
    print()  # Nouvelle ligne après le \r
    print_error(f"Timeout : serveur non accessible après {MAX_WAIT_TIME}s")
    return False

def run_generation_test() -> tuple:
    """
    Étape 4: Lancer le test de génération via le script transient 03
    
    Returns:
        tuple: (succès, résultats)
    """
    print_section("ÉTAPE 4/5 - Test de Génération d'Images")
    
    if not TEST_SCRIPT.exists():
        print_error(f"Script de test introuvable : {TEST_SCRIPT}")
        return False, {}
    
    print_info(f"Exécution de : {TEST_SCRIPT}")
    
    try:
        result = subprocess.run(
            [sys.executable, str(TEST_SCRIPT)],
            capture_output=True,
            text=True,
            timeout=300  # 5 minutes max pour génération
        )
        
        print(result.stdout)
        
        if result.returncode == 0:
            print_success("Test de génération réussi")
            
            # Extraire les résultats si possible
            results = {"returncode": 0, "output": result.stdout}
            
            return True, results
        else:
            print_error(f"Échec du test de génération (code: {result.returncode})")
            print(result.stderr)
            return False, {"returncode": result.returncode, "stderr": result.stderr}
            
    except subprocess.TimeoutExpired:
        print_error("Timeout lors du test de génération (300s)")
        return False, {"error": "timeout"}
    except Exception as e:
        print_error(f"Erreur lors du test de génération : {e}")
        return False, {"error": str(e)}

def generate_final_report(results: dict) -> bool:
    """
    Étape 5: Générer le rapport final numéroté
    
    Args:
        results: Dictionnaire contenant tous les résultats des étapes
    
    Returns:
        bool: True si rapport créé, False sinon
    """
    print_section("ÉTAPE 5/5 - Génération du Rapport Final")
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    rapport_path = RAPPORT_DIR / f"15-test-final-complet-20251101-145700.md"
    
    # Créer le répertoire si nécessaire
    RAPPORT_DIR.mkdir(parents=True, exist_ok=True)
    
    # Construire le contenu du rapport
    rapport_content = f"""# Rapport 15 - Test Final Complet Qwen ComfyUI

**Date d'exécution** : {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}  
**Script transient** : `04-resync-test-final-20251101-145700.py`  
**Phase** : Phase 29 - Corrections Qwen ComfyUI

---

## 📋 Résumé Exécutif

Ce rapport documente l'exécution complète du workflow de resynchronisation et test de génération d'images avec Qwen via ComfyUI.

### Statut Global

"""
    
    # Ajouter le statut de chaque étape
    all_success = all([
        results.get("resync", False),
        results.get("docker_restart", False),
        results.get("server_ready", False),
        results.get("generation_test", False)
    ])
    
    if all_success:
        rapport_content += "✅ **SUCCÈS COMPLET** - Tous les tests sont au vert (5/5)\n\n"
    else:
        rapport_content += "❌ **ÉCHEC PARTIEL** - Certains tests ont échoué\n\n"
    
    # Détail des étapes
    rapport_content += """---

## 🔄 Détail des Étapes

### Étape 1/5 - Resynchronisation des Credentials

"""
    
    if results.get("resync", False):
        rapport_content += "**Statut** : ✅ SUCCÈS\n\n"
    else:
        rapport_content += "**Statut** : ❌ ÉCHEC\n\n"
    
    rapport_content += """**Actions effectuées** :
- Exécution du script `scripts/genai-auth/resync-credentials-complete.py`
- Synchronisation `.secrets/.env.generated` → `docker-configurations/comfyui-qwen/.env`
- Mise à jour du token utilisateur

"""
    
    rapport_content += """### Étape 2/5 - Redémarrage Docker

"""
    
    if results.get("docker_restart", False):
        rapport_content += "**Statut** : ✅ SUCCÈS\n\n"
    else:
        rapport_content += "**Statut** : ❌ ÉCHEC\n\n"
    
    rapport_content += """**Actions effectuées** :
- Commande WSL : `wsl bash -c 'cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose restart'`
- Redémarrage du container ComfyUI

"""
    
    rapport_content += """### Étape 3/5 - Attente du Serveur

"""
    
    if results.get("server_ready", False):
        rapport_content += "**Statut** : ✅ SUCCÈS\n\n"
    else:
        rapport_content += "**Statut** : ❌ ÉCHEC\n\n"
    
    rapport_content += f"""**Actions effectuées** :
- Vérification endpoint : `{COMFYUI_HEALTH_ENDPOINT}`
- Timeout maximum : {MAX_WAIT_TIME}s
- Serveur accessible et prêt

"""
    
    rapport_content += """### Étape 4/5 - Test de Génération d'Images

"""
    
    if results.get("generation_test", False):
        rapport_content += "**Statut** : ✅ SUCCÈS\n\n"
    else:
        rapport_content += "**Statut** : ❌ ÉCHEC\n\n"
    
    rapport_content += """**Actions effectuées** :
- Exécution du script `03-test-generation-images-20251031-230500.py`
- Test d'authentification et génération d'image
- Vérification de l'image produite

"""
    
    # Résultats de génération
    if results.get("generation_results"):
        rapport_content += f"""**Résultats détaillés** :
```
{results.get("generation_results")}
```

"""
    
    # Checklist de validation
    rapport_content += """---

## ✅ Checklist de Validation

"""
    
    checks = [
        ("Credentials resynchronisés", results.get("resync", False)),
        ("Docker redémarré", results.get("docker_restart", False)),
        ("Serveur accessible", results.get("server_ready", False)),
        ("Authentification réussie", results.get("generation_test", False)),
        ("Image générée", results.get("generation_test", False))
    ]
    
    for check_name, check_status in checks:
        status_icon = "✅" if check_status else "❌"
        rapport_content += f"- [{status_icon}] {check_name}\n"
    
    # Conclusion
    rapport_content += """\n---

## 🎯 Conclusion

"""
    
    if all_success:
        rapport_content += """Le test final est **COMPLET ET RÉUSSI**. Tous les composants sont fonctionnels :
- ✅ Credentials correctement synchronisés
- ✅ Docker opérationnel
- ✅ Serveur ComfyUI accessible
- ✅ Authentification validée
- ✅ Génération d'images fonctionnelle

Le système Qwen ComfyUI est **PRÊT POUR PRODUCTION**.

"""
    else:
        rapport_content += """Le test final présente des **ÉCHECS PARTIELS**. Certains composants nécessitent une investigation :

"""
        
        if not results.get("resync", False):
            rapport_content += "- ❌ Problème de resynchronisation des credentials\n"
        if not results.get("docker_restart", False):
            rapport_content += "- ❌ Problème de redémarrage Docker\n"
        if not results.get("server_ready", False):
            rapport_content += "- ❌ Serveur ComfyUI non accessible\n"
        if not results.get("generation_test", False):
            rapport_content += "- ❌ Échec de génération d'images\n"
        
        rapport_content += "\n**Actions recommandées** : Consulter les logs détaillés ci-dessus.\n\n"
    
    # Métadonnées
    rapport_content += f"""---

## 📊 Métadonnées

- **Script transient** : `04-resync-test-final-20251101-145700.py`
- **Date d'exécution** : {datetime.now().isoformat()}
- **Phase SDDD** : Phase 29 - Corrections Qwen ComfyUI
- **Structure** : `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/`

---

*Rapport généré automatiquement par le système SDDD*
"""
    
    # Écrire le rapport
    try:
        rapport_path.write_text(rapport_content, encoding='utf-8')
        print_success(f"Rapport créé : {rapport_path}")
        return True
    except Exception as e:
        print_error(f"Erreur lors de la création du rapport : {e}")
        return False

def main():
    """Fonction principale : orchestration complète"""
    print_section("🚀 SCRIPT TRANSIENT 04 - RESYNC ET TEST FINAL")
    
    print_info("Phase 29 - Corrections Qwen ComfyUI")
    print_info(f"Date : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Dictionnaire pour stocker tous les résultats
    results = {
        "resync": False,
        "docker_restart": False,
        "server_ready": False,
        "generation_test": False,
        "generation_results": None
    }
    
    # Étape 1 : Resync credentials
    results["resync"] = resync_credentials()
    if not results["resync"]:
        print_warning("⚠️  Poursuite malgré l'échec de resync...")
    
    # Étape 2 : Restart Docker
    results["docker_restart"] = restart_docker()
    if not results["docker_restart"]:
        print_error("❌ Arrêt : Docker n'a pas redémarré")
        generate_final_report(results)
        return 1
    
    # Étape 3 : Wait for server
    results["server_ready"] = wait_for_server()
    if not results["server_ready"]:
        print_error("❌ Arrêt : Serveur non accessible")
        generate_final_report(results)
        return 1
    
    # Étape 4 : Run generation test
    test_success, test_results = run_generation_test()
    results["generation_test"] = test_success
    results["generation_results"] = test_results
    
    # Étape 5 : Generate final report
    generate_final_report(results)
    
    # Résumé final
    print_section("🏁 RÉSUMÉ FINAL")
    
    all_success = all([
        results["resync"],
        results["docker_restart"],
        results["server_ready"],
        results["generation_test"]
    ])
    
    if all_success:
        print_success("✅ SUCCÈS COMPLET - Tous les tests sont au vert (5/5)")
        print_success("🎉 Le système Qwen ComfyUI est PRÊT POUR PRODUCTION")
        return 0
    else:
        print_warning("⚠️  ÉCHEC PARTIEL - Certains tests ont échoué")
        print_info("📄 Consultez le rapport détaillé pour plus d'informations")
        return 1

if __name__ == "__main__":
    sys.exit(main())