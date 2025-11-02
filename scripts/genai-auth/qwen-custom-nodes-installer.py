#!/usr/bin/env python3
"""
Script consolidé d'installation des custom nodes Qwen pour ComfyUI.
Partie de la Phase 29 - Corrections Qwen ComfyUI.

Ce script :
1. Installe/Réinstalle ComfyUI-QwenImageWanBridge
2. Vérifie/Installe ComfyUI-Login
3. Synchronise les credentials Windows → WSL
4. Redémarre le container Docker
5. Vérifie que les 28 custom nodes Qwen sont chargés
6. Génère un rapport SDDD numéroté 22

USAGE:
    python scripts/genai-auth/qwen-custom-nodes-installer.py
"""

import os
import sys
import subprocess
import json
import time
import requests
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional

# Configuration globale
PROJECT_ROOT = Path("d:/Dev/CoursIA")
COMFYUI_URL = "http://localhost:8188"
COMFYUI_WSL_PATH = "/home/jesse/SD/workspace/comfyui-qwen"
CUSTOM_NODES_WSL_PATH = f"{COMFYUI_WSL_PATH}/ComfyUI/custom_nodes"
QWEN_REPO_URL = "https://github.com/gokayfem/ComfyUI-QwenImageWanBridge"
COMFYUI_LOGIN_REPO_URL = "https://github.com/liusida/ComfyUI-Login"

# Liste des 28 custom nodes attendus (Phase 12C)
EXPECTED_QWEN_NODES = [
    # Core Loaders (4)
    "QwenVLCLIPLoader", "QwenDiTLoader", "QwenTransformerLoader", "QwenVAELoader",
    # Samplers (4)
    "QwenImageSamplerNode", "QwenImageSamplerWithEdit", "QwenImageSamplerBatch", "QwenImageCascadeSampler",
    # Encoders/Decoders (4)
    "TextEncodeQwenImageEdit", "QwenVLEmptyLatent", "QwenVLImageToLatent", "QwenImageEncoderNode",
    # ControlNet (3)
    "QwenImageControlnetLoader", "QwenImageControlnetApply", "QwenImageDiffsynthControlnet",
    # Advanced Edit (4)
    "QwenImageInpaintNode", "QwenImageOutpaintNode", "QwenImageMaskNode", "QwenEntityControlNode",
    # Templates (2)
    "QwenTemplateBuilder", "QwenTemplateConnector",
    # Tokens/Analyse (3)
    "QwenTokenDebugger", "QwenTokenAnalyzer", "QwenSpatialTokenGenerator",
    # Processing (3)
    "QwenProcessorWrapper", "QwenProcessedToEmbedding", "QwenImageEncodeWrapper",
    # Utilitaires (2)
    "QwenLowresFixNode", "ModelMergeQwenImage",
    # Gestion (1)
    "QwenModelManagerWrapper"
]


class QwenCustomNodesInstaller:
    """Gestionnaire d'installation des custom nodes Qwen pour ComfyUI."""
    
    def __init__(self):
        self.project_root = PROJECT_ROOT
        self.timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        self.results = {
            'timestamp_start': datetime.now().isoformat(),
            'steps': [],
            'custom_nodes_before': 0,
            'custom_nodes_after': 0,
            'success': False
        }
    
    def log_step(self, step_name: str, status: str, details: str = ""):
        """Enregistre une étape d'exécution."""
        step_info = {
            'name': step_name,
            'status': status,
            'details': details,
            'timestamp': datetime.now().isoformat()
        }
        self.results['steps'].append(step_info)
        
        icon = "✅" if status == "SUCCESS" else "❌" if status == "ERROR" else "⏳"
        print(f"\n{icon} {step_name}")
        if details:
            print(f"   {details}")
    
    def execute_wsl_command(self, cmd: str, check: bool = True) -> Dict[str, Any]:
        """Exécute une commande WSL et retourne le résultat."""
        try:
            result = subprocess.run(
                ["wsl", "bash", "-c", cmd],
                capture_output=True,
                text=True,
                check=check,
                encoding='utf-8'
            )
            return {
                'success': True,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'returncode': result.returncode
            }
        except subprocess.CalledProcessError as e:
            return {
                'success': False,
                'stdout': e.stdout,
                'stderr': e.stderr,
                'returncode': e.returncode,
                'error': str(e)
            }
        except Exception as e:
            return {
                'success': False,
                'error': str(e)
            }
    
    def remove_existing_qwen_nodes(self) -> bool:
        """Supprime installation existante de ComfyUI-QwenImageWanBridge."""
        self.log_step("Suppression installation existante", "IN_PROGRESS")
        
        cmd = f"cd {CUSTOM_NODES_WSL_PATH} && rm -rf ComfyUI-QwenImageWanBridge"
        result = self.execute_wsl_command(cmd, check=False)
        
        if result['success'] or result['returncode'] == 0:
            self.log_step("Suppression installation existante", "SUCCESS", 
                         "Ancien répertoire supprimé (ou n'existait pas)")
            return True
        else:
            self.log_step("Suppression installation existante", "ERROR", 
                         f"Erreur: {result.get('stderr', result.get('error', 'Unknown'))}")
            return False
    
    def install_qwen_custom_nodes(self) -> bool:
        """Clone et installe ComfyUI-QwenImageWanBridge."""
        self.log_step("Installation ComfyUI-QwenImageWanBridge", "IN_PROGRESS")
        
        # Clone repository
        clone_cmd = f"cd {CUSTOM_NODES_WSL_PATH} && git clone {QWEN_REPO_URL}"
        result = self.execute_wsl_command(clone_cmd, check=False)
        
        if not result['success']:
            self.log_step("Installation ComfyUI-QwenImageWanBridge", "ERROR", 
                         f"Échec clone: {result.get('stderr', result.get('error'))}")
            return False
        
        # Installer dépendances
        install_cmd = f"cd {CUSTOM_NODES_WSL_PATH}/ComfyUI-QwenImageWanBridge && pip install -r requirements.txt"
        result = self.execute_wsl_command(install_cmd, check=False)
        
        if result['success'] or result['returncode'] == 0:
            self.log_step("Installation ComfyUI-QwenImageWanBridge", "SUCCESS", 
                         "Repository cloné et dépendances installées")
            return True
        else:
            self.log_step("Installation ComfyUI-QwenImageWanBridge", "ERROR", 
                         f"Échec installation dépendances: {result.get('stderr')}")
            return False
    
    def verify_comfyui_login(self) -> bool:
        """Vérifie et installe ComfyUI-Login si nécessaire."""
        self.log_step("Vérification ComfyUI-Login", "IN_PROGRESS")
        
        # Vérifier si déjà installé
        check_cmd = f"test -d {CUSTOM_NODES_WSL_PATH}/ComfyUI-Login && echo 'exists' || echo 'missing'"
        result = self.execute_wsl_command(check_cmd, check=False)
        
        if result['success'] and 'exists' in result['stdout']:
            self.log_step("Vérification ComfyUI-Login", "SUCCESS", 
                         "ComfyUI-Login déjà installé")
            return True
        
        # Installer si absent
        clone_cmd = f"cd {CUSTOM_NODES_WSL_PATH} && git clone {COMFYUI_LOGIN_REPO_URL}"
        result = self.execute_wsl_command(clone_cmd, check=False)
        
        if not result['success']:
            self.log_step("Vérification ComfyUI-Login", "ERROR", 
                         f"Échec clone: {result.get('stderr')}")
            return False
        
        # Installer dépendances
        install_cmd = f"cd {CUSTOM_NODES_WSL_PATH}/ComfyUI-Login && pip install -r requirements.txt"
        result = self.execute_wsl_command(install_cmd, check=False)
        
        if result['success'] or result['returncode'] == 0:
            self.log_step("Vérification ComfyUI-Login", "SUCCESS", 
                         "ComfyUI-Login installé avec succès")
            return True
        else:
            self.log_step("Vérification ComfyUI-Login", "ERROR", 
                         f"Échec installation dépendances: {result.get('stderr')}")
            return False
    
    def sync_credentials(self) -> bool:
        """Synchronise credentials Windows → WSL (réutilise logique resync-credentials-complete.py)."""
        self.log_step("Synchronisation credentials", "IN_PROGRESS")
        
        try:
            # Lire token depuis .secrets/.env.generated
            env_file = self.project_root / ".secrets/.env.generated"
            if not env_file.exists():
                self.log_step("Synchronisation credentials", "ERROR", 
                             f"Fichier credentials Windows introuvable: {env_file}")
                return False
            
            content = env_file.read_text(encoding='utf-8')
            token_raw = None
            for line in content.split('\n'):
                if line.startswith('QWEN_API_USER_TOKEN='):
                    token_raw = line.split('=', 1)[1].strip()
                    break
            
            if not token_raw:
                self.log_step("Synchronisation credentials", "ERROR", 
                             "Token QWEN_API_USER_TOKEN introuvable dans .env.generated")
                return False
            
            # Lire hash bcrypt depuis .secrets/qwen-api-user.token
            token_file = self.project_root / ".secrets/qwen-api-user.token"
            if not token_file.exists():
                self.log_step("Synchronisation credentials", "ERROR", 
                             f"Fichier hash bcrypt Windows introuvable: {token_file}")
                return False
            
            token_hash = token_file.read_text(encoding='utf-8').strip()
            
            # Synchroniser vers WSL
            wsl_token_path = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token"
            
            # Créer répertoire si nécessaire
            mkdir_cmd = "mkdir -p /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets"
            self.execute_wsl_command(mkdir_cmd, check=True)
            
            # Écrire hash sans newline (utiliser printf)
            write_cmd = f'printf "%s" "{token_hash}" > {wsl_token_path}'
            result = self.execute_wsl_command(write_cmd, check=False)
            
            if result['success'] or result['returncode'] == 0:
                # Vérifier le contenu
                verify_cmd = f"cat {wsl_token_path}"
                verify_result = self.execute_wsl_command(verify_cmd, check=True)
                
                if verify_result['stdout'].strip() == token_hash:
                    self.log_step("Synchronisation credentials", "SUCCESS", 
                                 f"Token synchronisé: {token_raw[:8]}...{token_raw[-4:]}")
                    return True
                else:
                    self.log_step("Synchronisation credentials", "ERROR", 
                                 "Hash écrit ne correspond pas au hash source")
                    return False
            else:
                self.log_step("Synchronisation credentials", "ERROR", 
                             f"Échec écriture fichier WSL: {result.get('stderr')}")
                return False
                
        except Exception as e:
            self.log_step("Synchronisation credentials", "ERROR", 
                         f"Exception: {str(e)}")
            return False
    
    def restart_container(self) -> bool:
        """Redémarre le container comfyui-qwen."""
        self.log_step("Redémarrage container Docker", "IN_PROGRESS")
        
        restart_cmd = f"cd {COMFYUI_WSL_PATH} && docker-compose restart comfyui-qwen"
        result = self.execute_wsl_command(restart_cmd, check=False)
        
        if result['success'] or result['returncode'] == 0:
            self.log_step("Redémarrage container Docker", "SUCCESS", 
                         "Container redémarré, attente 30s pour démarrage...")
            time.sleep(30)  # Attendre démarrage ComfyUI
            return True
        else:
            self.log_step("Redémarrage container Docker", "ERROR", 
                         f"Échec redémarrage: {result.get('stderr')}")
            return False
    
    def list_custom_nodes(self) -> Dict[str, Any]:
        """Liste les custom nodes via l'API ComfyUI."""
        try:
            # Lire token pour authentification
            env_file = self.project_root / ".secrets/.env.generated"
            if not env_file.exists():
                return {'success': False, 'error': 'Fichier credentials introuvable'}
            
            content = env_file.read_text(encoding='utf-8')
            token_raw = None
            for line in content.split('\n'):
                if line.startswith('QWEN_API_USER_TOKEN='):
                    token_raw = line.split('=', 1)[1].strip()
                    break
            
            if not token_raw:
                return {'success': False, 'error': 'Token QWEN_API_USER_TOKEN introuvable'}
            
            # Requête API
            headers = {'Authorization': f'Bearer {token_raw}'}
            response = requests.get(f"{COMFYUI_URL}/object_info", headers=headers, timeout=10)
            
            if response.status_code == 200:
                object_info = response.json()
                return {
                    'success': True,
                    'nodes': list(object_info.keys()),
                    'count': len(object_info)
                }
            else:
                return {
                    'success': False,
                    'error': f'HTTP {response.status_code}: {response.text[:200]}'
                }
        except Exception as e:
            return {
                'success': False,
                'error': str(e)
            }
    
    def verify_installation(self) -> bool:
        """Vérifie que les 28 custom nodes Qwen sont chargés."""
        self.log_step("Vérification custom nodes chargés", "IN_PROGRESS")
        
        # Attendre que ComfyUI soit disponible
        max_retries = 6
        for attempt in range(max_retries):
            result = self.list_custom_nodes()
            if result['success']:
                break
            print(f"   Tentative {attempt+1}/{max_retries}: API non disponible, attente 10s...")
            time.sleep(10)
        
        if not result['success']:
            self.log_step("Vérification custom nodes chargés", "ERROR", 
                         f"API ComfyUI inaccessible: {result.get('error')}")
            return False
        
        all_nodes = result['nodes']
        qwen_nodes_found = [node for node in all_nodes if node in EXPECTED_QWEN_NODES]
        qwen_nodes_missing = [node for node in EXPECTED_QWEN_NODES if node not in all_nodes]
        
        self.results['custom_nodes_after'] = len(qwen_nodes_found)
        
        if len(qwen_nodes_found) == len(EXPECTED_QWEN_NODES):
            self.log_step("Vérification custom nodes chargés", "SUCCESS", 
                         f"✅ {len(qwen_nodes_found)}/{len(EXPECTED_QWEN_NODES)} custom nodes Qwen chargés (100%)")
            return True
        else:
            details = f"⚠️ {len(qwen_nodes_found)}/{len(EXPECTED_QWEN_NODES)} custom nodes chargés ({len(qwen_nodes_found)*100//len(EXPECTED_QWEN_NODES)}%)\n"
            details += f"   Manquants: {', '.join(qwen_nodes_missing[:5])}"
            if len(qwen_nodes_missing) > 5:
                details += f" ... (+{len(qwen_nodes_missing)-5} autres)"
            
            self.log_step("Vérification custom nodes chargés", "ERROR", details)
            return False
    
    def generate_installation_report(self) -> Path:
        """Génère rapport SDDD numéroté 22."""
        self.log_step("Génération rapport SDDD", "IN_PROGRESS")
        
        report_dir = self.project_root / "docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports"
        report_dir.mkdir(parents=True, exist_ok=True)
        
        report_path = report_dir / f"22-installation-complete-custom-nodes-qwen-{self.timestamp}.md"
        
        # Calculer durée totale
        duration_seconds = (datetime.fromisoformat(self.results['timestamp_end']) - 
                          datetime.fromisoformat(self.results['timestamp_start'])).total_seconds()
        duration_minutes = duration_seconds / 60
        
        # Comptage réussites/échecs
        steps_success = sum(1 for step in self.results['steps'] if step['status'] == 'SUCCESS')
        steps_error = sum(1 for step in self.results['steps'] if step['status'] == 'ERROR')
        
        # Générer contenu markdown
        report_content = f"""# Rapport 22 - Installation Complète Custom Nodes Qwen

**Phase** : 29 - Corrections Qwen ComfyUI  
**Date** : {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}  
**Statut** : {'✅ SUCCÈS' if self.results['success'] else '❌ ÉCHEC'}

## 1. Résumé Exécutif

- **Custom nodes Qwen installés** : {self.results['custom_nodes_after']}/{len(EXPECTED_QWEN_NODES)} ({self.results['custom_nodes_after']*100//len(EXPECTED_QWEN_NODES)}%)
- **ComfyUI-Login vérifié** : {'✅' if any(s['name'] == 'Vérification ComfyUI-Login' and s['status'] == 'SUCCESS' for s in self.results['steps']) else '❌'}
- **Credentials synchronisés** : {'✅' if any(s['name'] == 'Synchronisation credentials' and s['status'] == 'SUCCESS' for s in self.results['steps']) else '❌'}
- **Durée totale** : {duration_minutes:.1f} minutes
- **Étapes réussies** : {steps_success}/{len(self.results['steps'])}
- **Étapes échouées** : {steps_error}/{len(self.results['steps'])}

## 2. Étapes Détaillées

"""
        
        # Ajouter chaque étape
        for i, step in enumerate(self.results['steps'], 1):
            icon = "✅" if step['status'] == "SUCCESS" else "❌" if step['status'] == "ERROR" else "⏳"
            report_content += f"### 2.{i}. {step['name']}\n\n"
            report_content += f"**Statut** : {icon} {step['status']}  \n"
            report_content += f"**Timestamp** : {step['timestamp']}  \n"
            
            if step['details']:
                report_content += f"\n**Détails** :\n```\n{step['details']}\n```\n\n"
            else:
                report_content += "\n"
        
        # Résultats vérification
        report_content += f"""## 3. Résultats Vérification

### 3.1. Custom Nodes Qwen Chargés

**Attendus** : {len(EXPECTED_QWEN_NODES)} nodes  
**Chargés** : {self.results['custom_nodes_after']} nodes  
**Taux de réussite** : {self.results['custom_nodes_after']*100//len(EXPECTED_QWEN_NODES)}%

"""
        
        if self.results['custom_nodes_after'] < len(EXPECTED_QWEN_NODES):
            # Lister nodes manquants si échec
            all_nodes_result = self.list_custom_nodes()
            if all_nodes_result['success']:
                all_nodes = all_nodes_result['nodes']
                qwen_nodes_found = [node for node in all_nodes if node in EXPECTED_QWEN_NODES]
                qwen_nodes_missing = [node for node in EXPECTED_QWEN_NODES if node not in all_nodes]
                
                report_content += f"""### 3.2. Nodes Manquants ({len(qwen_nodes_missing)})

```
{chr(10).join(f"- {node}" for node in qwen_nodes_missing)}
```

### 3.3. Nodes Chargés ({len(qwen_nodes_found)})

```
{chr(10).join(f"- {node}" for node in qwen_nodes_found)}
```

"""
        else:
            report_content += "### 3.2. Tous les nodes sont chargés ✅\n\n"
        
        # Recommandations
        if self.results['success']:
            report_content += """## 4. Recommandations

✅ **Installation complète réussie !**

### Prochaines Actions

1. **Tester génération d'image** :
   ```bash
   python scripts/genai-auth/validation_complete_qwen_system.py
   ```

2. **Valider workflow Text-to-Image** :
   - Vérifier que le workflow minimal (7 nodes) fonctionne
   - Tester avec prompt simple : "A beautiful sunset over mountains"

3. **Documenter résultats** :
   - Capturer logs de génération réussie
   - Sauvegarder image de test

"""
        else:
            report_content += """## 4. Recommandations

❌ **Installation incomplète - Actions correctives requises**

### Diagnostic Approfondi

1. **Vérifier logs Docker** :
   ```bash
   docker logs comfyui-qwen --tail 100
   ```

2. **Vérifier installation manuelle** :
   ```bash
   docker exec -it comfyui-qwen bash
   cd /workspace/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge
   pip install -r requirements.txt
   ```

3. **Redémarrer et re-tester** :
   ```bash
   docker-compose restart comfyui-qwen
   # Attendre 30s
   python scripts/genai-auth/qwen-custom-nodes-installer.py
   ```

### Support

Si l'erreur persiste :
- Consulter Rapport 21 (archéologie installation)
- Vérifier compatibilité versions Python/dépendances
- Tester installation sur système de référence (Phase 12C)

"""
        
        # Métadonnées techniques
        report_content += f"""## 5. Métadonnées Techniques

### Configuration Système

- **Projet** : CoursIA - Phase 29
- **Container Docker** : comfyui-qwen
- **URL API** : {COMFYUI_URL}
- **Repository Qwen** : {QWEN_REPO_URL}
- **Repository ComfyUI-Login** : {COMFYUI_LOGIN_REPO_URL}

### Timing Exécution

```json
{{
  "timestamp_start": "{self.results['timestamp_start']}",
  "timestamp_end": "{self.results['timestamp_end']}",
  "duration_seconds": {duration_seconds:.1f},
  "duration_minutes": {duration_minutes:.1f}
}}
```

### Résultats JSON Complets

```json
{json.dumps(self.results, indent=2, ensure_ascii=False)}
```

---

**Généré automatiquement par** : `scripts/genai-auth/qwen-custom-nodes-installer.py`  
**Version rapport** : 22 (Phase 29 - SDDD)
"""
        
        # Écrire rapport
        report_path.write_text(report_content, encoding='utf-8')
        
        self.log_step("Génération rapport SDDD", "SUCCESS", 
                     f"Rapport sauvegardé: {report_path.name}")
        
        return report_path
    
    def run_full_installation(self) -> bool:
        """Exécute l'installation complète étape par étape."""
        print("=" * 80)
        print("🔧 INSTALLATION COMPLÈTE CUSTOM NODES QWEN - PHASE 29")
        print("=" * 80)
        
        try:
            # Étape 1: Supprimer installation existante
            if not self.remove_existing_qwen_nodes():
                return False
            
            # Étape 2: Installer Qwen custom nodes
            if not self.install_qwen_custom_nodes():
                return False
            
            # Étape 3: Vérifier ComfyUI-Login
            if not self.verify_comfyui_login():
                return False
            
            # Étape 4: Synchroniser credentials
            if not self.sync_credentials():
                return False
            
            # Étape 5: Redémarrer container
            if not self.restart_container():
                return False
            
            # Étape 6: Vérifier installation (28 nodes)
            verification_success = self.verify_installation()
            
            # Enregistrer résultats finaux
            self.results['timestamp_end'] = datetime.now().isoformat()
            self.results['success'] = verification_success
            
            # Étape 7: Générer rapport
            report_path = self.generate_installation_report()
            
            # Affichage final
            print("\n" + "=" * 80)
            if verification_success:
                print("✅ INSTALLATION RÉUSSIE - 28/28 CUSTOM NODES CHARGÉS")
            else:
                print("⚠️ INSTALLATION PARTIELLE - VÉRIFIER RAPPORT POUR DÉTAILS")
            print("=" * 80)
            print(f"\n📋 Rapport complet généré : {report_path}")
            print(f"\n📊 Custom nodes Qwen : {self.results['custom_nodes_after']}/{len(EXPECTED_QWEN_NODES)}")
            
            if verification_success:
                print("\n🚀 PROCHAINES ÉTAPES :")
                print("   1. Tester génération d'image avec validation_complete_qwen_system.py")
                print("   2. Valider workflow Text-to-Image minimal")
                print("   3. Documenter résultats dans rapport Phase 29")
            else:
                print("\n⚠️ ACTIONS CORRECTIVES REQUISES :")
                print("   1. Consulter rapport 22 pour diagnostic détaillé")
                print("   2. Vérifier logs Docker : docker logs comfyui-qwen")
                print("   3. Réexécuter installation si nécessaire")
            
            return verification_success
            
        except KeyboardInterrupt:
            print("\n\n⏹️ Installation interrompue par l'utilisateur")
            self.results['timestamp_end'] = datetime.now().isoformat()
            self.results['success'] = False
            self.log_step("Installation interrompue", "ERROR", "Interruption utilisateur (Ctrl+C)")
            self.generate_installation_report()
            return False
            
        except Exception as e:
            print(f"\n\n❌ ERREUR CRITIQUE : {str(e)}")
            import traceback
            traceback.print_exc()
            
            self.results['timestamp_end'] = datetime.now().isoformat()
            self.results['success'] = False
            self.log_step("Erreur critique", "ERROR", str(e))
            self.generate_installation_report()
            return False


def main():
    """Point d'entrée principal."""
    installer = QwenCustomNodesInstaller()
    success = installer.run_full_installation()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()