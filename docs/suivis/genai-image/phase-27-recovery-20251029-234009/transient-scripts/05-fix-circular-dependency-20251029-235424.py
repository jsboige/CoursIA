#!/usr/bin/env python3
"""
Script transient de correction de dépendance circulaire - SDDD Phase Recovery
========================================================================

Ce script corrige la dépendance circulaire entre validate-qwen-solution.py
et comfyui_client_helper.py en implémentant ComfyUIClient directement.

Date: 2025-10-29
Auteur: Script transient SDDD
Version: 1.0 - Correction de dépendance circulaire
"""

import os
import sys
import re
import logging
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple

# Configuration du logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class CircularDependencyFixer:
    """
    Classe pour corriger la dépendance circulaire dans les scripts consolidés
    """
    
    def __init__(self, script_path: str, backup_enabled=True):
        self.script_path = Path(script_path)
        self.backup_enabled = backup_enabled
        self.backup_dir = self.script_path.parent / "backups"
        self.modifications_log = []
        
        # Créer le répertoire de backup si nécessaire
        if self.backup_enabled:
            self.backup_dir.mkdir(parents=True, exist_ok=True)
    
    def create_backup(self, file_path: Path) -> Optional[Path]:
        """Crée une sauvegarde du fichier avant modification"""
        if not self.backup_enabled:
            return None
            
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup_name = f"{file_path.name}.backup_{timestamp}"
        backup_path = self.backup_dir / backup_name
        
        try:
            if file_path.exists():
                import shutil
                shutil.copy2(file_path, backup_path)
                logger.info(f"💾 Backup créé: {backup_path}")
                self.modifications_log.append({
                    "action": "backup",
                    "file": str(file_path),
                    "backup": str(backup_path),
                    "timestamp": datetime.now().isoformat()
                })
                return backup_path
        except Exception as e:
            logger.error(f"❌ Erreur backup {file_path}: {e}")
        
        return None
    
    def detect_circular_dependency(self) -> Dict[str, any]:
        """Détecte la dépendance circulaire dans le script"""
        logger.info("🔍 Détection de la dépendance circulaire...")
        
        detected_issues = []
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
                
                for line_num, line in enumerate(lines, 1):
                    # Pattern de dépendance circulaire critique
                    if 'from comfyui_client_helper import ComfyUIClient' in line:
                        detected_issues.append({
                            "line": line_num,
                            "column": line.find('from comfyui_client_helper'),
                            "pattern": "from comfyui_client_helper import ComfyUIClient",
                            "matched_text": line.strip(),
                            "full_line": line.strip(),
                            "severity": "CRITICAL",
                            "description": "Dépendance circulaire avec comfyui_client_helper.py"
                        })
                    
                    # Pattern d'import de ComfyUIConfig
                    if 'from comfyui_client_helper import ComfyUIConfig' in line:
                        detected_issues.append({
                            "line": line_num,
                            "column": line.find('from comfyui_client_helper'),
                            "pattern": "from comfyui_client_helper import ComfyUIConfig",
                            "matched_text": line.strip(),
                            "full_line": line.strip(),
                            "severity": "HIGH",
                            "description": "Dépendance sur ComfyUIConfig depuis comfyui_client_helper"
                        })
        
        except Exception as e:
            logger.error(f"❌ Erreur lecture fichier: {e}")
            return {"issues": [], "error": str(e)}
        
        logger.info(f"📊 {len(detected_issues)} dépendances circulaires détectées")
        return {"issues": detected_issues, "error": None}
    
    def generate_comfyui_client_implementation(self) -> str:
        """Génère une implémentation inline de ComfyUIClient"""
        
        implementation = '''
# Implémentation inline de ComfyUIClient pour éviter la dépendance circulaire
# Cette implémentation remplace l'import depuis comfyui_client_helper

import requests
import json
import logging
from typing import Dict, List, Optional, Any
from datetime import datetime

logger = logging.getLogger(__name__)

class ComfyUIClient:
    """
    Client API ComfyUI léger et autonome
    Implémenté inline pour éviter la dépendance circulaire
    """
    
    def __init__(self, base_url: str = 'http://localhost:8188', timeout: int = 30, max_retries: int = 3):
        self.base_url = base_url.rstrip('/')
        self.timeout = timeout
        self.max_retries = max_retries
        self.session = requests.Session()
        
        # Configuration des headers par défaut
        self.session.headers.update({
            'Content-Type': 'application/json',
            'User-Agent': 'ComfyUIClient/1.0-SDDD'
        })
        
        logger.info(f"ComfyUIClient initialisé: {self.base_url}")
    
    def _make_request(self, method: str, endpoint: str, **kwargs) -> Optional[Dict[str, Any]]:
        """Effectue une requête HTTP avec gestion des erreurs"""
        url = f"{self.base_url}/{endpoint.lstrip('/')}"
        
        for attempt in range(self.max_retries):
            try:
                if method.upper() == 'GET':
                    response = self.session.get(url, timeout=self.timeout, **kwargs)
                elif method.upper() == 'POST':
                    response = self.session.post(url, timeout=self.timeout, **kwargs)
                else:
                    raise ValueError(f"Méthode HTTP non supportée: {method}")
                
                response.raise_for_status()
                return response.json()
                
            except requests.exceptions.RequestException as e:
                logger.warning(f"Tentative {attempt + 1}/{self.max_retries} échouée: {e}")
                if attempt == self.max_retries - 1:
                    raise
                time.sleep(2 ** attempt)  # Backoff exponentiel
        
        return None
    
    def get_system_stats(self) -> Optional[Dict[str, Any]]:
        """Récupère les statistiques système de ComfyUI"""
        try:
            result = self._make_request('GET', 'system_stats')
            if result:
                logger.info("Statistiques système récupérées avec succès")
            return result
        except Exception as e:
            logger.error(f"Erreur récupération stats système: {e}")
            return None
    
    def get_object_info(self) -> Optional[Dict[str, Any]]:
        """Récupère les informations des objets ComfyUI"""
        try:
            result = self._make_request('GET', 'object_info')
            if result:
                logger.info("Informations objets récupérées avec succès")
            return result
        except Exception as e:
            logger.error(f"Erreur récupération infos objets: {e}")
            return None
    
    def get_history(self, prompt_id: str) -> Optional[List[Dict[str, Any]]]:
        """Récupère l'historique pour un prompt ID"""
        try:
            result = self._make_request('GET', f'history/{prompt_id}')
            if result:
                logger.info(f"Historique récupéré pour prompt {prompt_id}")
            return result if isinstance(result, list) else [result]
        except Exception as e:
            logger.error(f"Erreur récupération historique: {e}")
            return None
    
    def submit_workflow(self, prompt: str, workflow: Dict[str, Any]) -> Optional[str]:
        """Soumet un workflow à ComfyUI"""
        try:
            payload = {
                'prompt': prompt,
                'workflow': workflow
            }
            
            result = self._make_request('POST', 'prompt', json=payload)
            if result and 'prompt_id' in result:
                prompt_id = result['prompt_id']
                logger.info(f"Workflow soumis avec ID: {prompt_id}")
                return prompt_id
            else:
                logger.error("Réponse invalide lors de la soumission du workflow")
                return None
        except Exception as e:
            logger.error(f"Erreur soumission workflow: {e}")
            return None
    
    def queue_prompt(self, prompt_id: str) -> bool:
        """Place un prompt dans la file d'attente"""
        try:
            payload = {'prompt_id': prompt_id}
            result = self._make_request('POST', 'queue', json=payload)
            
            if result and result.get('success'):
                logger.info(f"Prompt {prompt_id} mis en file d'attente")
                return True
            else:
                logger.error(f"Échec mise en file d'attente: {result}")
                return False
        except Exception as e:
            logger.error(f"Erreur mise en file d'attente: {e}")
            return False

class ComfyUIConfig:
    """
    Configuration ComfyUI inline pour éviter la dépendance circulaire
    """
    
    def __init__(self, base_url: str = 'http://localhost:8188', timeout: int = 30, max_retries: int = 3):
        self.base_url = base_url
        self.timeout = timeout
        self.max_retries = max_retries
'''
        
        return implementation
    
    def fix_circular_dependency(self) -> bool:
        """Corrige la dépendance circulaire en implémentant ComfyUIClient inline"""
        logger.info("🔧 Correction de la dépendance circulaire...")
        
        detected = self.detect_circular_dependency()
        
        if "error" in detected:
            logger.error(f"❌ Erreur détection: {detected['error']}")
            return False
        
        issues = detected["issues"]
        
        if not issues:
            logger.info("✅ Aucune dépendance circulaire détectée")
            return True
        
        # Créer backup avant modification
        self.create_backup(self.script_path)
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            corrections_applied = 0
            
            # Étape 1: Supprimer l'import circulaire
            old_import_line = 'from comfyui_client_helper import ComfyUIClient, ComfyUIConfig'
            if old_import_line in content:
                content = content.replace(old_import_line, '# Import circulaire supprimé - ComfyUIClient implémenté inline')
                corrections_applied += 1
                logger.info("✅ Import circulaire supprimé")
            
            # Étape 2: Ajouter l'implémentation inline de ComfyUIClient
            implementation = self.generate_comfyui_client_implementation()
            
            # Trouver le point d'insertion (après les imports existants)
            lines = content.split('\n')
            insertion_point = 0
            
            for i, line in enumerate(lines):
                if line.strip().startswith('logger = logging.getLogger(__name__)'):
                    insertion_point = i + 1
                    break
            
            # Insérer l'implémentation
            lines.insert(insertion_point, implementation.strip())
            content = '\n'.join(lines)
            corrections_applied += 1
            logger.info("✅ Implémentation ComfyUIClient ajoutée")
            
            # Étape 3: Corriger les références restantes
            # Remplacer les références à ComfyUIConfig si nécessaire
            config_replacements = [
                ('self.comfyui_config = ComfyUIConfig(', 'self.comfyui_config = ComfyUIConfigInline('),
            ]
            
            for old_ref, new_ref in config_replacements:
                if old_ref in content:
                    content = content.replace(old_ref, new_ref)
                    corrections_applied += 1
                    logger.info(f"✅ Référence ComfyUIConfig corrigée")
            
            # Réécrire le fichier
            with open(self.script_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            logger.info(f"✅ Fichier corrigé: {self.script_path} ({corrections_applied} corrections)")
            
            self.modifications_log.append({
                "action": "fix_circular_dependency",
                "file": str(self.script_path),
                "issues_detected": len(issues),
                "corrections_applied": corrections_applied,
                "timestamp": datetime.now().isoformat()
            })
            
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur correction {self.script_path}: {e}")
            return False
    
    def validate_fixes(self) -> Dict[str, any]:
        """Valide que les corrections ont été appliquées correctement"""
        logger.info("🧪 Validation des corrections de dépendance circulaire...")
        
        validation_results = {
            "circular_dependency_remaining": False,
            "inline_implementation_present": False,
            "overall_success": False
        }
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Vérifier que l'import circulaire a été supprimé
            validation_results["circular_dependency_remaining"] = 'from comfyui_client_helper import ComfyUIClient' in content
            
            # Vérifier que l'implémentation inline est présente
            validation_results["inline_implementation_present"] = 'class ComfyUIClient:' in content and 'Implémenté inline pour éviter la dépendance circulaire' in content
            
            # Succès global
            validation_results["overall_success"] = (
                not validation_results["circular_dependency_remaining"] and 
                validation_results["inline_implementation_present"]
            )
            
            logger.info(f"📊 Résultats validation:")
            logger.info(f"  Dépendance circulaire restante: {validation_results['circular_dependency_remaining']}")
            logger.info(f"  Implémentation inline présente: {validation_results['inline_implementation_present']}")
            logger.info(f"  Succès global: {validation_results['overall_success']}")
            
        except Exception as e:
            logger.error(f"❌ Erreur validation: {e}")
        
        return validation_results
    
    def generate_report(self) -> str:
        """Génère un rapport détaillé des corrections appliquées"""
        report = []
        report.append("=" * 60)
        report.append("RAPPORT DE CORRECTION DE DÉPENDANCE CIRCULAIRE")
        report.append("=" * 60)
        report.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append(f"Script cible: {self.script_path}")
        report.append(f"Total modifications: {len(self.modifications_log)}")
        report.append("")
        
        for i, mod in enumerate(self.modifications_log, 1):
            report.append(f"{i}. {mod['action'].upper()}: {mod['file']}")
            if 'issues_detected' in mod:
                report.append(f"   Problèmes détectés: {mod['issues_detected']}")
            if 'corrections_applied' in mod:
                report.append(f"   Corrections appliquées: {mod['corrections_applied']}")
            report.append(f"   Timestamp: {mod['timestamp']}")
            report.append("")
        
        return "\n".join(report)

def main():
    """Fonction principale du script transient"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Script transient de correction de dépendance circulaire",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        "--target-script",
        default="scripts/genai-auth/validate-qwen-solution.py",
        help="Script cible à corriger (défaut: scripts/genai-auth/validate-qwen-solution.py)"
    )
    
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="Désactiver la création de backups avant modification"
    )
    
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="Valider uniquement sans appliquer de corrections"
    )
    
    args = parser.parse_args()
    
    try:
        # Initialiser le fixer
        fixer = CircularDependencyFixer(
            script_path=args.target_script,
            backup_enabled=not args.no_backup
        )
        
        # Mode validation uniquement
        if args.validate_only:
            validation_results = fixer.validate_fixes()
            if validation_results["overall_success"]:
                logger.info("✅ Validation réussie - aucune correction nécessaire")
                return 0
            else:
                logger.warning("⚠️ Validation échouée - corrections nécessaires")
                return 1
        
        # Mode correction
        success = fixer.fix_circular_dependency()
        
        if success:
            # Validation post-correction
            validation_results = fixer.validate_fixes()
            
            if validation_results["overall_success"]:
                logger.info("🎉 Corrections de dépendance circulaire appliquées avec succès!")
            else:
                logger.warning("⚠️ Certaines corrections nécessitent une attention")
            
            # Générer et afficher le rapport
            report = fixer.generate_report()
            print("\n" + report)
            
            return 0 if validation_results["overall_success"] else 1
        else:
            logger.error("❌ Échec de la correction de dépendance circulaire")
            return 1
            
    except KeyboardInterrupt:
        logger.info("⏹️ Opération interrompue par l'utilisateur")
        return 130
    except Exception as e:
        logger.error(f"❌ Erreur inattendue: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(main())