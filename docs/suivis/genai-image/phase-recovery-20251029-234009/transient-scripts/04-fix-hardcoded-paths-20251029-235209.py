#!/usr/bin/env python3
"""
Script transient de correction des hardcoded paths - SDDD Phase Recovery
====================================================================

Ce script corrige les hardcoded paths Windows dans fix-qwen-workflow.py
pour le rendre portable et multi-plateforme.

Date: 2025-10-29
Auteur: Script transient SDDD
Version: 1.0 - Correction des hardcoded paths
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

class HardcodedPathFixer:
    """
    Classe pour corriger les hardcoded paths Windows dans les scripts consolidés
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
    
    def detect_hardcoded_paths(self) -> List[Dict[str, any]]:
        """Détecte tous les hardcoded paths dans le script"""
        logger.info("🔍 Détection des hardcoded paths...")
        
        hardcoded_patterns = [
            # Patterns Windows spécifiques
            r'"[dD]:[/\\][^"]*"',  # Chemins Windows avec lettres de lecteur
            r'"[cC]:[/\\][^"]*"',  # Chemins Windows avec C:
            r'"[eE]:[/\\][^"]*"',  # Chemins Windows avec E:
            r'"[a-zA-Z]:[/\\][^"]*"',  # Tous les chemins avec lettres de lecteur
            
            # Patterns de chemins absolus Windows
            r'"[A-Za-z]:[/\\][^"]*[/\\]docker-configurations"',
            r'"[A-Za-z]:[/\\][^"]*[/\\]ComfyUI"',
            r'"[A-Za-z]:[/\\][^"]*[/\\]custom_nodes"',
            
            # Patterns spécifiques au projet
            r'"d:/Dev/CoursIA[^"]*"',
            r'"D:/Dev/CoursIA[^"]*"',
        ]
        
        detected_issues = []
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
                
                for line_num, line in enumerate(lines, 1):
                    for pattern in hardcoded_patterns:
                        matches = re.finditer(pattern, line)
                        for match in matches:
                            detected_issues.append({
                                "line": line_num,
                                "column": match.start() + 1,
                                "pattern": pattern,
                                "matched_text": match.group(),
                                "full_line": line.strip(),
                                "severity": "HIGH" if "d:/Dev/CoursIA" in match.group() else "MEDIUM"
                            })
        
        except Exception as e:
            logger.error(f"❌ Erreur lecture fichier: {e}")
            return []
        
        logger.info(f"📊 {len(detected_issues)} hardcoded paths détectés")
        return detected_issues
    
    def generate_portable_replacement(self, original_path: str) -> str:
        """Génère un replacement portable pour un hardcoded path"""
        
        # Extraire le chemin relatif depuis le hardcoded path
        if "docker-configurations" in original_path:
            # Cas: d:/Dev/CoursIA/docker-configurations/comfyui-qwen/custom_nodes
            relative_path = "docker-configurations/comfyui-qwen/custom_nodes"
            return f'os.path.join(os.getcwd(), "{relative_path}")'
        
        elif "ComfyUI_QwenImageWanBridge" in original_path:
            # Cas: d:/Dev/CoursIA/docker-configurations/comfyui-qwen/custom_nodes/ComfyUI_QwenImageWanBridge
            relative_path = "docker-configurations/comfyui-qwen/custom_nodes/ComfyUI_QwenImageWanBridge"
            return f'os.path.join(os.getcwd(), "{relative_path}")'
        
        elif "custom_nodes" in original_path:
            # Cas générique pour custom_nodes
            relative_path = "docker-configurations/comfyui-qwen/custom_nodes"
            return f'os.path.join(os.getcwd(), "{relative_path}")'
        
        else:
            # Cas par défaut : utiliser Pathlib avec détection automatique
            return 'str(Path.cwd() / "docker-configurations" / "comfyui-qwen" / "custom_nodes")'
    
    def fix_hardcoded_paths(self) -> bool:
        """Corrige tous les hardcoded paths détectés"""
        logger.info("🔧 Correction des hardcoded paths...")
        
        detected_issues = self.detect_hardcoded_paths()
        
        if not detected_issues:
            logger.info("✅ Aucun hardcoded path détecté")
            return True
        
        # Créer backup avant modification
        self.create_backup(self.script_path)
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Appliquer les corrections
            corrections_applied = 0
            
            # Correction 1: Remplacer le hardcoded path dans __init__
            old_default_path = '"d:/Dev/CoursIA/docker-configurations/comfyui-qwen/custom_nodes"'
            new_default_path = 'os.path.join(os.getcwd(), "docker-configurations/comfyui-qwen/custom_nodes")'
            
            if old_default_path in content:
                content = content.replace(old_default_path, new_default_path)
                corrections_applied += 1
                logger.info(f"✅ Correction path par défaut: {old_default_path} → {new_default_path}")
            
            # Correction 2: Rendre les chemins configurables via variables d'environnement
            # Ajouter une section de configuration portable au début du script
            config_section = '''
# Configuration portable multi-plateforme
def get_workspace_path():
    """Retourne le chemin de workspace portable"""
    # Priorité: Variable d'environnement > chemin relatif > défaut
    env_workspace = os.environ.get('QWEN_WORKSPACE_PATH')
    if env_workspace:
        return Path(env_workspace)
    
    # Chemin relatif au répertoire courant
    current_dir = Path.cwd()
    relative_path = current_dir / "docker-configurations" / "comfyui-qwen" / "custom_nodes"
    
    if relative_path.exists():
        return relative_path
    
    # Chemin par défaut (fallback)
    return Path("docker-configurations/comfyui-qwen/custom_nodes")

# Utiliser la configuration portable
DEFAULT_WORKSPACE_PATH = str(get_workspace_path())
'''
            
            # Insérer la section de configuration après les imports
            import_insertion_point = content.find('class QwenWorkflowFixer:')
            if import_insertion_point > 0:
                # Trouver la fin des imports
                lines = content.split('\n')
                import_end_line = 0
                for i, line in enumerate(lines):
                    if line.strip().startswith('class ') and import_insertion_point > 0:
                        import_end_line = i
                        break
                
                # Insérer la configuration avant la classe
                lines.insert(import_end_line, config_section.strip())
                content = '\n'.join(lines)
                corrections_applied += 1
                logger.info("✅ Section configuration portable ajoutée")
            
            # Correction 3: Remplacer les hardcoded paths restants par des appels de fonction
            additional_patterns = [
                (r'"d:/Dev/CoursIA/docker-configurations/comfyui-qwen/custom_nodes"', 'get_workspace_path()'),
                (r'"d:/Dev/CoursIA[^"]*ComfyUI_QwenImageWanBridge[^"]*"', 'str(get_workspace_path() / "ComfyUI_QwenImageWanBridge")'),
                (r'self\.workspace_path = Path\("d:/Dev/CoursIA[^"]*"\)', 'self.workspace_path = get_workspace_path()'),
            ]
            
            for pattern, replacement in additional_patterns:
                if re.search(pattern, content):
                    content = re.sub(pattern, replacement, content)
                    corrections_applied += 1
                    logger.info(f"✅ Correction pattern: {pattern[:50]}...")
            
            # Réécrire le fichier avec toutes les corrections
            with open(self.script_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            logger.info(f"✅ Fichier corrigé: {self.script_path} ({corrections_applied} corrections)")
            
            self.modifications_log.append({
                "action": "fix_hardcoded_paths",
                "file": str(self.script_path),
                "issues_detected": len(detected_issues),
                "corrections_applied": corrections_applied,
                "timestamp": datetime.now().isoformat()
            })
            
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur correction {self.script_path}: {e}")
            return False
    
    def validate_fixes(self) -> Dict[str, any]:
        """Valide que les corrections ont été appliquées correctement"""
        logger.info("🧪 Validation des corrections de hardcoded paths...")
        
        validation_results = {
            "hardcoded_paths_remaining": 0,
            "portable_config_present": False,
            "overall_success": False
        }
        
        try:
            with open(self.script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Vérifier qu'il n'y a plus de hardcoded paths Windows
            windows_patterns = [
                r'"[dD]:[/\\][^"]*"',
                r'"[cC]:[/\\][^"]*"',
                r'"[eE]:[/\\][^"]*"',
            ]
            
            remaining_hardcoded = 0
            for pattern in windows_patterns:
                matches = re.findall(pattern, content)
                remaining_hardcoded += len(matches)
            
            validation_results["hardcoded_paths_remaining"] = remaining_hardcoded
            
            # Vérifier que la configuration portable est présente
            validation_results["portable_config_present"] = "get_workspace_path()" in content
            
            # Succès global
            validation_results["overall_success"] = (
                remaining_hardcoded == 0 and 
                validation_results["portable_config_present"]
            )
            
            logger.info(f"📊 Résultats validation:")
            logger.info(f"  Hardcoded paths restants: {remaining_hardcoded}")
            logger.info(f"  Configuration portable présente: {validation_results['portable_config_present']}")
            logger.info(f"  Succès global: {validation_results['overall_success']}")
            
        except Exception as e:
            logger.error(f"❌ Erreur validation: {e}")
        
        return validation_results
    
    def generate_report(self) -> str:
        """Génère un rapport détaillé des corrections appliquées"""
        report = []
        report.append("=" * 60)
        report.append("RAPPORT DE CORRECTION DES HARDCODED PATHS")
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
        description="Script transient de correction des hardcoded paths Windows",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        "--target-script",
        default="scripts/genai-auth/fix-qwen-workflow.py",
        help="Script cible à corriger (défaut: scripts/genai-auth/fix-qwen-workflow.py)"
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
        fixer = HardcodedPathFixer(
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
        success = fixer.fix_hardcoded_paths()
        
        if success:
            # Validation post-correction
            validation_results = fixer.validate_fixes()
            
            if validation_results["overall_success"]:
                logger.info("🎉 Corrections des hardcoded paths appliquées avec succès!")
            else:
                logger.warning("⚠️ Certaines corrections nécessitent une attention")
            
            # Générer et afficher le rapport
            report = fixer.generate_report()
            print("\n" + report)
            
            return 0 if validation_results["overall_success"] else 1
        else:
            logger.error("❌ Échec de la correction des hardcoded paths")
            return 1
            
    except KeyboardInterrupt:
        logger.info("⏹️ Opération interrompue par l'utilisateur")
        return 130
    except Exception as e:
        logger.error(f"❌ Erreur inattendue: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(main())