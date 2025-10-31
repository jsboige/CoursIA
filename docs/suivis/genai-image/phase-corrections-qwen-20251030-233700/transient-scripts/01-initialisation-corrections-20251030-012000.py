#!/usr/bin/env python3
"""
Script d'initialisation des corrections Qwen - Phase Corrections 2025-10-30

Auteur: Roo AI Assistant
Date: 2025-10-30 01:20:00
Objectif: Initialiser l'environnement pour les corrections Qwen
"""

import os
import sys
import json
import shutil
from datetime import datetime
from pathlib import Path

class CorrectionsInitializer:
    """Classe pour gérer l'initialisation des corrections Qwen"""
    
    def __init__(self):
        # Correction : utiliser resolve() pour gérer les chemins relatifs correctement
        script_path = Path(__file__).resolve()
        self.base_path = script_path.parent.parent
        self.phase_name = "phase-corrections-qwen-20251030-233700"
        self.timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        
        # Structure des répertoires
        self.dirs = {
            'transient_scripts': self.base_path / 'transient-scripts',
            'rapports': self.base_path / 'rapports',
            'config_backups': self.base_path / 'config-backups'
        }
        
        # Fichiers de configuration à surveiller
        self.config_files = [
            'docker-configurations/comfyui-qwen/.env',
            'docker-configurations/comfyui-qwen/docker-compose.yml',
            'docker-configurations/comfyui-qwen/custom_nodes/ComfyUI_QwenImageWanBridge/nodes/qwen_wrapper_nodes.py'
        ]
        
    def log_action(self, action, details=""):
        """Enregistre une action avec timestamp"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print(f"[{timestamp}] {action}: {details}")
        
    def verify_structure(self):
        """Vérifie que la structure des répertoires est correcte"""
        self.log_action("VÉRIFICATION_STRUCTURE", "Début de vérification")
        
        all_dirs_exist = True
        for dir_name, dir_path in self.dirs.items():
            if dir_path.exists():
                self.log_action("REPERTOIRE_OK", f"{dir_name}: {dir_path}")
            else:
                self.log_action("REPERTOIRE_MANQUANT", f"{dir_name}: {dir_path}")
                all_dirs_exist = False
                
        return all_dirs_exist
        
    def backup_configurations(self):
        """Crée des sauvegardes des fichiers de configuration"""
        self.log_action("SAUVEGARDE_CONFIG", "Début des sauvegardes")
        
        backup_dir = self.dirs['config_backups'] / f"backup-initial-{self.timestamp}"
        backup_dir.mkdir(exist_ok=True)
        
        backups_created = []
        for config_file in self.config_files:
            config_path = Path(config_file)
            if config_path.exists():
                # Crée le sous-répertoire si nécessaire
                backup_subdir = backup_dir / config_path.parent.name
                backup_subdir.mkdir(exist_ok=True)
                
                backup_file = backup_subdir / config_path.name
                shutil.copy2(config_path, backup_file)
                backups_created.append(str(backup_file))
                self.log_action("SAUVEGARDE_FICHIER", f"{config_file} -> {backup_file}")
            else:
                self.log_action("FICHIER_ABSENT", f"{config_file}")
                
        return backups_created
        
    def analyze_hardcoded_paths(self):
        """Analyse les fichiers pour détecter les chemins hardcodés"""
        self.log_action("ANALYSE_PATHS", "Recherche des chemins hardcodés")
        
        hardcoded_patterns = [
            r'C:\\',
            r'D:\\',
            r'/home/',
            r'/usr/',
            r'/opt/',
            r'/var/',
            r'localhost',
            r'127\.0\.0\.1',
            r'192\.168\.',
            r'10\.0\.0\.'
        ]
        
        files_with_hardcoded_paths = []
        
        # Analyse des fichiers Python dans les custom nodes
        custom_nodes_dir = Path('docker-configurations/comfyui-qwen/custom_nodes/ComfyUI_QwenImageWanBridge/nodes')
        if custom_nodes_dir.exists():
            for py_file in custom_nodes_dir.glob('*.py'):
                try:
                    with open(py_file, 'r', encoding='utf-8') as f:
                        content = f.read()
                        
                    for pattern in hardcoded_patterns:
                        import re
                        if re.search(pattern, content):
                            files_with_hardcoded_paths.append({
                                'file': str(py_file),
                                'pattern': pattern,
                                'type': 'hardcoded_path'
                            })
                            break
                            
                except Exception as e:
                    self.log_action("ERREUR_LECTURE", f"{py_file}: {e}")
                    
        return files_with_hardcoded_paths
        
    def generate_initial_report(self, backups_created, hardcoded_issues):
        """Génère le rapport initial"""
        self.log_action("GENERATION_RAPPORT", "Création du rapport initial")
        
        report_data = {
            'phase': self.phase_name,
            'timestamp': self.timestamp,
            'statut': 'initialisé',
            'sauvegardes': {
                'nombre': len(backups_created),
                'fichiers': backups_created
            },
            'problemes_detectes': {
                'hardcoded_paths': len(hardcoded_issues),
                'details': hardcoded_issues
            }
        }
        
        report_file = self.dirs['rapports'] / f"rapport-initial-{self.timestamp}.md"
        
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(f"# Rapport Initial - Corrections Qwen\n\n")
            f.write(f"**Phase**: {report_data['phase']}\n")
            f.write(f"**Timestamp**: {report_data['timestamp']}\n")
            f.write(f"**Statut**: {report_data['statut']}\n\n")
            
            f.write("## Sauvegardes Créées\n\n")
            f.write(f"- **Nombre**: {report_data['sauvegardes']['nombre']}\n")
            for backup in report_data['sauvegardes']['fichiers']:
                f.write(f"- {backup}\n")
            f.write("\n")
            
            f.write("## Problèmes Détectés\n\n")
            f.write(f"- **Chemins hardcodés**: {report_data['problemes_detectes']['hardcoded_paths']}\n")
            
            if report_data['problemes_detectes']['details']:
                f.write("\n### Détails des Chemins Hardcodés\n\n")
                for issue in report_data['problemes_detectes']['details']:
                    f.write(f"- **Fichier**: {issue['file']}\n")
                    f.write(f"  - **Pattern**: {issue['pattern']}\n")
                    f.write(f"  - **Type**: {issue['type']}\n")
                    
        self.log_action("RAPPORT_CRÉÉ", f"{report_file}")
        return str(report_file)
        
    def run_initialization(self):
        """Exécute le processus d'initialisation complet"""
        print("=" * 60)
        print(f"INITIALISATION CORRECTIONS QWEN - {self.phase_name}")
        print("=" * 60)
        
        # 1. Vérification de la structure
        if not self.verify_structure():
            self.log_action("ERREUR_STRUCTURE", "La structure des répertoires est incomplète")
            return False
            
        # 2. Sauvegarde des configurations
        backups_created = self.backup_configurations()
        
        # 3. Analyse des problèmes
        hardcoded_issues = self.analyze_hardcoded_paths()
        
        # 4. Génération du rapport
        report_file = self.generate_initial_report(backups_created, hardcoded_issues)
        
        # 5. Résumé
        print("\n" + "=" * 60)
        print("RÉSUMÉ DE L'INITIALISATION")
        print("=" * 60)
        print(f"✅ Structure vérifiée")
        print(f"✅ {len(backups_created)} sauvegardes créées")
        print(f"🔍 {len(hardcoded_issues)} fichiers avec chemins hardcodés détectés")
        print(f"📄 Rapport généré: {report_file}")
        print("\nL'espace de suivi est prêt pour les corrections!")
        print("=" * 60)
        
        return True

def main():
    """Point d'entrée principal"""
    initializer = CorrectionsInitializer()
    success = initializer.run_initialization()
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()