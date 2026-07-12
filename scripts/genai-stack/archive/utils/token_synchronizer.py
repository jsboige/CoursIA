#!/usr/bin/env python3
"""
token_synchronizer.py - Script d'unification définitive des tokens ComfyUI-Login

Ce script résout le problème d'incohérence systémique des tokens en créant
une source de vérité unique et en automatisant la synchronisation vers tous
les emplacements requis.

Usage:
    python token_synchronizer.py [--audit] [--sync] [--validate] [--source-token TOKEN]

Options:
    --audit       : Audit tous les emplacements de tokens existants
    --sync        : Synchronise tous les emplacements depuis la source de vérité
    --validate    : Valide la cohérence des tokens
    --source-token TOKEN : Token brut à utiliser comme source (optionnel)
"""

import os
import sys
import json
import hashlib
import bcrypt
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from datetime import datetime

@dataclass
class TokenLocation:
    """Représente un emplacement de token"""
    path: str
    type: str  # 'bcrypt', 'raw', 'env'
    description: str
    exists: bool = False
    content: Optional[str] = None
    is_valid: bool = False

@dataclass
class AuditReport:
    """Rapport d'audit des tokens"""
    timestamp: str
    locations: List[TokenLocation]
    inconsistencies: List[Dict]
    recommendations: List[str]
    
    def to_dict(self):
        return {
            'timestamp': self.timestamp,
            'locations': [asdict(loc) for loc in self.locations],
            'inconsistencies': self.inconsistencies,
            'recommendations': self.recommendations
        }

class TokenSynchronizer:
    """Synchroniseur unifié de tokens ComfyUI-Login"""
    
    def __init__(self, root_dir: Path = None):
        if root_dir is None:
            # Remonter jusqu'à la racine du projet (d:/Dev/CoursIA)
            # scripts/genai-auth/utils/token_synchronizer.py -> utils -> genai-auth -> scripts -> ROOT
            root_dir = Path(__file__).parent.parent.parent.parent
        
        self.root_dir = root_dir
        self.secrets_dir = root_dir / ".secrets"
        self.docker_config_dir = root_dir / "docker-configurations" / "services" / "comfyui-qwen"
        
        # Emplacements connus des tokens
        # NOTE: Utilisation exclusive du fichier .env Maître
        self.token_locations = [
            {
                'path': str(self.docker_config_dir / ".env"),
                'type': 'env',
                'description': 'Fichier .env MAÎTRE (Source de vérité unique)'
            },
            {
                'path': str(self.secrets_dir / "qwen-api-user.token"),
                'type': 'bcrypt',
                'description': 'Source de vérité - Hash bcrypt autoritaire'
            },
            {
                'path': str(self.secrets_dir / "comfyui_auth_tokens.conf"),
                'type': 'config',
                'description': 'Configuration unifiée des tokens'
            },
            {
                'path': str(self.docker_config_dir / ".secrets" / "qwen-api-user.token"),
                'type': 'bcrypt',
                'description': 'Token Docker côté WSL'
            }
        ]
    
    def log(self, message: str, level: str = "INFO"):
        """Affiche un message avec niveau"""
        prefix = {
            "INFO": "ℹ️",
            "SUCCESS": "✅",
            "ERROR": "❌",
            "WARNING": "⚠️",
            "AUDIT": "🔍",
            "SYNC": "🔄",
            "VALIDATE": "✔️"
        }.get(level, "•")
        print(f"{prefix} {message}")
    
    def ensure_directories(self):
        """Crée les répertoires nécessaires"""
        directories = [
            self.secrets_dir,
            self.docker_config_dir / ".secrets"
        ]
        
        for directory in directories:
            if not directory.exists():
                directory.mkdir(parents=True, exist_ok=True)
                self.log(f"Créé répertoire: {directory}", "INFO")
    
    def read_token_file(self, path: str) -> Optional[str]:
        """Lit le contenu d'un fichier de token"""
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read().strip()
                return content if content else None
        except Exception as e:
            self.log(f"Erreur lecture {path}: {e}", "ERROR")
            return None
    
    def write_token_file(self, path: str, content: str, backup: bool = False):
        """Écrit un token dans un fichier avec sauvegarde"""
        try:
            # Créer sauvegarde si fichier existe et utiliser le répertoire _backups
            if backup and Path(path).exists():
                # Créer le répertoire _backups s'il n'existe pas
                backup_dir = Path(path).parent.parent / "_backups"
                backup_dir.mkdir(parents=True, exist_ok=True)
                
                timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                backup_filename = f"{Path(path).name}.backup.{timestamp}"
                backup_path = backup_dir / backup_filename
                shutil.copy2(path, backup_path)
                self.log(f"Sauvegardé: {backup_path}", "INFO")
            
            # Créer répertoire si nécessaire
            Path(path).parent.mkdir(parents=True, exist_ok=True)
            
            # Écrire le nouveau contenu
            with open(path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            self.log(f"Écrit: {path}", "SUCCESS")
            return True
        except Exception as e:
            self.log(f"Erreur écriture {path}: {e}", "ERROR")
            return False
            return False
    
    def is_bcrypt_hash(self, token: str) -> bool:
        """Vérifie si un token est un hash bcrypt valide"""
        if not token:
            return False
        
        # Format bcrypt: $2b$12$ suivi de 53 caractères
        return token.startswith('$2b$12$') and len(token) == 60
    
    def generate_bcrypt_hash(self, raw_token: str) -> str:
        """Génère un hash bcrypt à partir d'un token brut"""
        try:
            salt = bcrypt.gensalt()
            hash_bytes = bcrypt.hashpw(raw_token.encode('utf-8'), salt)
            return hash_bytes.decode('utf-8')
        except Exception as e:
            self.log(f"Erreur génération hash: {e}", "ERROR")
            raise
    
    def validate_bcrypt_pair(self, raw_token: str, bcrypt_hash: str) -> bool:
        """Valide la correspondance entre token brut et hash bcrypt"""
        try:
            return bcrypt.checkpw(raw_token.encode('utf-8'), bcrypt_hash.encode('utf-8'))
        except Exception as e:
            self.log(f"Erreur validation bcrypt: {e}", "ERROR")
            return False
    
    def audit_tokens(self) -> AuditReport:
        """Audite tous les emplacements de tokens"""
        self.log("AUDIT COMPLET DES TOKENS COMFYUI-LOGIN", "AUDIT")
        
        locations = []
        inconsistencies = []
        
        # Analyser chaque emplacement
        for loc_info in self.token_locations:
            path = loc_info['path']
            token_type = loc_info['type']
            description = loc_info['description']
            
            location = TokenLocation(
                path=path,
                type=token_type,
                description=description,
                exists=Path(path).exists(),
                content=self.read_token_file(path) if Path(path).exists() else None
            )
            
            # Valider le contenu
            if location.content:
                if token_type == 'bcrypt':
                    location.is_valid = self.is_bcrypt_hash(location.content)
                elif token_type == 'raw':
                    location.is_valid = len(location.content) >= 20  # Token brut minimum
                elif token_type == 'env':
                    # Extraire les tokens des variables d'environnement
                    if 'COMFYUI_API_TOKEN=' in location.content:
                        token = location.content.split('COMFYUI_API_TOKEN=')[1].split('\n')[0].strip()
                        location.is_valid = self.is_bcrypt_hash(token)
                    elif 'COMFYUI_BEARER_TOKEN=' in location.content:
                        token = location.content.split('COMFYUI_BEARER_TOKEN=')[1].split('\n')[0].strip()
                        location.is_valid = self.is_bcrypt_hash(token)
            
            locations.append(location)
        
        # Détecter les incohérences
        bcrypt_hashes = [loc.content for loc in locations 
                      if loc.type == 'bcrypt' and loc.is_valid]
        
        if len(set(bcrypt_hashes)) > 1:
            inconsistencies.append({
                'type': 'multiple_bcrypt_hashes',
                'message': f"Hashs bcrypt différents trouvés: {len(set(bcrypt_hashes))}",
                'hashes': list(set(bcrypt_hashes))
            })
        
        # Vérifier la cohérence entre les emplacements
        env_bcrypt_tokens = []
        for loc in locations:
            if loc.type == 'env' and loc.content and loc.is_valid:
                # Extraire le token bcrypt des fichiers .env
                for line in loc.content.split('\n'):
                    if 'COMFYUI_API_TOKEN=' in line:
                        token = line.split('=')[1].strip()
                        if self.is_bcrypt_hash(token):
                            env_bcrypt_tokens.append(token)
                    elif 'COMFYUI_BEARER_TOKEN=' in line:
                        token = line.split('=')[1].strip()
                        if self.is_bcrypt_hash(token):
                            env_bcrypt_tokens.append(token)
        
        if env_bcrypt_tokens and len(set(env_bcrypt_tokens)) > 1:
            inconsistencies.append({
                'type': 'env_inconsistency',
                'message': f"Tokens bcrypt différents dans les fichiers .env: {len(set(env_bcrypt_tokens))}",
                'tokens': list(set(env_bcrypt_tokens))
            })
        
        # Générer les recommandations
        recommendations = []
        
        if inconsistencies:
            recommendations.append("CRÉER une source de vérité unique dans .secrets/comfyui_auth_tokens.conf")
            recommendations.append("SYNCHRONISER tous les emplacements depuis cette source")
            recommendations.append("VALIDIDER la cohérence après synchronisation")
        
        # Vérifier la présence de la source de vérité
        truth_config = self.secrets_dir / "comfyui_auth_tokens.conf"
        if not truth_config.exists():
            recommendations.append("CRÉER le fichier de configuration unifiée")
        
        return AuditReport(
            timestamp=datetime.now().isoformat(),
            locations=locations,
            inconsistencies=inconsistencies,
            recommendations=recommendations
        )
    
    def create_unified_config(self, raw_token: str = None) -> bool:
        """Crée la configuration unifiée des tokens"""
        self.log("CRÉATION CONFIGURATION UNIFIÉE", "SYNC")
        
        try:
            # S'assurer que le répertoire .secrets existe
            self.ensure_directories()
            
            config_path = self.secrets_dir / "comfyui_auth_tokens.conf"
            
            # Générer un nouveau token brut si non fourni
            if not raw_token:
                import secrets
                raw_token = secrets.token_urlsafe(32)
                self.log(f"Nouveau token brut généré: {raw_token[:8]}...", "INFO")
            
            # Générer le hash bcrypt correspondant
            bcrypt_hash = self.generate_bcrypt_hash(raw_token)
            
            # Créer la configuration unifiée
            config = {
                'version': '1.0',
                'created_at': datetime.now().isoformat(),
                'raw_token': raw_token,
                'bcrypt_hash': bcrypt_hash,
                'description': 'Configuration unifiée des tokens ComfyUI-Login - Source de vérité',
                'locations': [
                    {
                        'name': 'secrets_main',
                        'path': str(self.secrets_dir / "qwen-api-user.token"),
                        'type': 'bcrypt',
                        'content': bcrypt_hash
                    },
                    {
                        'name': 'env_master',
                        'path': str(self.root_dir / "docker-configurations" / "services" / "comfyui-qwen" / ".env"),
                        'type': 'env',
                        'content': bcrypt_hash
                    },
                    {
                        'name': 'docker_secrets',
                        'path': str(self.docker_config_dir / ".secrets" / "qwen-api-user.token"),
                        'type': 'bcrypt',
                        'content': bcrypt_hash
                    }
                ]
            }
            
            # Écrire le fichier de configuration
            with open(config_path, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2, ensure_ascii=False)
            
            self.log(f"Configuration unifiée créée: {config_path}", "SUCCESS")
            return True
            
        except Exception as e:
            self.log(f"Erreur création configuration: {e}", "ERROR")
            return False
    
    def synchronize_from_config(self) -> bool:
        """Synchronise tous les emplacements depuis la configuration unifiée"""
        self.log("SYNCHRONISATION DEPUIS CONFIGURATION UNIFIÉE", "SYNC")
        
        config_path = self.secrets_dir / "comfyui_auth_tokens.conf"
        
        if not config_path.exists():
            self.log("Configuration unifiée introuvable", "ERROR")
            return False
        
        try:
            # Lire la configuration
            with open(config_path, 'r', encoding='utf-8') as f:
                config = json.load(f)
            
            success_count = 0
            total_count = len(config['locations'])
            
            # Synchroniser chaque emplacement
            for location in config['locations']:
                path = location['path']
                content = location['content']
                location_type = location['type']
                
                if location_type == 'env':
                    # Pour les fichiers .env, mettre à jour uniquement les lignes pertinentes
                    if Path(path).exists():
                        existing_content = self.read_token_file(path)
                        if existing_content:
                            # Mettre à jour les lignes COMFYUI_*
                            lines = existing_content.split('\n')
                            
                            # Utiliser un dictionnaire pour éviter les doublons
                            env_vars = {}
                            other_lines = []
                            
                            for line in lines:
                                line = line.strip()
                                if not line:
                                    continue
                                    
                                if line.startswith('#'):
                                    other_lines.append(line)
                                    continue
                                    
                                if '=' in line:
                                    key, val = line.split('=', 1)
                                    env_vars[key.strip()] = val.strip()
                                else:
                                    other_lines.append(line)
                            
                            # Mettre à jour les valeurs
                            env_vars['COMFYUI_API_TOKEN'] = content
                            # Si COMFYUI_BEARER_TOKEN était présent, le mettre à jour, sinon l'ajouter si c'est le fichier docker
                            if 'COMFYUI_BEARER_TOKEN' in env_vars or 'docker' in location['name']:
                                env_vars['COMFYUI_BEARER_TOKEN'] = content
                            
                            # Toujours mettre à jour le raw token
                            env_vars['COMFYUI_RAW_TOKEN'] = config['raw_token']
                            
                            # Reconstruire le contenu
                            updated_lines = other_lines + [f"{k}={v}" for k, v in env_vars.items()]
                            
                            content = '\n'.join(updated_lines)
                
                # Écrire le fichier
                if self.write_token_file(path, content):
                    success_count += 1
                    self.log(f"Synchronisé: {location['name']}", "SUCCESS")
                else:
                    self.log(f"Échec synchronisation: {location['name']}", "ERROR")
            
            self.log(f"Synchronisation terminée: {success_count}/{total_count} emplacements", "SUCCESS")
            return success_count == total_count
            
        except Exception as e:
            self.log(f"Erreur synchronisation: {e}", "ERROR")
            return False
    
    def validate_consistency(self) -> bool:
        """Valide la cohérence des tokens synchronisés"""
        self.log("VALIDATION COHÉRENCE DES TOKENS", "VALIDATE")
        
        try:
            # Lire la configuration unifiée
            config_path = self.secrets_dir / "comfyui_auth_tokens.conf"
            
            if not config_path.exists():
                self.log("Configuration unifiée introuvable pour validation", "ERROR")
                return False
            
            with open(config_path, 'r', encoding='utf-8') as f:
                config = json.load(f)
            
            expected_bcrypt = config['bcrypt_hash']
            expected_raw = config['raw_token']
            
            # Valider chaque emplacement
            all_consistent = True
            
            for location in config['locations']:
                path = location['path']
                location_type = location['type']
                expected_content = location['content']
                
                if not Path(path).exists():
                    self.log(f"Fichier manquant: {location['name']}", "ERROR")
                    all_consistent = False
                    continue
                
                actual_content = self.read_token_file(path)
                
                if location_type == 'env':
                    # Pour les .env, vérifier uniquement les lignes pertinentes
                    if actual_content:
                        lines = actual_content.split('\n')
                        for line in lines:
                            if line.startswith('COMFYUI_API_TOKEN='):
                                actual_token = line.split('=')[1].strip()
                                if actual_token != expected_bcrypt:
                                    self.log(f"Incohérence COMFYUI_API_TOKEN dans {location['name']}", "ERROR")
                                    all_consistent = False
                            elif line.startswith('COMFYUI_BEARER_TOKEN='):
                                actual_token = line.split('=')[1].strip()
                                if actual_token != expected_bcrypt:
                                    self.log(f"Incohérence COMFYUI_BEARER_TOKEN dans {location['name']}", "ERROR")
                                    all_consistent = False
                else:
                    # Pour les fichiers de token directs
                    if actual_content != expected_content:
                        self.log(f"Incohérence dans {location['name']}", "ERROR")
                        all_consistent = False
            
            # Valider la correspondance bcrypt
            if not self.validate_bcrypt_pair(expected_raw, expected_bcrypt):
                self.log("Incohérence entre token brut et hash bcrypt", "ERROR")
                all_consistent = False
            
            if all_consistent:
                self.log("✅ TOUS LES TOKENS SONT COHÉRENTS", "SUCCESS")
            else:
                self.log("❌ DES INCOHÉRENCES ONT ÉTÉ DÉTECTÉES", "ERROR")
            
            return all_consistent
            
        except Exception as e:
            self.log(f"Erreur validation: {e}", "ERROR")
            return False
    
    def print_audit_report(self, report: AuditReport):
        """Affiche le rapport d'audit"""
        print(f"\n📊 RAPPORT D'AUDIT - {report.timestamp}")
        print("=" * 80)
        
        # Afficher les emplacements
        print(f"\n📍 EMPLACEMENTS TROUVÉS ({len(report.locations)}):")
        for loc in report.locations:
            status = "✅" if loc.exists and loc.is_valid else "❌" if not loc.exists else "⚠️"
            content_preview = loc.content[:20] + "..." if loc.content and len(loc.content) > 20 else loc.content
            print(f"  {status} {loc.description}")
            print(f"     Chemin: {loc.path}")
            print(f"     Type: {loc.type}")
            if loc.content:
                print(f"     Contenu: {content_preview}")
            print()
        
        # Afficher les incohérences
        if report.inconsistencies:
            print(f"⚠️ INCOHÉRENCES DÉTECTÉES ({len(report.inconsistencies)}):")
            for i, inconsistency in enumerate(report.inconsistencies, 1):
                print(f"  {i}. {inconsistency['message']}")
                if 'hashes' in inconsistency:
                    for h in inconsistency['hashes']:
                        print(f"     - {h}")
                print()
        
        # Afficher les recommandations
        if report.recommendations:
            print(f"💡 RECOMMANDATIONS ({len(report.recommendations)}):")
            for i, rec in enumerate(report.recommendations, 1):
                print(f"  {i}. {rec}")
            print()
    
    def run_complete_unification(self, source_token: str = None) -> bool:
        """Exécute le processus d'unification complète"""
        self.log("DÉMARRAGE UNIFICATION DÉFINITIVE DES TOKENS", "INFO")
        
        # 1. Audit initial
        audit_report = self.audit_tokens()
        self.print_audit_report(audit_report)
        
        # 2. Créer la configuration unifiée
        if not self.create_unified_config(source_token):
            self.log("Échec création configuration unifiée", "ERROR")
            return False
        
        # 3. Synchroniser tous les emplacements
        if not self.synchronize_from_config():
            self.log("Échec synchronisation", "ERROR")
            return False
        
        # 4. Valider la cohérence
        if not self.validate_consistency():
            self.log("Échec validation cohérence", "ERROR")
            return False
        
        self.log("🎉 UNIFICATION DES TOKENS TERMINÉE AVEC SUCCÈS", "SUCCESS")
        return True

def main():
    """Point d'entrée principal"""
    parser = argparse.ArgumentParser(
        description="Synchroniseur unifié de tokens ComfyUI-Login"
    )
    parser.add_argument(
        '--audit', '-a',
        action='store_true',
        help="Audite tous les emplacements de tokens"
    )
    parser.add_argument(
        '--sync', '-s',
        action='store_true',
        help="Synchronise depuis la configuration unifiée"
    )
    parser.add_argument(
        '--validate', '-v',
        action='store_true',
        help="Valide la cohérence des tokens"
    )
    parser.add_argument(
        '--source-token', '-t',
        type=str,
        help="Token brut à utiliser comme source"
    )
    parser.add_argument(
        '--unify', '-u',
        action='store_true',
        help="Exécute l'unification complète (audit + sync + validate)"
    )
    parser.add_argument(
        '--report', '-r',
        type=str,
        help="Sauvegarde le rapport d'audit dans un fichier"
    )
    
    args = parser.parse_args()
    
    # Créer le synchroniseur
    synchronizer = TokenSynchronizer()
    
    success = True
    
    try:
        if args.unify:
            # Unification complète
            success = synchronizer.run_complete_unification(args.source_token)
        elif args.audit:
            # Audit uniquement
            report = synchronizer.audit_tokens()
            synchronizer.print_audit_report(report)
            
            if args.report:
                with open(args.report, 'w', encoding='utf-8') as f:
                    json.dump(report.to_dict(), f, indent=2, ensure_ascii=False)
                print(f"📄 Rapport sauvegardé: {args.report}")
        
        elif args.sync:
            # Synchronisation uniquement
            success = synchronizer.synchronize_from_config()
        
        elif args.validate:
            # Validation uniquement
            success = synchronizer.validate_consistency()
        
        else:
            # Par défaut: audit
            report = synchronizer.audit_tokens()
            synchronizer.print_audit_report(report)
    
    except KeyboardInterrupt:
        print("\n⚠️ Opération interrompue par l'utilisateur")
        success = False
    except Exception as e:
        print(f"\n❌ Erreur fatale: {e}")
        import traceback
        traceback.print_exc()
        success = False
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()