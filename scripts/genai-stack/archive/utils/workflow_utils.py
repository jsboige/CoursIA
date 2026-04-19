#!/usr/bin/env python3
"""
Utilitaire consolidé pour la manipulation de workflows ComfyUI

Ce script fusionne les fonctionnalités de :
- fix_workflow_links.py (supprimé)
- Autres scripts de manipulation de workflows

FONCTIONNALITÉS PRINCIPALES :
1. Validation de workflows JSON
2. Correction des liens dans les workflows
3. Gestion des métadonnées de workflows
4. Backup et restauration de workflows
5. Optimisation des workflows
"""

import os
import sys
import json
import shutil
import logging
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Any

# Configuration du logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class WorkflowUtils:
    """
    Classe utilitaire consolidée pour la manipulation des workflows ComfyUI
    """
    
    def __init__(self, workspace_path: str = None, backup_enabled: bool = True):
        self.workspace_path = Path(workspace_path) if workspace_path else Path.cwd()
        self.backup_dir = self.workspace_path / "backups"
        self.backup_enabled = backup_enabled
        
        # Créer le répertoire de backup si nécessaire
        if self.backup_enabled:
            self.backup_dir.mkdir(parents=True, exist_ok=True)
    
    def validate_workflow_json(self, workflow_path: Path) -> Dict[str, Any]:
        """
        Valide la structure et le contenu d'un workflow JSON
        
        Args:
            workflow_path: Chemin vers le fichier workflow
            
        Returns:
            Dictionnaire avec les résultats de validation
        """
        logger.info(f"🔍 Validation du workflow: {workflow_path}")
        
        validation_results = {
            "valid": False,
            "errors": [],
            "warnings": [],
            "metadata": {},
            "node_count": 0
        }
        
        try:
            if not workflow_path.exists():
                validation_results["errors"].append(f"Fichier non trouvé: {workflow_path}")
                return validation_results
            
            # Lire et valider le JSON
            with open(workflow_path, 'r', encoding='utf-8') as f:
                workflow_data = json.load(f)
            
            # Validation de base
            if not isinstance(workflow_data, dict):
                validation_results["errors"].append("Le workflow doit être un objet JSON")
                return validation_results
            
            # Validation des noeuds
            if "nodes" in workflow_data:
                nodes = workflow_data["nodes"]
                validation_results["node_count"] = len(nodes)
                
                # Valider chaque noeud
                for i, node_data in enumerate(nodes):
                    if not isinstance(node_data, dict):
                        validation_results["errors"].append(f"Nœud {i} invalide: doit être un dictionnaire")
                        continue
                    
                    # Validation des champs requis
                    required_fields = ["type"]  # "type" au lieu de "class_type" dans notre format
                    for field in required_fields:
                        if field not in node_data:
                            validation_results["errors"].append(f"Nœud {i}: champ '{field}' manquant")
                    
                    # Validation des types
                    if "type" in node_data:
                        node_type = node_data["type"]
                        if not isinstance(node_type, str):
                            validation_results["errors"].append(f"Nœud {i}: type doit être une chaîne")
            else:
                validation_results["errors"].append("Le workflow doit contenir une section 'nodes'")
            
            # Validation des liens
            if "links" in workflow_data:
                links = workflow_data["links"]
                for i, link in enumerate(links):
                    if not isinstance(link, list) or len(link) != 2:
                        validation_results["errors"].append(f"Lien {i} invalide: doit être [source, target]")
            
            # Extraire les métadonnées
            from datetime import datetime
            validation_results["metadata"] = {
                "file_size": workflow_path.stat().st_size if workflow_path.exists() else 0,
                "last_modified": datetime.fromtimestamp(workflow_path.stat().st_mtime).isoformat() if workflow_path.exists() else None,
                "node_types": list(set(node.get("type", "Unknown") for node in workflow_data.get("nodes", [])))
            }
            
            # Si pas d'erreurs critiques
            if not validation_results["errors"]:
                validation_results["valid"] = True
                logger.info("✅ Workflow JSON valide")
            else:
                logger.warning(f"⚠️ {len(validation_results['errors'])} erreurs trouvées")
            
            return validation_results
            
        except json.JSONDecodeError as e:
            validation_results["errors"].append(f"Erreur JSON: {e}")
        except Exception as e:
            validation_results["errors"].append(f"Erreur lecture: {e}")
        
        return validation_results
    
    def fix_workflow_links(self, workflow_path: Path, dry_run: bool = False) -> bool:
        """
        Corrige les liens dans un workflow JSON
        
        Args:
            workflow_path: Chemin vers le fichier workflow
            dry_run: Si True, ne modifie pas le fichier
            
        Returns:
            True si succès, False sinon
        """
        logger.info(f"🔧 Correction des liens dans: {workflow_path}")
        
        try:
            if not workflow_path.exists():
                logger.error(f"❌ Fichier non trouvé: {workflow_path}")
                return False
            
            # Lire le workflow
            with open(workflow_path, 'r', encoding='utf-8') as f:
                workflow_data = json.load(f)
            
            # Créer backup si pas dry run
            if not dry_run:
                backup_path = self.create_backup(workflow_path)
                if backup_path:
                    logger.info(f"💾 Backup créé: {backup_path}")
            
            corrections_made = 0
            
            # Corriger les liens
            if "links" in workflow_data:
                original_links = workflow_data["links"]
                fixed_links = []
                
                for i, link in enumerate(original_links):
                    if isinstance(link, list) and len(link) == 2:
                        # Lien déjà au bon format
                        fixed_links.append(link)
                    else:
                        # Corriger le lien au format [source, target]
                        if isinstance(link, list):
                            # Convertir [node1, node2] en {"source": "node1", "target": "node2"}
                            if len(link) == 2:
                                source_id, target_id = link
                                fixed_link = {"source": source_id, "target": target_id}
                                fixed_links.append(fixed_link)
                                corrections_made += 1
                                logger.info(f"✅ Lien {i} corrigé: {source_id} -> {target_id}")
                            else:
                                logger.warning(f"⚠️ Lien {i} format non reconnu: {link}")
                        else:
                            logger.warning(f"⚠️ Lien {i} type non reconnu: {type(link)}")
                
                # Mettre à jour les liens
                if corrections_made > 0:
                    workflow_data["links"] = fixed_links
                    
                    if not dry_run:
                        # Réécrire le fichier
                        with open(workflow_path, 'w', encoding='utf-8') as f:
                            json.dump(workflow_data, f, indent=2)
                        
                        logger.info(f"✅ {corrections_made} liens corrigés")
                        return True
                else:
                    logger.info(f"🔍 {corrections_made} liens à corriger (dry run)")
                    return corrections_made > 0
            else:
                logger.info("ℹ️ Aucun lien à corriger")
                return True
                
        except Exception as e:
            logger.error(f"❌ Erreur correction liens: {e}")
            return False
    
    def optimize_workflow(self, workflow_path: Path, dry_run: bool = False) -> bool:
        """
        Optimise la structure d'un workflow JSON
        
        Args:
            workflow_path: Chemin vers le fichier workflow
            dry_run: Si True, ne modifie pas le fichier
            
        Returns:
            True si succès, False sinon
        """
        logger.info(f"⚡ Optimisation du workflow: {workflow_path}")
        
        try:
            if not workflow_path.exists():
                logger.error(f"❌ Fichier non trouvé: {workflow_path}")
                return False
            
            # Lire le workflow
            with open(workflow_path, 'r', encoding='utf-8') as f:
                workflow_data = json.load(f)
            
            # Créer backup si pas dry run
            if not dry_run:
                backup_path = self.create_backup(workflow_path)
                if backup_path:
                    logger.info(f"💾 Backup créé: {backup_path}")
            
            optimizations_made = 0
            
            # Optimisations
            if "nodes" in workflow_data:
                nodes = workflow_data["nodes"]
                # Trier les noeuds par class_type pour optimiser l'accès
                sorted_nodes = sorted(nodes, key=lambda x: x.get("class_type", ""))
                workflow_data["nodes"] = sorted_nodes
                optimizations_made += 1
                
                # Nettoyer les métadonnées inutiles
                for node in nodes:
                    if "metadata" in node and not node["metadata"]:
                        del node["metadata"]
                        optimizations_made += 1
            
            # Supprimer les liens en double
            if "links" in workflow_data:
                original_links = workflow_data["links"]
                seen_links = set()
                unique_links = []
                
                for link in original_links:
                    if isinstance(link, list) and len(link) == 2:
                        link_key = f"{link[0]}->{link[1]}"
                        if link_key not in seen_links:
                            seen_links.add(link_key)
                            unique_links.append(link)
                        else:
                            logger.info(f"🗑️ Suppression du lien en double: {link_key}")
                            optimizations_made += 1
                    else:
                        unique_links.append(link)
                
                workflow_data["links"] = unique_links
                if len(unique_links) < len(original_links):
                    optimizations_made += len(original_links) - len(unique_links)
            
            # Mettre à jour le fichier
            if optimizations_made > 0 or not dry_run:
                with open(workflow_path, 'w', encoding='utf-8') as f:
                    json.dump(workflow_data, f, indent=2)
                
                logger.info(f"✅ {optimizations_made} optimisations appliquées")
                return True
            else:
                logger.info("ℹ️ Aucune optimisation nécessaire")
                return True
                
        except Exception as e:
            logger.error(f"❌ Erreur optimisation: {e}")
            return False
    
    def backup_workflow(self, workflow_path: Path) -> Optional[Path]:
        """
        Crée une sauvegarde d'un workflow
        
        Args:
            workflow_path: Chemin vers le fichier workflow
            
        Returns:
            Chemin vers le fichier de backup
        """
        if not workflow_path.exists():
            logger.error(f"❌ Fichier non trouvé: {workflow_path}")
            return None
        
        try:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_name = f"{workflow_path.stem}_backup_{timestamp}.json"
            backup_path = self.backup_dir / backup_name
            
            shutil.copy2(workflow_path, backup_path)
            logger.info(f"✅ Backup créé: {backup_path}")
            return backup_path
            
        except Exception as e:
            logger.error(f"❌ Erreur backup: {e}")
            return None
    
    def restore_workflow(self, backup_path: Path) -> bool:
        """
        Restaure un workflow depuis une sauvegarde
        
        Args:
            backup_path: Chemin vers le fichier de backup
            
        Returns:
            True si succès, False sinon
        """
        if not backup_path.exists():
            logger.error(f"❌ Backup non trouvé: {backup_path}")
            return False
        
        try:
            # Extraire le nom original
            original_name = backup_path.stem.split("_backup_")[0]
            original_path = backup_path.parent / f"{original_name}.json"
            
            shutil.copy2(backup_path, original_path)
            logger.info(f"✅ Workflow restauré: {original_path}")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur restauration: {e}")
            return False
    
    def create_backup(self, file_path: Path) -> Optional[Path]:
        """
        Crée une sauvegarde d'un fichier
        
        Args:
            file_path: Chemin vers le fichier à sauvegarder
            
        Returns:
            Chemin vers le fichier de backup
        """
        if not self.backup_enabled:
            return None
        
        try:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_name = f"{file_path.name}.backup_{timestamp}"
            backup_path = self.backup_dir / backup_name
            
            shutil.copy2(file_path, backup_path)
            logger.info(f"✅ Backup créé: {backup_path}")
            return backup_path
            
        except Exception as e:
            logger.error(f"❌ Erreur backup: {e}")
            return None

def main():
    """Fonction principale de l'utilitaire"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Utilitaire consolidé pour la manipulation de workflows ComfyUI",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        "workflow",
        required=True,
        help="Chemin vers le fichier workflow à traiter"
    )
    
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Valider la structure du workflow JSON"
    )
    
    parser.add_argument(
        "--fix-links",
        action="store_true",
        help="Corriger les liens dans le workflow"
    )
    
    parser.add_argument(
        "--optimize",
        action="store_true",
        help="Optimiser la structure du workflow"
    )
    
    parser.add_argument(
        "--backup",
        action="store_true",
        help="Créer une sauvegarde du workflow"
    )
    
    parser.add_argument(
        "--restore",
        help="Restaurer un workflow depuis une sauvegarde",
        metavar="BACKUP_FILE"
    )
    
    parser.add_argument(
        "--workspace",
        help="Chemin vers le workspace (défaut: répertoire courant)"
    )
    
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="Désactiver la création de backups"
    )
    
    args = parser.parse_args()
    
    # Initialiser l'utilitaire
    utils = WorkflowUtils(
        workspace_path=args.workspace,
        backup_enabled=not args.no_backup
    )
    
    success = True
    
    try:
        if args.validate:
            if not args.workflow:
                parser.error("L'option --validate requiert un fichier workflow")
                return 1
            
            results = utils.validate_workflow_json(Path(args.workflow))
            print("\n📊 RÉSULTATS DE VALIDATION:")
            print(f"✅ Valide: {results['valid']}")
            if results['errors']:
                print(f"❌ Erreurs: {len(results['errors'])}")
                for error in results['errors']:
                    print(f"  • {error}")
            if results['warnings']:
                print(f"⚠️ Avertissements: {len(results['warnings'])}")
                for warning in results['warnings']:
                    print(f"  • {warning}")
            print(f"📊 Métadonnées: {results['metadata']}")
            
        elif args.fix_links:
            success = utils.fix_workflow_links(Path(args.workflow), dry_run=False)
            
        elif args.optimize:
            success = utils.optimize_workflow(Path(args.workflow), dry_run=False)
            
        elif args.backup:
            backup_path = utils.backup_workflow(Path(args.workflow))
            if backup_path:
                print(f"✅ Backup créé: {backup_path}")
            else:
                print("❌ Échec du backup")
                success = False
            
        elif args.restore:
            success = utils.restore_workflow(Path(args.restore))
            if success:
                print(f"✅ Workflow restauré: {args.restore}")
            else:
                print("❌ Échec de la restauration")
                success = False
            
        else:
            parser.print_help()
            return 0 if success else 1
    
    except KeyboardInterrupt:
        print("\n⏹️ Opération interrompue par l'utilisateur")
        return 130
    except Exception as e:
        print(f"\n❌ Erreur: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(main())