#!/usr/bin/env python3
"""
Script de réparation rapide des notebooks Jupyter - Métadonnées manquantes
🚨 CORRECTION URGENTE - Notebooks corrompus sans métadonnées racine
"""

import json
import os
import logging
from pathlib import Path

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(name)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("NotebookMetadataFix")

def fix_notebook_metadata(notebook_path: str) -> bool:
    """
    Répare un notebook en ajoutant les métadonnées manquantes à la racine.
    
    Args:
        notebook_path: Chemin vers le notebook à réparer
        
    Returns:
        True si la réparation a réussi, False sinon
    """
    logger.info(f"🚨 RÉPARATION: {notebook_path}")
    
    try:
        # Lire le fichier JSON
        with open(notebook_path, 'r', encoding='utf-8') as f:
            notebook_data = json.load(f)
        
        logger.info("✅ Fichier JSON chargé avec succès")
        
        # Vérifier les clés manquantes
        missing_keys = []
        if 'metadata' not in notebook_data:
            missing_keys.append('metadata')
        if 'nbformat' not in notebook_data:
            missing_keys.append('nbformat')
        if 'nbformat_minor' not in notebook_data:
            missing_keys.append('nbformat_minor')
        
        if not missing_keys:
            logger.info("ℹ️ Le notebook semble déjà avoir toutes les clés requises")
            return True
        
        logger.info(f"🔍 Clés manquantes détectées: {missing_keys}")
        
        # Créer une sauvegarde
        backup_path = f"{notebook_path}.backup"
        with open(backup_path, 'w', encoding='utf-8') as f:
            json.dump(notebook_data, f, indent=2, ensure_ascii=False)
        logger.info(f"💾 Sauvegarde créée: {backup_path}")
        
        # Ajouter les métadonnées manquantes
        if 'metadata' not in notebook_data:
            notebook_data['metadata'] = {
                "kernelspec": {
                    "display_name": "Python 3",
                    "language": "python",
                    "name": "python3"
                },
                "language_info": {
                    "codemirror_mode": {"name": "ipython", "version": 3},
                    "file_extension": ".py",
                    "mimetype": "text/x-python",
                    "name": "python",
                    "nbconvert_exporter": "python",
                    "pygments_lexer": "ipython3",
                    "version": "3.8.0"
                }
            }
            logger.info("✅ Métadonnées 'metadata' ajoutées")
        
        if 'nbformat' not in notebook_data:
            notebook_data['nbformat'] = 4
            logger.info("✅ Clé 'nbformat' ajoutée")
        
        if 'nbformat_minor' not in notebook_data:
            notebook_data['nbformat_minor'] = 2
            logger.info("✅ Clé 'nbformat_minor' ajoutée")
        
        # Sauvegarder le notebook réparé
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(notebook_data, f, indent=2, ensure_ascii=False)
        
        logger.info("💿 Notebook réparé et sauvegardé")
        
        # Validation finale
        with open(notebook_path, 'r', encoding='utf-8') as f:
            validated_data = json.load(f)
        
        # Vérifier toutes les clés essentielles
        required_keys = ['cells', 'metadata', 'nbformat', 'nbformat_minor']
        for key in required_keys:
            if key not in validated_data:
                raise ValueError(f"Clé manquante après réparation: {key}")
        
        # Vérifier les sous-clés de metadata
        if 'kernelspec' not in validated_data['metadata']:
            raise ValueError("Sous-clé 'kernelspec' manquante dans metadata")
        if 'language_info' not in validated_data['metadata']:
            raise ValueError("Sous-clé 'language_info' manquante dans metadata")
        
        logger.info("🎉 ✅ RÉPARATION RÉUSSIE!")
        logger.info(f"  📊 {len(validated_data['cells'])} cellules présentes")
        logger.info(f"  🔧 Métadonnées complètes ajoutées")
        logger.info(f"  📝 Format: nbformat {validated_data['nbformat']}.{validated_data['nbformat_minor']}")
        
        return True
        
    except Exception as e:
        logger.error(f"❌ ÉCHEC RÉPARATION: {e}")
        return False

def main():
    """Fonction principale du script."""
    logger.info("🚨 SCRIPT RÉPARATION URGENTE - Métadonnées Notebooks Manquantes")
    
    # Liste des notebooks corrompus
    notebooks = [
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb"
    ]
    
    # Compteurs
    success_count = 0
    total_count = len(notebooks)
    
    # Réparer chaque notebook
    for notebook_path in notebooks:
        if not os.path.exists(notebook_path):
            logger.error(f"❌ Fichier introuvable: {notebook_path}")
            continue
            
        if fix_notebook_metadata(notebook_path):
            success_count += 1
            logger.info(f"✅ SUCCÈS: {os.path.basename(notebook_path)}")
        else:
            logger.error(f"❌ ÉCHEC: {os.path.basename(notebook_path)}")
        
        logger.info("")  # Ligne vide pour séparer
    
    # Rapport final
    logger.info("📊 RAPPORT FINAL:")
    logger.info(f"  ✅ Réparés avec succès: {success_count}/{total_count}")
    logger.info(f"  ❌ Échecs: {total_count - success_count}/{total_count}")
    
    if success_count == total_count:
        logger.info("🎉 🏆 MISSION ACCOMPLIE - TOUS LES NOTEBOOKS RÉPARÉS! 🏆 🎉")
        return True
    else:
        logger.error("⚠️ Certains notebooks n'ont pas pu être réparés")
        return False

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)