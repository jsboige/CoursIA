#!/usr/bin/env python3
"""
Script de réparation automatisée des notebooks Jupyter corrompus
🚨 RÉPARATION URGENTE - Corruption Notebooks Agents SymbolicAI

Ce script répare les notebooks corrompus qui ont perdu leur structure JSON
et ne contiennent plus que le contenu brut sans métadonnées.
"""

import json
import os
import logging
import re
from typing import Dict, List, Any, Optional
from pathlib import Path

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(name)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("NotebookRepair")

class NotebookRepairTool:
    """Outil de réparation des notebooks Jupyter corrompus."""
    
    def __init__(self):
        self.repaired_count = 0
        self.failed_count = 0
        
        # Métadonnées standard pour notebooks Python
        self.standard_metadata = {
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
    
    def analyze_raw_content(self, raw_content: str) -> List[Dict[str, Any]]:
        """
        Parse le contenu brut pour identifier les cellules et leur type.
        """
        logger.info("Analyse du contenu brut pour identifier les cellules...")
        
        cells = []
        lines = raw_content.split('\n')
        current_cell = None
        current_lines = []
        
        i = 0
        while i < len(lines):
            line = lines[i].rstrip()
            
            # Détection de cellule code Python (commence par # %%)
            if line.startswith('# %%'):
                # Sauvegarder la cellule précédente
                if current_cell is not None:
                    current_cell['source'] = current_lines
                    cells.append(current_cell)
                
                # Créer nouvelle cellule code
                current_cell = {
                    "cell_type": "code",
                    "execution_count": None,
                    "id": f"cell-{len(cells)+1}",
                    "metadata": {},
                    "outputs": []
                }
                current_lines = [line]
                
            # Détection de cellule markdown (commence par #)
            elif line.startswith('# ') and not line.startswith('# %%') and current_cell is None:
                current_cell = {
                    "cell_type": "markdown",
                    "id": f"cell-{len(cells)+1}", 
                    "metadata": {}
                }
                current_lines = [line[2:]]  # Enlever le "# "
                
            # Détection de séparateurs markdown (##, ###, etc.)
            elif re.match(r'^#{1,6}\s', line) and current_cell and current_cell['cell_type'] == 'markdown':
                current_lines.append(line[line.find(' ')+1:] if ' ' in line else line)
                
            else:
                # Continuer la cellule courante
                if current_cell is None:
                    # Créer une cellule markdown par défaut
                    current_cell = {
                        "cell_type": "markdown",
                        "id": f"cell-{len(cells)+1}",
                        "metadata": {}
                    }
                    current_lines = []
                
                current_lines.append(line)
            
            i += 1
        
        # Sauvegarder la dernière cellule
        if current_cell is not None:
            current_cell['source'] = current_lines
            cells.append(current_cell)
        
        logger.info(f"✅ Analyse terminée: {len(cells)} cellules identifiées")
        for i, cell in enumerate(cells):
            cell_type = cell['cell_type']
            source_preview = str(cell['source'][:1])[:50] if cell['source'] else "vide"
            logger.debug(f"  Cellule {i+1}: {cell_type} - {source_preview}...")
            
        return cells
    
    def create_valid_notebook_structure(self, raw_content: str) -> Dict[str, Any]:
        """
        Crée une structure de notebook Jupyter valide à partir du contenu brut.
        """
        logger.info("🔧 Construction de la structure JSON du notebook...")
        
        # Parser le contenu pour identifier les cellules
        cells = self.analyze_raw_content(raw_content)
        
        # Créer la structure complète du notebook
        notebook_structure = {
            "cells": cells,
            "metadata": self.standard_metadata,
            "nbformat": 4,
            "nbformat_minor": 2
        }
        
        logger.info("✅ Structure JSON du notebook construite avec succès")
        logger.debug(f"  📊 {len(cells)} cellules, métadonnées complètes, nbformat 4.2")
        
        return notebook_structure
    
    def repair_notebook(self, notebook_path: str) -> bool:
        """
        Répare un notebook corrompu en restaurant sa structure JSON.
        
        Args:
            notebook_path: Chemin vers le notebook à réparer
            
        Returns:
            True si la réparation a réussi, False sinon
        """
        logger.info(f"🚨 DÉBUT RÉPARATION: {notebook_path}")
        
        try:
            # Lire le contenu brut
            logger.info("📖 Lecture du fichier corrompu...")
            with open(notebook_path, 'r', encoding='utf-8') as f:
                raw_content = f.read()
            
            if not raw_content.strip():
                logger.error("❌ Fichier vide ou illisible")
                return False
            
            # Vérifier si c'est vraiment corrompu (pas de structure JSON)
            try:
                json.loads(raw_content)
                logger.info("ℹ️ Le fichier semble déjà avoir une structure JSON valide")
                return True
            except json.JSONDecodeError:
                logger.info("✅ Confirmation: fichier corrompu (pas de JSON), réparation nécessaire")
            
            # Créer la structure valide
            notebook_structure = self.create_valid_notebook_structure(raw_content)
            
            # Créer une sauvegarde
            backup_path = f"{notebook_path}.backup"
            logger.info(f"💾 Création sauvegarde: {backup_path}")
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(raw_content)
            
            # Sauvegarder le notebook réparé
            logger.info("💿 Sauvegarde du notebook réparé...")
            with open(notebook_path, 'w', encoding='utf-8') as f:
                json.dump(notebook_structure, f, indent=2, ensure_ascii=False)
            
            # Validation
            logger.info("🔍 Validation de la réparation...")
            with open(notebook_path, 'r', encoding='utf-8') as f:
                validated_content = json.load(f)
            
            # Vérifier les clés essentielles
            required_keys = ['cells', 'metadata', 'nbformat', 'nbformat_minor']
            for key in required_keys:
                if key not in validated_content:
                    raise ValueError(f"Clé manquante après réparation: {key}")
            
            # Vérifier les métadonnées
            if 'kernelspec' not in validated_content['metadata']:
                raise ValueError("Métadonnées kernelspec manquantes")
            if 'language_info' not in validated_content['metadata']:
                raise ValueError("Métadonnées language_info manquantes")
                
            logger.info("🎉 ✅ RÉPARATION RÉUSSIE!")
            logger.info(f"  📊 {len(validated_content['cells'])} cellules restaurées")
            logger.info(f"  🔧 Métadonnées Python 3 ajoutées")
            logger.info(f"  📝 Format nbformat {validated_content['nbformat']}.{validated_content['nbformat_minor']}")
            
            self.repaired_count += 1
            return True
            
        except Exception as e:
            logger.error(f"❌ ÉCHEC RÉPARATION: {e}")
            self.failed_count += 1
            return False
    
    def repair_multiple_notebooks(self, notebook_paths: List[str]) -> Dict[str, bool]:
        """
        Répare plusieurs notebooks et retourne un rapport.
        """
        logger.info(f"🚀 DÉBUT RÉPARATION EN LOT: {len(notebook_paths)} notebooks")
        
        results = {}
        for path in notebook_paths:
            if os.path.exists(path):
                results[path] = self.repair_notebook(path)
            else:
                logger.error(f"❌ Fichier introuvable: {path}")
                results[path] = False
                self.failed_count += 1
        
        # Rapport final
        logger.info(f"📊 RAPPORT FINAL:")
        logger.info(f"  ✅ Réparés avec succès: {self.repaired_count}")
        logger.info(f"  ❌ Échecs: {self.failed_count}")
        logger.info(f"  📈 Taux de réussite: {(self.repaired_count/(self.repaired_count+self.failed_count)*100):.1f}%")
        
        return results

def main():
    """Fonction principale du script de réparation."""
    logger.info("🚨 SCRIPT DE RÉPARATION URGENTE - Notebooks Agents SymbolicAI")
    
    # Liste des notebooks corrompus identifiés
    corrupted_notebooks = [
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb", 
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb"
    ]
    
    # Créer l'outil de réparation
    repair_tool = NotebookRepairTool()
    
    # Exécuter la réparation
    results = repair_tool.repair_multiple_notebooks(corrupted_notebooks)
    
    # Afficher les résultats détaillés
    logger.info("📋 DÉTAILS DES RÉSULTATS:")
    for notebook_path, success in results.items():
        status = "✅ RÉPARÉ" if success else "❌ ÉCHEC"
        logger.info(f"  {status}: {os.path.basename(notebook_path)}")
    
    return repair_tool.repaired_count == len(corrupted_notebooks)

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)