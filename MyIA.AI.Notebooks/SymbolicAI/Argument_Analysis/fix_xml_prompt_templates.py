#!/usr/bin/env python3
"""
Script de correction des templates XML/HTML dans les prompts Semantic Kernel

PROBLÈME IDENTIFIÉ :
- Les prompts BNF Tweety contiennent des caractères HTML échappés (=&gt; au lieu de =>)
- Semantic Kernel ne peut pas parser ces prompts comme XML valide
- Erreur : "not well-formed (invalid token): line X, column Y"

SOLUTION :
- Identifier les notebooks contenant les définitions PropositionalLogicAgent 
- Corriger les échappements HTML dans les prompts BNF
- Créer des versions corrigées avec suffix -xml-fixed

Auteur : Mission SDDD - Validation SymbolicAI Argument Analysis
Date : 2025-10-03
"""

import re
import html
import os
import json
from pathlib import Path
import logging

# Configuration du logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def fix_xml_prompt_templates():
    """
    Corrige les templates de prompts XML malformés dans les notebooks
    """
    
    # Liste des notebooks à analyser (ceux contenant PropositionalLogicAgent)
    notebook_paths = [
        "Argument_Analysis_Agentic-2-pl_agent.ipynb",
        # Ajouter d'autres notebooks si nécessaire
    ]
    
    total_fixes = 0
    
    for notebook_name in notebook_paths:
        notebook_path = Path(notebook_name)
        
        if not notebook_path.exists():
            logger.warning(f"📁 Notebook non trouvé : {notebook_path}")
            continue
            
        logger.info(f"🔍 Analyse du notebook : {notebook_path}")
        
        try:
            # Lecture du notebook
            with open(notebook_path, 'r', encoding='utf-8') as f:
                notebook = json.load(f)
            
            notebook_fixes = 0
            
            # Parcours des cellules
            for cell_idx, cell in enumerate(notebook.get('cells', [])):
                if cell.get('cell_type') == 'code':
                    # Analyse du source de la cellule
                    source_lines = cell.get('source', [])
                    modified = False
                    
                    for line_idx, line in enumerate(source_lines):
                        original_line = line
                        
                        # Pattern 1: Correction des échappements HTML dans BNF
                        # Remplace =&gt; par =>
                        if '=&gt;' in line:
                            line = line.replace('=&gt;', '=>')
                            modified = True
                            logger.info(f"  🔧 Cellule {cell_idx}, ligne {line_idx}: =&gt; → =>")
                        
                        # Pattern 2: Correction des &lt; et &gt; 
                        if '&lt;' in line:
                            line = line.replace('&lt;', '<')
                            modified = True
                            logger.info(f"  🔧 Cellule {cell_idx}, ligne {line_idx}: &lt; → <")
                        
                        if '&gt;' in line and '=&gt;' not in original_line:  # Éviter double correction
                            line = line.replace('&gt;', '>')
                            modified = True
                            logger.info(f"  🔧 Cellule {cell_idx}, ligne {line_idx}: &gt; → >")
                        
                        # Pattern 3: Correction des &quot;
                        if '&quot;' in line:
                            line = line.replace('&quot;', '"')
                            modified = True
                            logger.info(f"  🔧 Cellule {cell_idx}, ligne {line_idx}: &quot; → \"")
                        
                        # Pattern 4: Correction des &amp; (sauf s'il précède gt, lt, quot)
                        if '&amp;' in line and not re.search(r'&amp;(gt|lt|quot|apos);', line):
                            line = line.replace('&amp;', '&')
                            modified = True
                            logger.info(f"  🔧 Cellule {cell_idx}, ligne {line_idx}: &amp; → &")
                        
                        source_lines[line_idx] = line
                        
                        if modified:
                            notebook_fixes += 1
            
            # Sauvegarde si des corrections ont été apportées
            if notebook_fixes > 0:
                # Backup de l'original
                backup_path = notebook_path.with_suffix('.ipynb.backup')
                with open(backup_path, 'w', encoding='utf-8') as f:
                    json.dump(notebook, f, indent=2, ensure_ascii=False)
                logger.info(f"💾 Sauvegarde créée : {backup_path}")
                
                # Sauvegarde des corrections
                fixed_path = notebook_path.with_stem(notebook_path.stem + '_xml-fixed')
                with open(fixed_path, 'w', encoding='utf-8') as f:
                    json.dump(notebook, f, indent=2, ensure_ascii=False)
                
                logger.info(f"✅ {notebook_fixes} corrections appliquées dans : {fixed_path}")
                total_fixes += notebook_fixes
            else:
                logger.info(f"ℹ️  Aucune correction nécessaire dans {notebook_name}")
                
        except Exception as e:
            logger.error(f"❌ Erreur lors du traitement de {notebook_path} : {e}")
            continue
    
    return total_fixes

def validate_fix_effectiveness():
    """
    Valide l'efficacité des corrections en recherchant les patterns problématiques restants
    """
    logger.info("🔍 Validation de l'efficacité des corrections...")
    
    # Recherche de patterns problématiques dans les notebooks corrigés
    problematic_patterns = [
        r'=&gt;',  # HTML escaped =>
        r'&lt;',   # HTML escaped <
        r'&gt;',   # HTML escaped > (hors contexte =&gt;)
        r'&quot;', # HTML escaped "
    ]
    
    fixed_notebooks = list(Path('.').glob('*_xml-fixed.ipynb'))
    
    if not fixed_notebooks:
        logger.warning("⚠️  Aucun notebook corrigé trouvé")
        return False
    
    issues_found = 0
    
    for notebook_path in fixed_notebooks:
        logger.info(f"📋 Validation : {notebook_path}")
        
        try:
            with open(notebook_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            for pattern in problematic_patterns:
                matches = re.findall(pattern, content)
                if matches:
                    logger.warning(f"  ⚠️  Pattern restant trouvé : {pattern} ({len(matches)} occurrences)")
                    issues_found += len(matches)
        
        except Exception as e:
            logger.error(f"❌ Erreur validation {notebook_path} : {e}")
    
    if issues_found == 0:
        logger.info("✅ Validation réussie : Aucun pattern problématique restant")
        return True
    else:
        logger.warning(f"⚠️  {issues_found} patterns problématiques restants détectés")
        return False

def main():
    """Point d'entrée principal"""
    logger.info("🚀 Démarrage du script de correction XML/HTML dans les prompts")
    logger.info("=" * 70)
    
    # Étape 1 : Correction des templates
    total_fixes = fix_xml_prompt_templates()
    
    logger.info("=" * 70)
    
    if total_fixes > 0:
        logger.info(f"🎉 {total_fixes} corrections totales appliquées")
        
        # Étape 2 : Validation
        validation_success = validate_fix_effectiveness()
        
        if validation_success:
            logger.info("✅ SUCCÈS COMPLET : Corrections appliquées et validées")
        else:
            logger.warning("⚠️  SUCCÈS PARTIEL : Corrections appliquées mais patterns restants détectés")
            
    else:
        logger.info("ℹ️  Aucune correction nécessaire")
    
    logger.info("=" * 70)
    logger.info("🏁 Script terminé")
    
    return total_fixes > 0

if __name__ == "__main__":
    main()