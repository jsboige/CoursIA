#!/usr/bin/env python3
"""
Script de correction d'encodage HTML pour SymbolicAI Argument Analysis
Corrige les entités HTML qui cassent le parsing XML dans PropositionalLogicAgent
"""

import html
import re
import logging
from pathlib import Path

def setup_logging():
    """Configure le logging pour le script."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s [%(levelname)s] %(message)s',
        datefmt='%H:%M:%S'
    )
    return logging.getLogger("HTMLEncodingFix")

def decode_html_entities(text: str) -> str:
    """Décode les entités HTML dans un texte."""
    if not text:
        return text
    
    # Décoder les entités HTML standard
    decoded = html.unescape(text)
    
    # Corrections spécifiques supplémentaires si nécessaire
    replacements = {
        '&#x27;': "'",  # Apostrophe
        '&#39;': "'",   # Apostrophe alternative
        '&quot;': '"',  # Guillemets
        '&amp;': '&',   # Esperluette
        '&lt;': '<',    # Plus petit que
        '&gt;': '>',    # Plus grand que
    }
    
    for entity, replacement in replacements.items():
        decoded = decoded.replace(entity, replacement)
    
    return decoded

def create_text_sanitizer_function() -> str:
    """Crée une fonction Python pour sanitiser le texte."""
    return '''
def sanitize_text_for_xml(text: str) -> str:
    """
    Sanitise un texte pour éviter les erreurs de parsing XML.
    Décode les entités HTML et nettoie les caractères problématiques.
    """
    import html
    import re
    
    if not text:
        return text
    
    # Décoder les entités HTML
    sanitized = html.unescape(text)
    
    # Corrections spécifiques
    replacements = {
        '&#x27;': "'",
        '&#39;': "'", 
        '&quot;': '"',
        '&amp;': '&',
        '&lt;': '<',
        '&gt;': '>',
    }
    
    for entity, replacement in replacements.items():
        sanitized = sanitized.replace(entity, replacement)
    
    # Supprimer les caractères de contrôle qui peuvent poser problème
    sanitized = re.sub(r'[\\x00-\\x08\\x0B\\x0C\\x0E-\\x1F\\x7F]', '', sanitized)
    
    return sanitized
'''

def main():
    """Fonction principale du script."""
    logger = setup_logging()
    logger.info("🔧 === CORRECTION ENCODAGE HTML POUR ARGUMENT ANALYSIS ===")
    
    # Créer le fichier de fonction sanitizer
    sanitizer_path = Path("text_sanitizer.py")
    
    try:
        with open(sanitizer_path, 'w', encoding='utf-8') as f:
            f.write(create_text_sanitizer_function())
        
        logger.info(f"✅ Fonction sanitizer créée: {sanitizer_path}")
        
        # Test de la fonction
        test_text = "D&#x27;un côté, les réseaux sociaux permettent de rester en contact avec nos proches."
        sanitized = decode_html_entities(test_text)
        
        logger.info(f"📋 Test d'encodage:")
        logger.info(f"   Avant: {test_text}")
        logger.info(f"   Après: {sanitized}")
        
        if "&#x27;" not in sanitized and "'" in sanitized:
            logger.info("✅ Décodage HTML opérationnel !")
        else:
            logger.warning("⚠️ Décodage HTML peut-être incomplet")
        
        logger.info("📝 Instructions d'intégration:")
        logger.info("   1. Importer: from text_sanitizer import sanitize_text_for_xml")
        logger.info("   2. Utiliser: clean_text = sanitize_text_for_xml(raw_text)")
        logger.info("   3. Appliquer avant tout parsing XML dans PropositionalLogicAgent")
        
        return True
        
    except Exception as e:
        logger.error(f"❌ Erreur lors de la création du sanitizer: {e}")
        return False

if __name__ == "__main__":
    success = main()
    if success:
        print("\\n🎉 Correction d'encodage HTML créée avec succès !")
    else:
        print("\\n❌ Échec création correction d'encodage")