
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
    sanitized = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]', '', sanitized)
    
    return sanitized
