#!/usr/bin/env python3
"""
GenAI Helpers - Utilitaires Phase 2 CoursIA
Fonctionnalites communes pour tous les modules GenAI Images
"""

import os
import json
import base64
import asyncio
from typing import Dict, List, Optional, Any
from pathlib import Path
from datetime import datetime
import logging

# Configuration logging
def setup_genai_logging(level="INFO"):
    """Configuration logging standardisee GenAI"""
    logger = logging.getLogger('genai_coursia')
    logger.setLevel(getattr(logging, level))
    
    if not logger.handlers:
        handler = logging.StreamHandler()
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        handler.setFormatter(formatter)
        logger.addHandler(handler)
    
    return logger

# Configuration environnement
def load_genai_config():
    """Chargement configuration GenAI depuis .env"""
    from dotenv import load_dotenv
    
    env_file = Path.cwd() / '.env'
    if env_file.exists():
        load_dotenv(env_file)
        return True
    return False

# Validation APIs
def validate_apis():
    """Validation des APIs disponibles"""
    status = {
        'openrouter': bool(os.getenv('OPENROUTER_API_KEY')),
        'openai': bool(os.getenv('OPENAI_API_KEY')),
        'docker_enabled': os.getenv('DOCKER_ENABLED', 'false').lower() == 'true'
    }
    return status

# Sauvegarde resultats
def save_generation_result(image_data, metadata, output_dir="outputs/generated"):
    """Sauvegarde standard resultats generation"""
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    
    # Sauvegarde image si base64
    if isinstance(image_data, str):
        image_path = output_path / f"genai_image_{timestamp}.png"
        with open(image_path, 'wb') as f:
            f.write(base64.b64decode(image_data))
    
    # Sauvegarde metadonnees
    metadata_path = output_path / f"genai_metadata_{timestamp}.json"
    with open(metadata_path, 'w') as f:
        json.dump(metadata, f, indent=2, default=str)
    
    return str(image_path), str(metadata_path)

# Export principales fonctions
__all__ = ['setup_genai_logging', 'load_genai_config', 'validate_apis', 'save_generation_result']
