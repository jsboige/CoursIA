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


# ---------------------------------------------------------------------------
# Resolution de la configuration OpenAI / OpenRouter
# ---------------------------------------------------------------------------
# La cle du module est une cle OpenRouter : elle n'ouvre pas les services
# OpenAI natifs, et le client `openai` doit pointer sur l'adresse OpenRouter.
# Sous Colab il n'y a pas de fichier .env : la cle y est un Secret de notebook,
# lu par `google.colab.userdata`.

OPENROUTER_BASE_URL = 'https://openrouter.ai/api/v1'

# Modeles par defaut, par fournisseur. Ce ne sont pas des secrets : le nom du
# modele se lit dans le code, la cle jamais. Les modeles OpenRouter listes sont
# ouverts sur la cle du module (recette verifiee, issue #23264).
DEFAULT_OPENAI_MODEL = 'gpt-5-mini'
DEFAULT_OPENAI_REASONING_MODEL = 'gpt-5.6-sol'
DEFAULT_OPENROUTER_MODEL = 'qwen/qwen3.8-flash'
DEFAULT_OPENROUTER_REASONING_MODEL = 'deepseek/deepseek-v4.1-flash'

# Noms de Secrets Colab a essayer, dans l'ordre.
COLAB_SECRET_NAMES = ('OPENAI_API_KEY', 'OPENROUTER_API_KEY')

_MISSING_KEY_HELP = """Aucune cle d'API n'a ete trouvee.

En local (Jupyter, VS Code) :
  1. copiez MyIA.AI.Notebooks/GenAI/.env.example en .env, dans le dossier du
     carnet ou dans un dossier parent ;
  2. remplacez-y la valeur de OPENAI_API_KEY par la cle fournie en cours ;
  3. relancez la cellule.

Sous Google Colab, il n'y a pas de fichier .env : utilisez les Secrets du
carnet (icone cle dans la barre de gauche, ou onglet Secrets) :
  1. ajoutez un secret nomme OPENAI_API_KEY — ou OPENROUTER_API_KEY si la cle
     qui vous a ete remise est une cle OpenRouter ;
  2. basculez l'interrupteur « Acces au notebook » sur ON ;
  3. relancez la cellule, sans redemarrer la session.

Ne collez jamais une cle dans une cellule : le carnet partirait avec elle dans
un commit, et le depot est public."""


class MissingApiKeyError(RuntimeError):
    """Aucune cle d'API exploitable, ni dans l'environnement ni dans les Secrets."""


class OpenAIConfig:
    """Configuration resolue du client `openai`.

    Attributs :
        api_key        : la cle elle-meme (jamais journalisee, jamais affichee).
        base_url       : adresse a laquelle parler ; None = adresse OpenAI.
        model          : modele par defaut du carnet.
        reasoning_model: modele de raisonnement, quand le carnet en utilise un.
        provider       : 'openai' ou 'openrouter'.
        key_source     : d'ou vient la cle, pour diagnostiquer sans la montrer.
    """

    __slots__ = ('api_key', 'base_url', 'model', 'reasoning_model',
                 'provider', 'key_source')

    def __init__(self, api_key, base_url, model, reasoning_model,
                 provider, key_source):
        self.api_key = api_key
        self.base_url = base_url
        self.model = model
        self.reasoning_model = reasoning_model
        self.provider = provider
        self.key_source = key_source

    @property
    def masked_key(self):
        """Cle masquee, sure a afficher dans une sortie de cellule."""
        if not self.api_key:
            return '<absente>'
        if len(self.api_key) <= 8:
            return '*' * len(self.api_key)
        return '%s...%s' % (self.api_key[:4], self.api_key[-4:])

    def __repr__(self):
        return ('OpenAIConfig(provider=%r, base_url=%r, model=%r, '
                'reasoning_model=%r, key_source=%r, api_key=%r)'
                % (self.provider, self.base_url, self.model,
                   self.reasoning_model, self.key_source, self.masked_key))


def is_colab():
    """Vrai si le code tourne dans un notebook Google Colab."""
    try:
        import google.colab  # noqa: F401
    except Exception:
        return False
    return True


def read_colab_secret(name):
    """Lit un Secret de notebook Colab ; None hors Colab ou si absent.

    La valeur n'est jamais journalisee par cette fonction.
    """
    try:
        from google.colab import userdata
    except Exception:
        return None
    try:
        value = userdata.get(name)
    except Exception:
        # Secret absent : Colab leve SecretNotFoundError, dont le message
        # cite le nom du secret — ce qui est sans danger — mais on prefere
        # un None silencieux, l'appelant rend un message unique et complet.
        return None
    if isinstance(value, str) and value.strip():
        return value.strip()
    return None


def _read_key(name):
    """Cherche une cle dans l'environnement puis dans les Secrets Colab."""
    value = os.getenv(name)
    if value and value.strip():
        return value.strip(), 'env:%s' % name
    value = read_colab_secret(name)
    if value:
        return value, 'colab:%s' % name
    return None, None


def resolve_openai_config(required=True, env=None):
    """Resout la configuration du client `openai` selon la cle disponible.

    Ordre : OPENAI_API_KEY (environnement, puis Secret Colab), puis
    OPENROUTER_API_KEY (environnement, puis Secret Colab). Une cle OpenRouter
    implique l'adresse OpenRouter et un modele ouvert sur cette cle.

    Args:
        required: si True, leve MissingApiKeyError quand aucune cle n'existe.
        env: dictionnaire a lire au lieu de os.environ (utile aux tests).

    Returns:
        OpenAIConfig

    Raises:
        MissingApiKeyError: aucune cle et required=True.
    """
    if env is not None:
        api_key = (env.get('OPENAI_API_KEY') or '').strip()
        source = 'env:OPENAI_API_KEY'
        if not api_key:
            api_key = (env.get('OPENROUTER_API_KEY') or '').strip()
            source = 'env:OPENROUTER_API_KEY'
        if not api_key:
            api_key, source = None, None
        openrouter = source == 'env:OPENROUTER_API_KEY'
        base_url = env.get('OPENAI_BASE_URL')
        model_env = env.get('OPENAI_MODEL')
        reasoning_env = env.get('OPENAI_REASONING_MODEL')
    else:
        api_key, source = _read_key('OPENAI_API_KEY')
        openrouter = False
        if not api_key:
            api_key, source = _read_key('OPENROUTER_API_KEY')
            openrouter = source is not None
        base_url = os.getenv('OPENAI_BASE_URL')
        model_env = os.getenv('OPENAI_MODEL')
        reasoning_env = os.getenv('OPENAI_REASONING_MODEL')

    if not api_key:
        if required:
            raise MissingApiKeyError(_MISSING_KEY_HELP)
        return None

    if base_url:
        provider = 'openrouter' if 'openrouter' in base_url.lower() else 'openai'
    elif openrouter:
        base_url = OPENROUTER_BASE_URL
        provider = 'openrouter'
    else:
        base_url = None
        provider = 'openai'

    if provider == 'openrouter':
        model_default = DEFAULT_OPENROUTER_MODEL
        reasoning_default = DEFAULT_OPENROUTER_REASONING_MODEL
    else:
        model_default = DEFAULT_OPENAI_MODEL
        reasoning_default = DEFAULT_OPENAI_REASONING_MODEL

    return OpenAIConfig(
        api_key=api_key,
        base_url=base_url,
        model=model_env or model_default,
        reasoning_model=reasoning_env or reasoning_default,
        provider=provider,
        key_source=source,
    )


def apply_openai_environment(config=None, required=True):
    """Pose la configuration resolue dans l'environnement du processus.

    Deux contrats distincts, selon que `config` est fournie ou non :

    * **`config=None`** — la configuration est *resolue* (environnement puis
      Secrets Colab) puis *posee* : chaque variable absente de l'environnement
      est ecrite (`setdefault`). Une valeur deja exportee n'est jamais ecrasee,
      l'auteur du carnet a pu la poser deliberement.
    * **`config` explicite** — l'appelant affirme cette configuration : elle
      *remplace* l'environnement. Les quatre variables sont ecrites, et
      `OPENAI_BASE_URL` est **retiree** quand la configuration ne porte pas de
      `base_url` — sinon une adresse OpenRouter residuelle re-route
      silencieusement une cle OpenAI native.

    Ce que le client `openai` 2.x lit tout seul : `OPENAI_API_KEY` et
    `OPENAI_BASE_URL`. Il ne lit **pas** `OPENAI_MODEL` : le nom du modele
    reste un argument d'appel, `client.chat.completions.create(model=cfg.model)`.
    Poser `OPENAI_MODEL` sert a ce que le carnet le relise (`os.getenv`), pas a
    le faire consommer par le client.

    Returns:
        OpenAIConfig (ou None si required=False et aucune cle).
    """
    explicit = config is not None
    if config is None:
        config = resolve_openai_config(required=required)
    if config is None:
        return None

    variables = (
        ('OPENAI_API_KEY', config.api_key),
        ('OPENAI_MODEL', config.model),
        ('OPENAI_REASONING_MODEL', config.reasoning_model),
    )
    for name, value in variables:
        if explicit:
            os.environ[name] = value
        else:
            os.environ.setdefault(name, value)

    if config.base_url:
        if explicit:
            os.environ['OPENAI_BASE_URL'] = config.base_url
        else:
            os.environ.setdefault('OPENAI_BASE_URL', config.base_url)
    elif explicit:
        # Configuration sans base_url : l'adresse residuelle doit partir,
        # sinon la cle native part chez le fournisseur precedent.
        os.environ.pop('OPENAI_BASE_URL', None)
    return config

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
__all__ = ['setup_genai_logging', 'load_genai_config', 'validate_apis', 'save_generation_result',
           'is_colab', 'read_colab_secret', 'resolve_openai_config',
           'apply_openai_environment', 'OpenAIConfig', 'MissingApiKeyError',
           'OPENROUTER_BASE_URL', 'DEFAULT_OPENROUTER_MODEL']
