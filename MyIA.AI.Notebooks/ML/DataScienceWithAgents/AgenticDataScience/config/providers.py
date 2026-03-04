"""
Configuration Multi-Provider pour AgenticDataScience.

Ce module fournit une couche d'abstraction permettant d'utiliser
n'importe quel LLM compatible OpenAI via LiteLLM.
"""

from enum import Enum
from typing import Optional, ClassVar
from pydantic import BaseModel
from pydantic_settings import BaseSettings
from pathlib import Path
import os

# Chemin absolu vers le fichier .env (dans le répertoire parent du module config)
_ENV_FILE = Path(__file__).parent.parent / ".env"


class ProviderType(Enum):
    """Providers LLM supportés."""
    GEMINI = "gemini"
    OPENAI = "openai"
    OPENROUTER = "openrouter"
    VLLM = "vllm"
    LMSTUDIO = "lmstudio"


class ProviderConfig(BaseModel):
    """Configuration d'un provider LLM."""
    provider: ProviderType
    model: str
    api_key: Optional[str] = None
    base_url: Optional[str] = None

    # Defaults par provider
    DEFAULTS: ClassVar[dict] = {
        ProviderType.GEMINI: {
            "model": "gemini-3.1-pro",
            "base_url": "https://generativelanguage.googleapis.com/v1beta"
        },
        ProviderType.OPENAI: {
            "model": "gpt-4o",
            "base_url": "https://api.openai.com/v1"
        },
        ProviderType.OPENROUTER: {
            "model": "anthropic/claude-3.5-sonnet",
            "base_url": "https://openrouter.ai/api/v1"
        },
        ProviderType.VLLM: {
            "model": "qwen3.5-35b-a3b",
            "base_url": "http://localhost:8000/v1"
        },
        ProviderType.LMSTUDIO: {
            "model": "local-model",
            "base_url": "http://localhost:1234/v1"
        }
    }

    @classmethod
    def get_defaults(cls, provider: ProviderType) -> dict:
        """Retourne les valeurs par défaut pour un provider."""
        return cls.DEFAULTS.get(provider, {})


class Settings(BaseSettings):
    """Configuration globale chargée depuis .env."""

    # Provider actif
    active_provider: str = "vllm"

    # Gemini
    gemini_api_key: Optional[str] = None
    gemini_model: str = "gemini-3.1-pro"

    # OpenAI
    openai_api_key: Optional[str] = None
    openai_base_url: str = "https://api.openai.com/v1"
    openai_model: str = "gpt-4o"

    # OpenRouter (multi-modeles)
    openrouter_api_key: Optional[str] = None
    openrouter_base_url: str = "https://openrouter.ai/api/v1"
    openrouter_model: str = "openai/gpt-4.1"

    # vLLM (reverse proxy)
    vllm_base_url: Optional[str] = None
    vllm_model: str = "qwen3.5-35b-a3b"
    vllm_api_key: Optional[str] = None

    # LM Studio
    lmstudio_base_url: str = "http://localhost:1234/v1"
    lmstudio_model: str = "local-model"

    model_config = {
        "env_file": _ENV_FILE,
        "env_file_encoding": "utf-8",
        "extra": "ignore"
    }


def get_settings() -> Settings:
    """Charge et retourne les paramètres."""
    return Settings()


def get_provider_config(settings: Optional[Settings] = None) -> ProviderConfig:
    """
    Retourne la configuration du provider actif.

    Args:
        settings: Instance Settings (chargée si None)

    Returns:
        ProviderConfig configuré
    """
    if settings is None:
        settings = get_settings()

    provider_str = settings.active_provider.lower()
    provider = ProviderType(provider_str)
    defaults = ProviderConfig.get_defaults(provider)

    if provider == ProviderType.GEMINI:
        return ProviderConfig(
            provider=provider,
            model=settings.gemini_model or defaults["model"],
            api_key=settings.gemini_api_key,
            base_url=defaults["base_url"]
        )

    elif provider == ProviderType.OPENAI:
        return ProviderConfig(
            provider=provider,
            model=settings.openai_model or defaults["model"],
            api_key=settings.openai_api_key,
            base_url=settings.openai_base_url or defaults["base_url"]
        )

    elif provider == ProviderType.OPENROUTER:
        return ProviderConfig(
            provider=provider,
            model=settings.openrouter_model or defaults["model"],
            api_key=settings.openrouter_api_key,
            base_url=settings.openrouter_base_url or "https://openrouter.ai/api/v1"
        )

    elif provider == ProviderType.VLLM:
        return ProviderConfig(
            provider=provider,
            model=settings.vllm_model or defaults["model"],
            api_key=settings.vllm_api_key,
            base_url=settings.vllm_base_url or defaults["base_url"]
        )

    elif provider == ProviderType.LMSTUDIO:
        return ProviderConfig(
            provider=provider,
            model=settings.lmstudio_model or defaults["model"],
            api_key=None,
            base_url=settings.lmstudio_base_url or defaults["base_url"]
        )

    raise ValueError(f"Provider non supporté: {provider}")


def get_litellm_model(config: ProviderConfig) -> str:
    """
    Retourne le nom du modèle au format LiteLLM.

    Args:
        config: Configuration du provider

    Returns:
        String au format litellm (ex: "gemini/gemini-3.1-pro")
    """
    prefix_map = {
        ProviderType.GEMINI: "gemini",
        ProviderType.OPENAI: "openai",
        ProviderType.OPENROUTER: "openrouter",
        ProviderType.VLLM: "openai",  # vLLM utilise l'API OpenAI
        ProviderType.LMSTUDIO: "openai"  # LM Studio aussi
    }

    prefix = prefix_map.get(config.provider, "openai")
    return f"{prefix}/{config.model}"


# Instance globale pour accès facile
_settings = None

def get_global_settings() -> Settings:
    """Retourne l'instance globale des settings (singleton)."""
    global _settings
    if _settings is None:
        _settings = get_settings()
    return _settings
