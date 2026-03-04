"""
Client LLM unifié pour AgenticDataScience.

Utilise LiteLLM pour fournir une interface commune à tous les providers.
"""

from typing import Optional, List, Dict, Any, Union
from litellm import completion
from config.providers import (
    get_provider_config,
    get_litellm_model,
    get_global_settings,
    ProviderConfig
)


class LLMClient:
    """
    Client LLM unifié supportant multiples providers.

    Usage:
        client = LLMClient()  # Utilise le provider configuré dans .env
        response = client.generate("Explique-moi le machine learning")
    """

    def __init__(self, config: Optional[ProviderConfig] = None):
        """
        Initialise le client avec la configuration du provider actif.

        Args:
            config: Configuration explicite (sinon utilise .env)
        """
        if config is None:
            config = get_provider_config()
        self.config = config
        self.model = get_litellm_model(config)

    def generate(
        self,
        prompt: str,
        system: Optional[str] = None,
        temperature: float = 0.7,
        max_tokens: Optional[int] = None,
        **kwargs
    ) -> str:
        """
        Génère une réponse à partir d'un prompt.

        Args:
            prompt: Prompt utilisateur
            system: Prompt système (optionnel)
            temperature: Température de génération
            max_tokens: Limite de tokens
            **kwargs: Arguments supplémentaires pour litellm

        Returns:
            Texte généré
        """
        messages = []

        if system:
            messages.append({"role": "system", "content": system})

        messages.append({"role": "user", "content": prompt})

        # Construction des arguments
        call_kwargs = {
            "model": self.model,
            "messages": messages,
            "temperature": temperature,
        }

        # Ajout base_url pour vLLM et LM Studio
        if self.config.base_url and self.config.provider.value in ["vllm", "lmstudio"]:
            call_kwargs["api_base"] = self.config.base_url

        # Ajout API key si disponible
        if self.config.api_key:
            call_kwargs["api_key"] = self.config.api_key

        if max_tokens:
            call_kwargs["max_tokens"] = max_tokens

        call_kwargs.update(kwargs)

        response = completion(**call_kwargs)
        return response.choices[0].message.content

    def chat(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        **kwargs
    ) -> str:
        """
        Interface de chat avec historique.

        Args:
            messages: Liste de messages [{"role": "user/assistant", "content": "..."}]
            temperature: Température de génération
            **kwargs: Arguments supplémentaires

        Returns:
            Réponse de l'assistant
        """
        call_kwargs = {
            "model": self.model,
            "messages": messages,
            "temperature": temperature,
        }

        if self.config.base_url and self.config.provider.value in ["vllm", "lmstudio"]:
            call_kwargs["api_base"] = self.config.base_url

        if self.config.api_key:
            call_kwargs["api_key"] = self.config.api_key

        call_kwargs.update(kwargs)

        response = completion(**call_kwargs)
        return response.choices[0].message.content

    def __repr__(self) -> str:
        return f"LLMClient(provider={self.config.provider.value}, model={self.config.model})"


# Instance globale pour usage simple
_default_client = None


def get_client() -> LLMClient:
    """Retourne le client LLM par défaut (singleton)."""
    global _default_client
    if _default_client is None:
        _default_client = LLMClient()
    return _default_client


def generate(prompt: str, **kwargs) -> str:
    """
    Fonction utilitaire pour générer rapidement une réponse.

    Usage:
        from utils.llm_client import generate
        response = generate("Explique Python en 3 phrases")
    """
    return get_client().generate(prompt, **kwargs)
