"""Helpers pour les notebooks Claudish.

Ce module fournit des fonctions utilitaires pour appeler Claudish
(le proxy multi-provider compatible wire Anthropic) depuis des
notebooks Jupyter, sans dépendre du CLI Claude Code.

Exemple d'utilisation:

    from helpers.claudish_client import chat, list_models, get_endpoint

    # Lister les modeles exposes par Claudish
    print(list_models())

    # Appel direct sur le wire Anthropic
    text = chat("Explique le no-fallback en 2 phrases", model="glm-5.2")
    print(text)
"""