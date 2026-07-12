"""
Fonctions utilitaires pour le projet.
"""

from datetime import datetime


def format_name(first_name: str, last_name: str) -> str:
    """
    Formate un nom complet à partir du prénom et du nom.

    Args:
        first_name: Le prénom de la personne.
        last_name: Le nom de famille.

    Returns:
        Le nom complet formaté (Prénom NOM).
    """
    return f"{first_name.capitalize()} {last_name.upper()}"


def calculate_age(birth_year: int) -> int:
    """
    Calcule l'âge à partir de l'année de naissance.

    Args:
        birth_year: L'année de naissance (ex: 1990).

    Returns:
        L'âge en années.

    Raises:
        ValueError: Si l'année de naissance est dans le futur.
    """
    current_year = datetime.now().year

    if birth_year > current_year:
        raise ValueError("L'année de naissance ne peut pas être dans le futur")

    return current_year - birth_year


def validate_email(email: str) -> bool:
    """
    Vérifie si une adresse email a un format valide.

    Args:
        email: L'adresse email à valider.

    Returns:
        True si le format est valide, False sinon.
    """
    if not email or "@" not in email:
        return False

    parts = email.split("@")
    if len(parts) != 2:
        return False

    local, domain = parts
    if not local or not domain:
        return False

    if "." not in domain:
        return False

    return True
