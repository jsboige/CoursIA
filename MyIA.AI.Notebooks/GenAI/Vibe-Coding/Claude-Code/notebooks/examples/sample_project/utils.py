"""
Fonctions utilitaires pour l'application de demonstration.

Ce module contient des fonctions de calcul statistique et de formatage
utilisees par le module principal.
"""

from typing import List, Dict, Any
import math


def calculate_statistics(data: List[float]) -> Dict[str, float]:
    """
    Calcule les statistiques descriptives d'une liste de nombres.

    Args:
        data: Liste de valeurs numeriques.

    Returns:
        Dict contenant mean, median, std_dev, min, max, count.

    Raises:
        ValueError: Si la liste est vide.

    Example:
        >>> stats = calculate_statistics([1, 2, 3, 4, 5])
        >>> stats["mean"]
        3.0
    """
    if not data:
        raise ValueError("La liste de donnees ne peut pas etre vide")

    n = len(data)
    sorted_data = sorted(data)

    # Moyenne
    mean = sum(data) / n

    # Mediane
    mid = n // 2
    if n % 2 == 0:
        median = (sorted_data[mid - 1] + sorted_data[mid]) / 2
    else:
        median = sorted_data[mid]

    # Ecart-type
    variance = sum((x - mean) ** 2 for x in data) / n
    std_dev = math.sqrt(variance)

    return {
        "mean": round(mean, 2),
        "median": round(median, 2),
        "std_dev": round(std_dev, 2),
        "min": min(data),
        "max": max(data),
        "count": n
    }


def format_report(stats: Dict[str, Any]) -> str:
    """
    Formate les statistiques en un rapport lisible.

    Args:
        stats: Dictionnaire de statistiques.

    Returns:
        str: Rapport formate.
    """
    lines = [
        "Rapport Statistique",
        "=" * 30,
        f"Nombre d'elements : {stats.get('count', 'N/A')}",
        f"Moyenne          : {stats.get('mean', 'N/A')}",
        f"Mediane          : {stats.get('median', 'N/A')}",
        f"Ecart-type       : {stats.get('std_dev', 'N/A')}",
        f"Minimum          : {stats.get('min', 'N/A')}",
        f"Maximum          : {stats.get('max', 'N/A')}",
        "=" * 30
    ]
    return "\n".join(lines)


def validate_data(data: List[Any]) -> List[float]:
    """
    Valide et nettoie une liste de donnees.

    Args:
        data: Liste de donnees brutes.

    Returns:
        List[float]: Liste de valeurs numeriques valides.
    """
    valid_data = []
    for item in data:
        try:
            value = float(item)
            if not math.isnan(value) and not math.isinf(value):
                valid_data.append(value)
        except (TypeError, ValueError):
            continue
    return valid_data


def normalize_data(data: List[float]) -> List[float]:
    """
    Normalise les donnees entre 0 et 1.

    Args:
        data: Liste de valeurs numeriques.

    Returns:
        List[float]: Valeurs normalisees.
    """
    if not data:
        return []

    min_val = min(data)
    max_val = max(data)
    range_val = max_val - min_val

    if range_val == 0:
        return [0.5] * len(data)

    return [(x - min_val) / range_val for x in data]
