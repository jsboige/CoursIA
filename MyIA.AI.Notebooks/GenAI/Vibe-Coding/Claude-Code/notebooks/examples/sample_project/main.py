"""
Application de demonstration pour les notebooks Claude CLI.

Ce fichier sert d'exemple pour les exercices de reference de fichiers
et d'analyse de code avec Claude.
"""

from utils import calculate_statistics, format_report


def main():
    """Point d'entree principal de l'application."""
    # Donnees d'exemple
    data = [23, 45, 67, 89, 12, 34, 56, 78, 90, 11]

    print("=== Analyse Statistique ===\n")

    # Calculer les statistiques
    stats = calculate_statistics(data)

    # Afficher le rapport
    report = format_report(stats)
    print(report)

    # Retourner les stats pour les tests
    return stats


def process_batch(items: list) -> dict:
    """
    Traite un lot d'elements et retourne un resume.

    Args:
        items: Liste d'elements a traiter.

    Returns:
        dict: Resume du traitement avec count, valid, invalid.
    """
    valid_count = 0
    invalid_count = 0

    for item in items:
        if isinstance(item, (int, float)) and item >= 0:
            valid_count += 1
        else:
            invalid_count += 1

    return {
        "total": len(items),
        "valid": valid_count,
        "invalid": invalid_count,
        "success_rate": valid_count / len(items) if items else 0
    }


if __name__ == "__main__":
    main()
