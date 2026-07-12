"""
Point d'entrée principal de l'application.
"""

from utils import format_name, calculate_age
from models.user import User


def main():
    """Fonction principale de démonstration."""
    # Créer quelques utilisateurs
    users = [
        User("Alice", "Dupont", "alice@example.com", 1990),
        User("Bob", "Martin", "bob@example.com", 1985),
        User("Charlie", "Bernard", "charlie@example.com", 2000),
    ]

    # Afficher les informations
    print("=== Liste des utilisateurs ===\n")

    for user in users:
        full_name = format_name(user.first_name, user.last_name)
        age = calculate_age(user.birth_year)

        print(f"Nom complet : {full_name}")
        print(f"Email : {user.email}")
        print(f"Âge : {age} ans")
        print(f"Actif : {'Oui' if user.is_active else 'Non'}")
        print("-" * 30)


if __name__ == "__main__":
    main()
