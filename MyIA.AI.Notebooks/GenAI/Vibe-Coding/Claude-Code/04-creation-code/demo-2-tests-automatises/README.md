# Demo 2 - Tests Automatisés

## Objectif

Apprendre à générer des tests complets et efficaces pour du code existant ou nouvellement créé.

## Durée estimée

**45 minutes**

## Concepts

### Types de tests

| Type | Description | Scope |
|------|-------------|-------|
| Unitaire | Teste une fonction/méthode isolée | Fonction |
| Intégration | Teste plusieurs composants ensemble | Module |
| End-to-End | Teste le système complet | Application |

### Structure des tests avec pytest

```python
# test_module.py

import pytest
from src.module import fonction

class TestFonction:
    """Tests pour la fonction."""

    def test_cas_normal(self):
        """Test du comportement normal."""
        result = fonction(input_valide)
        assert result == expected

    def test_cas_limite(self):
        """Test des cas limites."""
        result = fonction(input_limite)
        assert result == expected

    def test_erreur(self):
        """Test de la gestion d'erreur."""
        with pytest.raises(ValueError):
            fonction(input_invalide)
```

## Étapes

### Étape 1 : Analyser le code à tester (5 min)

Avant de générer des tests, analysez le code :

```
@src/services.py Analyse ce code et liste :
1. Toutes les fonctions publiques à tester
2. Les dépendances externes à mocker
3. Les cas limites à couvrir
4. Les branches conditionnelles
```

### Étape 2 : Générer des tests unitaires (15 min)

#### Demande de génération

```
@src/services.py Génère des tests unitaires complets avec pytest.

Pour chaque fonction, couvre :
- Cas normal (happy path)
- Cas limites (valeurs extrêmes, listes vides)
- Cas d'erreur (exceptions attendues)
- Différentes branches du code

Structure :
- Un fichier test par module source
- Classes de test groupées par fonctionnalité
- Nommage descriptif : test_<fonction>_<scenario>

Inclus :
- Fixtures pour les données de test
- Commentaires explicatifs
- Type hints
```

#### Exemple de résultat

```python
# tests/test_book_service.py

import pytest
from datetime import date
from src.services import BookService
from src.models import Book
from src.exceptions import BookNotFound, InvalidRating


@pytest.fixture
def service(db_session):
    """Service avec base de données de test."""
    return BookService(db_session)


@pytest.fixture
def sample_book(service):
    """Livre de test."""
    return service.add_book(
        title="1984",
        author="George Orwell",
        pages=328,
        genre="Dystopia"
    )


class TestAddBook:
    """Tests pour BookService.add_book"""

    def test_add_book_success(self, service):
        """Ajouter un livre avec des données valides."""
        book = service.add_book(
            title="Le Petit Prince",
            author="Saint-Exupéry",
            pages=96
        )

        assert book.id is not None
        assert book.title == "Le Petit Prince"
        assert book.is_read is False

    def test_add_book_with_genre(self, service):
        """Ajouter un livre avec genre optionnel."""
        book = service.add_book(
            title="Dune",
            author="Frank Herbert",
            pages=412,
            genre="Science-Fiction"
        )

        assert book.genre == "Science-Fiction"

    def test_add_book_empty_title_fails(self, service):
        """Titre vide doit lever une erreur."""
        with pytest.raises(ValueError, match="titre"):
            service.add_book(title="", author="Test", pages=100)


class TestMarkAsRead:
    """Tests pour BookService.mark_as_read"""

    def test_mark_as_read_success(self, service, sample_book):
        """Marquer un livre comme lu."""
        updated = service.mark_as_read(sample_book.id, rating=4)

        assert updated.is_read is True
        assert updated.rating == 4
        assert updated.read_date == date.today()

    def test_mark_as_read_invalid_rating(self, service, sample_book):
        """Note invalide (hors 1-5) doit lever une erreur."""
        with pytest.raises(InvalidRating):
            service.mark_as_read(sample_book.id, rating=6)

    def test_mark_as_read_book_not_found(self, service):
        """Livre inexistant doit lever une erreur."""
        with pytest.raises(BookNotFound):
            service.mark_as_read(book_id=99999, rating=3)
```

### Étape 3 : Ajouter des fixtures (10 min)

#### Fichier conftest.py

```
Génère un fichier conftest.py avec :

Fixtures de base :
- db_session : Session SQLAlchemy de test (rollback après chaque test)
- client : TestClient pour API (si applicable)
- sample_data : Données de test réutilisables

Fixtures spécifiques :
- Utilisateurs de test avec différents rôles
- Données représentatives du domaine

Configuration :
- Markers personnalisés (slow, integration)
- Hooks de setup/teardown
```

### Étape 4 : Tests avec mocking (10 min)

#### Mocker des dépendances

```
@src/services/email.py Cette fonction envoie des emails.
Génère des tests qui mockent l'envoi réel.

Le mock doit :
- Vérifier que send_email est appelé avec les bons arguments
- Simuler les cas de succès et d'échec
- Ne pas envoyer de vrais emails
```

#### Exemple avec mock

```python
from unittest.mock import Mock, patch

class TestEmailService:

    @patch('src.services.email.smtp_client')
    def test_send_welcome_email(self, mock_smtp):
        """Test d'envoi d'email de bienvenue."""
        mock_smtp.send.return_value = True

        service = EmailService()
        result = service.send_welcome("user@test.com", "John")

        assert result is True
        mock_smtp.send.assert_called_once_with(
            to="user@test.com",
            subject="Bienvenue John !",
            body=pytest.any(str)
        )

    @patch('src.services.email.smtp_client')
    def test_send_email_failure(self, mock_smtp):
        """Test de gestion d'erreur d'envoi."""
        mock_smtp.send.side_effect = ConnectionError("SMTP down")

        service = EmailService()

        with pytest.raises(EmailSendError):
            service.send_welcome("user@test.com", "John")
```

### Étape 5 : Vérifier la couverture (5 min)

```bash
# Installer pytest-cov
pip install pytest-cov

# Lancer les tests avec couverture
pytest --cov=src --cov-report=html --cov-report=term

# Ouvrir le rapport HTML
open htmlcov/index.html
```

Si la couverture est insuffisante :

```
La couverture de @src/services.py est de 65%.
Génère des tests supplémentaires pour atteindre 80%.
Focus sur les lignes non couvertes.
```

## Exercice pratique

### Mission

Atteignez 80% de couverture sur un module existant.

### Étapes

1. **Mesurer la couverture actuelle**
   ```bash
   pytest --cov=src --cov-report=term-missing
   ```

2. **Identifier les lacunes**
   ```
   Quelles lignes ne sont pas couvertes dans @src/services.py ?
   ```

3. **Générer les tests manquants**
   ```
   Génère des tests pour couvrir les lignes [X, Y, Z] de @src/services.py
   ```

4. **Valider**
   ```bash
   pytest --cov=src --cov-fail-under=80
   ```

### Livrable

- Suite de tests complète
- Couverture > 80%
- Rapport de couverture HTML

## Bonnes pratiques

### Nommage des tests

```python
# Pattern : test_<fonction>_<scenario>_<resultat_attendu>

def test_add_book_with_valid_data_returns_book():
def test_add_book_with_empty_title_raises_error():
def test_list_books_when_empty_returns_empty_list():
```

### Organisation des tests

```
tests/
├── conftest.py           # Fixtures globales
├── factories.py          # Factories de données
├── unit/
│   ├── test_models.py
│   └── test_services.py
├── integration/
│   └── test_api.py
└── e2e/
    └── test_workflows.py
```

### AAA Pattern

```python
def test_example():
    # Arrange - Préparer les données
    input_data = {"key": "value"}

    # Act - Exécuter l'action
    result = function(input_data)

    # Assert - Vérifier le résultat
    assert result == expected
```

## Points clés à retenir

1. **Couverture ≠ Qualité** : 100% de couverture ne garantit pas des bons tests

2. **Testez les comportements** : Pas l'implémentation

3. **Isolez les tests** : Chaque test doit être indépendant

4. **Nommez clairement** : Le nom doit décrire le scénario

---

**Prochaine étape** : [Demo 3 - Documentation](../demo-3-documentation/)
