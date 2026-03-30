"""
Tests unitaires pour le module utils.
"""

import pytest
from datetime import datetime
from src.utils import format_name, calculate_age, validate_email


class TestFormatName:
    """Tests pour la fonction format_name."""

    def test_format_name_basic(self):
        """Test avec des noms simples."""
        result = format_name("alice", "dupont")
        assert result == "Alice DUPONT"

    def test_format_name_already_formatted(self):
        """Test avec des noms déjà formatés."""
        result = format_name("Alice", "DUPONT")
        assert result == "Alice DUPONT"

    def test_format_name_mixed_case(self):
        """Test avec des casses mélangées."""
        result = format_name("aLiCe", "dUpOnT")
        assert result == "Alice DUPONT"


class TestCalculateAge:
    """Tests pour la fonction calculate_age."""

    def test_calculate_age_valid(self):
        """Test avec une année de naissance valide."""
        current_year = datetime.now().year
        result = calculate_age(1990)
        assert result == current_year - 1990

    def test_calculate_age_current_year(self):
        """Test avec l'année courante."""
        current_year = datetime.now().year
        result = calculate_age(current_year)
        assert result == 0

    def test_calculate_age_future_year(self):
        """Test avec une année future - doit lever une exception."""
        future_year = datetime.now().year + 1
        with pytest.raises(ValueError) as excinfo:
            calculate_age(future_year)
        assert "futur" in str(excinfo.value).lower()


class TestValidateEmail:
    """Tests pour la fonction validate_email."""

    def test_validate_email_valid(self):
        """Test avec des emails valides."""
        assert validate_email("test@example.com") is True
        assert validate_email("user.name@domain.org") is True
        assert validate_email("a@b.co") is True

    def test_validate_email_invalid_no_at(self):
        """Test avec un email sans @."""
        assert validate_email("testexample.com") is False

    def test_validate_email_invalid_no_domain(self):
        """Test avec un email sans domaine."""
        assert validate_email("test@") is False

    def test_validate_email_invalid_no_local(self):
        """Test avec un email sans partie locale."""
        assert validate_email("@example.com") is False

    def test_validate_email_invalid_no_dot_in_domain(self):
        """Test avec un email sans point dans le domaine."""
        assert validate_email("test@example") is False

    def test_validate_email_empty(self):
        """Test avec une chaîne vide."""
        assert validate_email("") is False

    def test_validate_email_none(self):
        """Test avec None."""
        assert validate_email(None) is False
