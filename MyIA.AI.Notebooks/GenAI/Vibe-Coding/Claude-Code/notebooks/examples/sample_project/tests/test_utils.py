"""
Tests unitaires pour le module utils.

Execute avec: pytest tests/test_utils.py
"""

import pytest
import sys
import os

# Ajouter le repertoire parent au path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils import (
    calculate_statistics,
    format_report,
    validate_data,
    normalize_data
)


class TestCalculateStatistics:
    """Tests pour la fonction calculate_statistics."""

    def test_basic_statistics(self):
        """Test des statistiques de base."""
        data = [1, 2, 3, 4, 5]
        stats = calculate_statistics(data)

        assert stats["mean"] == 3.0
        assert stats["median"] == 3.0
        assert stats["min"] == 1
        assert stats["max"] == 5
        assert stats["count"] == 5

    def test_even_count_median(self):
        """Test de la mediane avec nombre pair d'elements."""
        data = [1, 2, 3, 4]
        stats = calculate_statistics(data)

        assert stats["median"] == 2.5

    def test_single_element(self):
        """Test avec un seul element."""
        data = [42]
        stats = calculate_statistics(data)

        assert stats["mean"] == 42
        assert stats["median"] == 42
        assert stats["std_dev"] == 0

    def test_empty_list_raises_error(self):
        """Test qu'une liste vide leve une erreur."""
        with pytest.raises(ValueError):
            calculate_statistics([])

    def test_negative_numbers(self):
        """Test avec des nombres negatifs."""
        data = [-5, -3, 0, 3, 5]
        stats = calculate_statistics(data)

        assert stats["mean"] == 0
        assert stats["min"] == -5
        assert stats["max"] == 5


class TestFormatReport:
    """Tests pour la fonction format_report."""

    def test_basic_format(self):
        """Test du formatage de base."""
        stats = {"mean": 10.5, "median": 10, "count": 5}
        report = format_report(stats)

        assert "Rapport Statistique" in report
        assert "10.5" in report
        assert "10" in report

    def test_missing_values(self):
        """Test avec des valeurs manquantes."""
        stats = {"mean": 10}
        report = format_report(stats)

        assert "N/A" in report


class TestValidateData:
    """Tests pour la fonction validate_data."""

    def test_mixed_data(self):
        """Test avec des donnees mixtes."""
        data = [1, "hello", 3.5, None, 5, "6"]
        valid = validate_data(data)

        assert valid == [1.0, 3.5, 5.0, 6.0]

    def test_all_invalid(self):
        """Test avec que des donnees invalides."""
        data = ["a", "b", None, []]
        valid = validate_data(data)

        assert valid == []

    def test_special_floats(self):
        """Test avec des valeurs speciales."""
        data = [1, float('inf'), 3, float('nan')]
        valid = validate_data(data)

        assert valid == [1.0, 3.0]


class TestNormalizeData:
    """Tests pour la fonction normalize_data."""

    def test_basic_normalization(self):
        """Test de normalisation basique."""
        data = [0, 50, 100]
        normalized = normalize_data(data)

        assert normalized == [0.0, 0.5, 1.0]

    def test_constant_data(self):
        """Test avec des donnees constantes."""
        data = [5, 5, 5]
        normalized = normalize_data(data)

        assert all(x == 0.5 for x in normalized)

    def test_empty_list(self):
        """Test avec une liste vide."""
        assert normalize_data([]) == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
