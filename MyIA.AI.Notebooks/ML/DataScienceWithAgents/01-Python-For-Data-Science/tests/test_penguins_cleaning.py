"""Tests du pipeline de nettoyage du notebook 1.5 (Palmer Penguins)."""
import pandas as pd
import pytest

from pathlib import Path

DATA = Path(__file__).resolve().parent.parent / "data"


@pytest.fixture
def raw():
    return pd.read_csv(DATA / "penguins_raw.csv")


@pytest.fixture
def tidy():
    return pd.read_csv(DATA / "penguins.csv")


def test_raw_shape(raw):
    """Le jeu brut a les dimensions attendues."""
    assert raw.shape == (344, 17)


def test_no_exact_duplicates(raw):
    """Aucun doublon exact dans le jeu brut (audité en 1.5)."""
    assert raw.duplicated().sum() == 0


def test_species_short_names(raw, tidy):
    """Le nom court (premier mot) du brut coincide avec l'espèce de la référence."""
    assert (raw["Species"].str.split().str[0] == tidy["species"]).all()


def test_cleaning_reaches_reference(raw, tidy):
    """Le pipeline de 1.5 rejoint la référence : 0 divergence sur les 4 mesures."""
    pairs = [
        ("Culmen Length (mm)", "bill_length_mm"),
        ("Culmen Depth (mm)", "bill_depth_mm"),
        ("Flipper Length (mm)", "flipper_length_mm"),
        ("Body Mass (g)", "body_mass_g"),
    ]
    for col_raw, col_tidy in pairs:
        a, b = raw[col_raw], tidy[col_tidy]
        divergent = ((a != b) & ~(a.isna() & b.isna())).sum()
        assert divergent == 0, f"{col_raw}: {divergent} lignes divergentes"


def test_reference_keeps_missing_values(tidy):
    """La table de référence conserve ses 19 valeurs manquantes (nettoyer != supprimer)."""
    assert tidy.isna().sum().sum() == 19


def test_date_column_parseable(raw):
    """La date de ponte texte se convertit en datetime."""
    dates = pd.to_datetime(raw["Date Egg"])
    assert set(dates.dt.year.unique()) == {2007, 2008, 2009}
