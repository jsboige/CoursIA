"""Tests du garde zero-pad serie (#12586).

Les cas sont construits sur les formes REELLES de la serie GameTheory :
zero-pades valides (03a, 08d, 26), chiffre unique invalide (3a, 8d, 8-).
Le lookahead est la piece delicate -- chaque forme a son test.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_series_zero_pad import main, violations  # noqa: E402


@pytest.fixture
def series(tmp_path: Path) -> Path:
    d = tmp_path / "GameTheory"
    d.mkdir()
    return d


def test_serie_propre_passe(series: Path):
    for name in ["GameTheory-01-Setup.ipynb", "GameTheory-03a-X.ipynb",
                 "GameTheory-08d-Y.lean", "GameTheory-26-Z.ipynb"]:
        (series / name).write_text("x", encoding="utf-8")
    assert violations(series) == []


def test_chiffre_unique_avec_lettre_est_violation(series: Path):
    (series / "GameTheory-3a-Chemins.ipynb").write_text("x", encoding="utf-8")
    found = violations(series)
    assert len(found) == 1
    assert found[0]["name"] == "GameTheory-3a-Chemins.ipynb"


def test_chiffre_unique_avec_tiret_est_violation(series: Path):
    (series / "GameTheory-8-CombinatorialGames.ipynb").write_text("x",
                                                                  encoding="utf-8")
    assert len(violations(series)) == 1


def test_deux_chiffres_puis_lettre_passe(series: Path):
    # le 0 de 08d est suivi d'un chiffre -> pas une violation
    (series / "GameTheory-08d-Lean-CGT-Native.ipynb").write_text("x",
                                                                 encoding="utf-8")
    assert violations(series) == []


def test_sous_repertoire_scanne(series: Path):
    sub = series / "game_theory_lean"
    sub.mkdir()
    (sub / "GameTheory-3b-Fantom.ipynb").write_text("x", encoding="utf-8")
    found = violations(series)
    assert len(found) == 1
    assert found[0]["name"] == "GameTheory-3b-Fantom.ipynb"


def test_hors_prefix_ignore(series: Path):
    (series / "autre-3-nom.ipynb").write_text("x", encoding="utf-8")
    (series / "game_theory_lean").mkdir()
    (series / "game_theory_lean" / "Swaps.lean").write_text("x",
                                                            encoding="utf-8")
    assert violations(series) == []


def test_prefix_non_defaut(series: Path):
    (series / "Search-5-X.ipynb").write_text("x", encoding="utf-8")
    assert len(violations(series, prefix="Search")) == 1
    assert violations(series, prefix="GameTheory") == []


def test_main_sortie_zero_sur_serie_propre(series: Path, capsys):
    (series / "GameTheory-03b-Ok.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--prefix", "GameTheory"]) == 0
    assert "OK" in capsys.readouterr().out


def test_main_sortie_un_sur_violation(series: Path, capsys):
    (series / "GameTheory-3e-Bad.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--prefix", "GameTheory"]) == 1
    assert "3e-Bad" in capsys.readouterr().out


def test_main_json_shape(series: Path, capsys):
    import json
    (series / "GameTheory-3f-Bad.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["count"] == 1
    assert payload["violations"][0]["name"] == "GameTheory-3f-Bad.ipynb"


def test_main_repertoire_introuvable():
    assert main(["--series-dir", "Nulle/Part"]) == 2
