"""Tests de la resolution du paquet ``v4`` (issue #23179).

Le defaut d'origine n'etait pas visible en test : la remontee depuis ``Path.cwd()``
reussissait toujours parce que les tests tournaient depuis ``04-Applications``.
Ces cas construisent donc les arborescences et deplacent le point de depart.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

from helpers import audio_v4


def _make_tree(root: Path, prefix: tuple[str, ...] = ("GenAI",)) -> Path:
    """Cree ``<root>/<prefix>/Audio/04-Applications/v4/narration.py`` et le rend."""
    applications = root.joinpath(*prefix, "Audio", "04-Applications")
    (applications / "v4").mkdir(parents=True)
    (applications / "v4" / "narration.py").write_text(
        "def parse_narration_script(script):\n    return []\n", encoding="utf-8"
    )
    return applications


def test_remontee_depuis_04_applications(tmp_path: Path) -> None:
    applications = _make_tree(tmp_path)
    assert audio_v4.find_v4_root(applications) == applications


def test_ancre_genai_depuis_audio(tmp_path: Path) -> None:
    """Le cas mesure dans l'issue : un noyau lance dans ``Audio/``."""
    applications = _make_tree(tmp_path)
    assert audio_v4.find_v4_root(applications.parent) == applications


def test_descente_depuis_myia_ai_notebooks(tmp_path: Path) -> None:
    applications = _make_tree(tmp_path)
    assert audio_v4.find_v4_root(tmp_path) == applications


def test_descente_depuis_la_racine_du_depot(tmp_path: Path) -> None:
    """La racine du depot porte ``MyIA.AI.Notebooks`` entre elle et ``GenAI``."""
    applications = _make_tree(tmp_path, prefix=("MyIA.AI.Notebooks", "GenAI"))
    assert audio_v4.find_v4_root(tmp_path) == applications


def test_echec_nomme_le_chemin_attendu(tmp_path: Path) -> None:
    elsewhere = tmp_path / "ailleurs"
    elsewhere.mkdir()
    with pytest.raises(ModuleNotFoundError) as excinfo:
        audio_v4.find_v4_root(elsewhere)

    message = str(excinfo.value)
    assert "v4/narration.py" in message
    assert "attendu" in message
    assert str(elsewhere) in message


def test_ensure_est_idempotent(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(sys, "path", list(sys.path))
    applications = _make_tree(tmp_path)

    first = audio_v4.ensure_v4_on_path(applications)
    audio_v4.ensure_v4_on_path(applications)

    assert first == applications
    assert sys.path.count(str(applications)) == 1
