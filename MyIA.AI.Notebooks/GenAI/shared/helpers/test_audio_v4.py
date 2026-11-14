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


def test_depuis_repertoire_frere_du_depot(tmp_path: Path) -> None:
    """Un noyau lance dans docs/ retrouve le paquet du meme depot."""
    applications = _make_tree(tmp_path, prefix=("MyIA.AI.Notebooks", "GenAI"))
    (tmp_path / ".git").mkdir()
    start = tmp_path / "docs" / "reference"
    start.mkdir(parents=True)
    assert audio_v4.find_v4_root(start) == applications


def test_git_worktree_et_priorite_locale(tmp_path: Path) -> None:
    """Le fichier .git des worktrees marche, sans supplanter un v4 local."""
    depot = _make_tree(tmp_path, prefix=("MyIA.AI.Notebooks", "GenAI"))
    (tmp_path / ".git").write_text("gitdir: /dummy\n", encoding="utf-8")
    start = tmp_path / "docs"
    start.mkdir()
    assert audio_v4.find_v4_root(start) == depot
    local = _make_tree(start)
    assert audio_v4.find_v4_root(start) == local


def test_ne_sort_pas_du_depot_imbrique(tmp_path: Path) -> None:
    _make_tree(tmp_path, prefix=("MyIA.AI.Notebooks", "GenAI"))
    (tmp_path / ".git").mkdir()
    nested = tmp_path / "nested"
    nested.mkdir()
    (nested / ".git").mkdir()
    start = nested / "docs"
    start.mkdir()
    with pytest.raises(ModuleNotFoundError):
        audio_v4.find_v4_root(start)


def test_depot_imbrique_ne_charge_pas_le_v4_du_parent(tmp_path: Path) -> None:
    """Un v4 situe au-dessus du depot imbrique ne lui appartient pas."""
    outer_v4 = tmp_path / "v4"
    outer_v4.mkdir()
    (outer_v4 / "narration.py").write_text("", encoding="utf-8")
    nested = tmp_path / "nested"
    nested.mkdir()
    (nested / ".git").write_text("gitdir: /dummy\n", encoding="utf-8")
    start = nested / "docs"
    start.mkdir()
    with pytest.raises(ModuleNotFoundError):
        audio_v4.find_v4_root(start)


def test_ancre_genai_exterieure_ne_contourne_pas_le_depot_imbrique(tmp_path: Path) -> None:
    """L'ancre GenAI au-dessus de .git ne doit pas servir un autre depot."""
    genai = tmp_path / "GenAI"
    _make_tree(tmp_path, prefix=("GenAI",))
    nested = genai / "nested"
    nested.mkdir()
    (nested / ".git").mkdir()
    with pytest.raises(ModuleNotFoundError):
        audio_v4.find_v4_root(nested)
