#!/usr/bin/env python3
"""Tests dedies au detecteur check_media_regression (#12067).

Couvre les 5 cas de la matrice :

  1. Silence OK : pas de modification base->tete, 0 finding.
  2. Regression silencieuse (#12000) : cellule code gardee mais media
     remplace par un texte de mode degrade. --check exit 1.
  3. Suppression legitime : cellule code retirees entierement (remplacee
     par une cellule markdown, ou par une cellule code sans media).
     --check exit 0.
  4. Ajout : nouveau media a la tete. Pas un finding.
  5. Rotation asset : meme MIME, contenu different -- non detecte
     (presence MIME intacte = intentionnel).
  6. Mode chemin-explicite : cible un .ipynb precis, pas de delta git.
"""

from __future__ import annotations

import base64
import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "check_media_regression.py"

# Permet d'importer le script comme module (chemin absolu)
sys.path.insert(0, str(SCRIPT.parent))


def _png_b64(n: int) -> str:
    return base64.b64encode(b"x" * n).decode()


def _notebook_with_media(cells_media: list[tuple[str, int]]) -> dict:
    """Construit un notebook avec N cellules code portant un media chacune."""
    cells = []
    for mime, size in cells_media:
        cells.append({
            "cell_type": "code",
            "execution_count": 1,
            "outputs": [{
                "data": {mime: _png_b64(size)},
                "metadata": {},
                "output_type": "display_data",
            }],
            "source": [],
        })
    return {"cells": cells}


def _notebook_with_text(cells_text: list[str]) -> dict:
    cells = []
    for txt in cells_text:
        cells.append({
            "cell_type": "code",
            "execution_count": 1,
            "outputs": [{
                "text": txt,
                "metadata": {},
                "output_type": "stream",
            }],
            "source": [],
        })
    return {"cells": cells}


# ---------- Tests unitaires des helpers ----------


def test_is_media_key_image_png() -> None:
    from check_media_regression import _is_media_key
    assert _is_media_key("image/png") is True
    assert _is_media_key("image/jpeg") is True
    assert _is_media_key("audio/mpeg") is True
    assert _is_media_key("audio/wav") is True
    assert _is_media_key("video/mp4") is True
    assert _is_media_key("text/html") is False
    assert _is_media_key("text/plain") is False
    assert _is_media_key("application/json") is False


def test_collect_media_cells_picks_code_only() -> None:
    """Les cellules markdown ne sont pas scannees (les medias pedagogiques
    sont dans les outputs des cellules code).
    """
    from check_media_regression import _collect_media_cells
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["![png](data:image/png;base64,xxx)"]},
            {"cell_type": "code", "outputs": [
                {"data": {"image/png": "xxx"}, "metadata": {}, "output_type": "display_data"}
            ], "source": [], "execution_count": 1},
        ]
    }
    result = _collect_media_cells(nb)
    assert 1 in result
    assert 0 not in result


def test_collect_media_cells_html_embed() -> None:
    """Un output data avec text/html contenant <video>/<audio> est media."""
    from check_media_regression import _collect_media_cells
    nb = {"cells": [{
        "cell_type": "code",
        "execution_count": 1,
        "outputs": [{
            "data": {"text/html": ["<video src='x.mp4'>"]},
            "metadata": {},
            "output_type": "display_data",
        }],
        "source": [],
    }]}
    result = _collect_media_cells(nb)
    assert 0 in result
    assert "html:<video|audio>" in result[0]


# ---------- Tests d'integration (delta base vs tete) ----------


def _make_git_repo(tmp_path: Path, base_nb: dict, head_nb: dict) -> Path:
    repo = tmp_path / "fixture_repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    nb = repo / "fixture.ipynb"
    nb.write_text(json.dumps(base_nb))
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=repo, check=True)
    if json.dumps(base_nb, sort_keys=True) == json.dumps(head_nb, sort_keys=True):
        # Pas de modif => pas de 2e commit
        return repo
    nb.write_text(json.dumps(head_nb))
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "head"], cwd=repo, check=True)
    return repo


def _run_detector(repo: Path, *flags: str, base: str = "HEAD~1", head: str = "HEAD") -> subprocess.CompletedProcess:
    """Execute le detecteur avec flags positionnels avant les kwargs.

    Usage:
        _run_detector(repo)                                 # defaut
        _run_detector(repo, "--check")                      # flag booleen
        _run_detector(repo, "--base", "main", "--head", "HEAD")  # explicite
    """
    return subprocess.run(
        [sys.executable, str(SCRIPT), *flags, "--base", base, "--head", head],
        cwd=repo,
        capture_output=True,
        text=True,
    )


def test_no_modification_zero_findings(tmp_path: Path) -> None:
    """Cas 1 : base == tete -- 0 finding."""
    nb = _notebook_with_media([("image/png", 100)])
    repo = _make_git_repo(tmp_path, nb, nb)
    result = _run_detector(repo)
    # 0 notebook modifie => soit "Aucun notebook modifie", soit "0 finding"
    assert "Aucun notebook" in result.stdout or "0 finding" in result.stdout
    assert result.returncode == 0


def test_silent_regression_exit_one(tmp_path: Path) -> None:
    """Cas 2 : #12000 incident -- cellule code gardee, media -> texte degrade."""
    base = _notebook_with_media([("image/png", 533_000)])
    head = _notebook_with_text(["Generation ltx_pipelines desactivee"])
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "REGRESSION SILENCIEUSE" in result.stdout
    assert "image/png" in result.stdout
    # --check doit retourner exit 1
    result_check = _run_detector(repo, "--check")
    assert result_check.returncode == 1


def test_legitimate_suppression_exit_zero(tmp_path: Path) -> None:
    """Cas 3 : cellule code retirees entierement, remplacee par markdown."""
    base = _notebook_with_media([("image/png", 100)])
    head = {"cells": [{"cell_type": "markdown", "source": ["# intro"]}]}
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "SUPPRESSION LEGITIME" in result.stdout
    assert "REGRESSION SILENCIEUSE" not in result.stdout
    # --check exit 0 (legitime, pas une regression silencieuse)
    result_check = _run_detector(repo, "--check")
    assert result_check.returncode == 0


def test_legitimate_suppression_mime_lost_in_text_cell(tmp_path: Path) -> None:
    """Cas 3bis : cellule code gardee mais son contenu change (plus de media).
    Si la cellule tete est code mais n'a pas le media, c'est une
    regression silencieuse (pas legitime) -- l'auteur a efface sans
    retirer la cellule.
    """
    base = _notebook_with_media([("image/png", 100)])
    head = _notebook_with_text(["ok"])
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "REGRESSION SILENCIEUSE" in result.stdout


def test_added_media_is_information_not_finding(tmp_path: Path) -> None:
    """Cas 4 : ajout de media n'est pas un finding."""
    base = _notebook_with_media([("image/png", 100)])
    head = _notebook_with_media([("image/png", 100), ("image/jpeg", 200)])
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "AJOUTS" in result.stdout
    assert "REGRESSION SILENCIEUSE" not in result.stdout
    assert "SUPPRESSION LEGITIME" not in result.stdout
    # --check exit 0
    result_check = _run_detector(repo, "--check")
    assert result_check.returncode == 0


def test_asset_rotation_not_detected(tmp_path: Path) -> None:
    """Cas 5 : rotation d'asset (meme MIME, contenu different) -- non detecte."""
    base = _notebook_with_media([("image/png", 100)])
    head = _notebook_with_media([("image/png", 999)])  # meme MIME, contenu different
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "REGRESSION SILENCIEUSE" not in result.stdout
    assert "0 finding" in result.stdout


def test_json_output_well_formed(tmp_path: Path) -> None:
    """Mode --json produit du JSON parsable avec les bonnes cles."""
    base = _notebook_with_media([("image/png", 533_000)])
    head = _notebook_with_text(["Generation ltx_pipelines desactivee"])
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo, "--json")
    assert result.returncode == 0
    payload = json.loads(result.stdout)
    assert "findings" in payload
    assert "summary" in payload
    assert payload["summary"]["regression_silencieuse"] == 1
    assert payload["summary"]["suppression_legitime"] == 0
    assert payload["summary"]["ajouts"] == 0
    finding = payload["findings"][0]
    assert finding["regression_silencieuse"][0]["cell_index"] == 0
    assert "image/png" in finding["regression_silencieuse"][0]["lost_mime"]


def test_multi_mime_types(tmp_path: Path) -> None:
    """Plusieurs types MIME (audio + image) dans le meme notebook."""
    base = _notebook_with_media([("image/png", 100), ("audio/mpeg", 200)])
    head = _notebook_with_text(["degraded 1", "degraded 2"])
    repo = _make_git_repo(tmp_path, base, head)
    result = _run_detector(repo)
    assert "REGRESSION SILENCIEUSE" in result.stdout
    assert "image/png" in result.stdout
    assert "audio/mpeg" in result.stdout


def test_explicit_path_mode(tmp_path: Path) -> None:
    """Mode chemin-explicite : cible un .ipynb precis, pas de delta git."""
    nb = _notebook_with_media([("image/png", 100)])
    nb_path = tmp_path / "explicit.ipynb"
    nb_path.write_text(json.dumps(nb))
    result = subprocess.run(
        [sys.executable, str(SCRIPT), str(nb_path)],
        capture_output=True,
        text=True,
    )
    # Mode chemin-explicite : pas de base, donc les medias detectes a
    # la tete sont consideres comme AJOUTS (info, pas finding).
    # --check reste vert (pas de regression silencieuse stricte).
    assert result.returncode == 0
    assert "AJOUTS" in result.stdout or "0 finding" in result.stdout
    assert "REGRESSION SILENCIEUSE" not in result.stdout


def test_no_modified_notebooks(tmp_path: Path) -> None:
    """delta git avec 0 notebook modifie -> message 'Aucun'."""
    repo = tmp_path / "empty_repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    readme = repo / "README.md"
    readme.write_text("# nothing here\n")
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=repo, check=True)
    result = _run_detector(repo)
    assert "Aucun notebook" in result.stdout
    assert result.returncode == 0