"""Tests du module extract_readme_figures (EPIC #5654 P0).

Couvre (stdlib + PIL optionnel) :
* ``_png_dimensions`` depuis l'en-tete IHDR (PNG 1x1 et 2x3 synthetiques sans PIL) ;
* ``list_figures`` : inventaire exhaustif d'une mini-serie de 2 notebooks ;
* ``extract_figure`` : extraction + ``MANIFEST.md`` + idempotence (pas de doublon) ;
* alt-text FR obligatoire (regle HARD accessibilite #5654) ;
* bornes : cell_index / output_index hors plage, output sans PNG ;
* ``_optimize_with_pil`` : downscale respecte ``max_dim`` quand PIL present.

Les PNG de test sont construits en stdlib (``zlib`` + ``struct``) pour prouver
que le module marche SANS PIL (le chemin de parsing IHDR est exerce directement).
"""

import base64
import json
import os
import struct
import sys
import zlib
from pathlib import Path

import pytest

sys.path.insert(
    0, os.path.join(os.path.dirname(__file__), "..", "notebook_tools"))

from extract_readme_figures import (  # noqa: E402
    MAX_BYTES_DEFAULT,
    _optimize_with_pil,
    _png_dimensions,
    extract_figure,
    list_figures,
    resolve_repo_path,
)


# ----------------------------------------------------------- helpers PNG stdlib
def _make_png(width: int, height: int, rgb=(255, 0, 0), noise: bool = False) -> bytes:
    """PNG minimal RGB valide (stdlib ``zlib`` + ``struct``, sans PIL).

    ``noise=True`` : pixels pseudo-aleatoires deterministes (LCG seed fixe) ->
    IDAT incompressible, utile pour generer un PNG depassant le plafond poids
    (sinon zlib compresse une image unie a quelques centaines d'octets).
    """
    magic = b"\x89PNG\r\n\x1a\n"

    def _chunk(typ: bytes, data: bytes) -> bytes:
        crc = zlib.crc32(typ + data) & 0xFFFFFFFF
        return struct.pack(">I", len(data)) + typ + data + struct.pack(">I", crc)

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)  # 8-bit RGB

    def _row(y: int) -> bytes:
        if not noise:
            return b"\x00" + bytes(rgb) * width
        # LCG deterministe : evite la dependance a random (determinisme test).
        state = (y * 2654435761) & 0xFFFFFFFF
        out = bytearray(b"\x00")
        for _ in range(width * 3):
            state = (state * 1103515245 + 12345) & 0x7FFFFFFF
            out.append(state & 0xFF)
        return bytes(out)

    raw = b"".join(_row(y) for y in range(height))
    # noise=True : level 0 (deflate store) -> IDAT ~= raw size, incompressible
    # (un PNG bruite doit VRAIMENT depasser le plafond poids, pas se faire
    # retracter par zlib). Sinon level 6 par defaut (image unie -> quelques octets).
    idat = zlib.compress(raw, level=0 if noise else 6)
    return magic + _chunk(b"IHDR", ihdr) + _chunk(b"IDAT", idat) + _chunk(b"IEND", b"")


def _write_nb_with_figure(path: Path, png_bytes: bytes, preamble_cells: int = 1):
    """Notebook avec ``preamble_cells`` cellules vides puis la cellule-figure.

    La figure est donc a ``cell_index = preamble_cells`` (teste l'indexation).
    """
    b64 = base64.b64encode(png_bytes).decode("ascii")
    cells = [{
        "cell_type": "code", "execution_count": 1,
        "source": [f"# preamble {i}\n"], "outputs": [], "metadata": {},
    } for i in range(preamble_cells)]
    cells.append({
        "cell_type": "code", "execution_count": 1,
        "source": ["import matplotlib.pyplot as plt\n"],
        "outputs": [{
            "output_type": "display_data",
            "data": {"image/png": b64},
            "metadata": {},
        }],
        "metadata": {},
    })
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ----------------------------------------------------------- _png_dimensions
def test_png_dimensions_1x1():
    dims = _png_dimensions(_make_png(1, 1))
    assert dims == (1, 1)


def test_png_dimensions_2x3():
    dims = _png_dimensions(_make_png(2, 3))
    assert dims == (2, 3)


def test_png_dimensions_non_png_returns_none():
    assert _png_dimensions(b"not a png") is None
    assert _png_dimensions(b"") is None


# ----------------------------------------------------------- list_figures
def test_list_figures_inventorie_deux_notebooks(tmp_path):
    serie = tmp_path / "MiniSerie"
    _write_nb_with_figure(serie / "nbA.ipynb", _make_png(2, 2), preamble_cells=1)
    _write_nb_with_figure(serie / "sub" / "nbB.ipynb", _make_png(3, 4), preamble_cells=0)
    inv = list_figures(serie)
    assert inv["serie"] == "MiniSerie"
    assert inv["n_notebooks_with_figures"] == 2
    assert inv["n_figures"] == 2
    assert inv["total_bytes"] > 0
    paths = [Path(r["notebook"]).name for r in inv["figures"]]
    assert set(paths) == {"nbA.ipynb", "nbB.ipynb"}
    # dimensions lues via IHDR
    by_name = {Path(r["notebook"]).name: r for r in inv["figures"]}
    assert (by_name["nbA.ipynb"]["width"], by_name["nbA.ipynb"]["height"]) == (2, 2)
    assert (by_name["nbB.ipynb"]["width"], by_name["nbB.ipynb"]["height"]) == (3, 4)


def test_list_figures_ignore_checkpoints(tmp_path):
    serie = tmp_path / "S"
    _write_nb_with_figure(serie / "nb.ipynb", _make_png(1, 1))
    # un jumeau dans .ipynb_checkpoints doit etre ignore
    _write_nb_with_figure(
        serie / ".ipynb_checkpoints" / "nb-checkpoint.ipynb", _make_png(1, 1))
    inv = list_figures(serie)
    assert inv["n_figures"] == 1


def test_list_figures_over_weight_flag(tmp_path):
    serie = tmp_path / "S"
    # PNG bruite (incompressible) : depasse reellement les 200 KB de plafond.
    big = _make_png(320, 320, noise=True)
    _write_nb_with_figure(serie / "big.ipynb", big)
    inv = list_figures(serie)
    assert len(inv["figures"]) == 1
    assert inv["figures"][0]["bytes"] > MAX_BYTES_DEFAULT   # sanity du fixture
    assert inv["figures"][0]["over_weight"] is True


def test_list_figures_missing_dir_raises():
    with pytest.raises(FileNotFoundError):
        list_figures("/no/such/serie/here")


# ----------------------------------------------------------- extract_figure
def test_extract_figure_writes_png_and_manifest(tmp_path):
    serie = tmp_path / "S"
    nb = _write_nb_with_figure(serie / "nb.ipynb", _make_png(5, 5), preamble_cells=1)
    assets = serie / "assets" / "readme"
    out = assets / "fig.png"
    entry = extract_figure(
        nb, cell_index=1, output_index=0, output_path=out,
        alt_text_fr="Carte de chaleur des poids du reseau",
        serie_root=serie,
    )
    assert out.exists() and out.read_bytes()[:8] == b"\x89PNG\r\n\x1a\n"
    assert entry["used_pil"] in (True, False)          # depend de l'env
    assert entry["over_weight"] is False               # 5x5 < 200 KB
    manifest = assets / "MANIFEST.md"
    assert manifest.exists()
    body = manifest.read_text(encoding="utf-8")
    assert "fig.png" in body
    assert "MANIFEST des figures README" in body       # header
    assert "Carte de chaleur des poids du reseau" in body
    assert "cellule 1" in body and "output 0" in body
    # chemin relatif depuis serie_root dans le manifest
    assert "nb.ipynb" in body and str(serie.resolve()) not in body


def test_extract_figure_idempotent_no_duplicate(tmp_path):
    serie = tmp_path / "S"
    # preamble_cells=0 : la figure est a cell_index=0.
    nb = _write_nb_with_figure(serie / "nb.ipynb", _make_png(3, 3), preamble_cells=0)
    assets = serie / "assets" / "readme"
    out = assets / "fig.png"
    extract_figure(nb, 0, 0, out, " premiere extraction ", serie_root=serie)
    extract_figure(nb, 0, 0, out, "deuxieme extraction (remplace)", serie_root=serie)
    body = (assets / "MANIFEST.md").read_text(encoding="utf-8")
    # un seul bloc ## fig.png (remplacement, pas de doublon)
    assert body.count("## fig.png") == 1
    assert "deuxieme extraction (remplace)" in body


def test_extract_figure_alt_text_required(tmp_path):
    serie = tmp_path / "S"
    nb = _write_nb_with_figure(serie / "nb.ipynb", _make_png(2, 2))
    with pytest.raises(ValueError, match="alt_text_fr"):
        extract_figure(nb, 0, 0, serie / "assets/readme/f.png", "",
                       serie_root=serie)
    with pytest.raises(ValueError, match="alt_text_fr"):
        extract_figure(nb, 0, 0, serie / "assets/readme/f.png", "   ",
                       serie_root=serie)


def test_extract_figure_cell_out_of_range(tmp_path):
    serie = tmp_path / "S"
    nb = _write_nb_with_figure(serie / "nb.ipynb", _make_png(2, 2))  # 1 cell (index 0)
    with pytest.raises(ValueError, match="cell_index"):
        extract_figure(nb, 5, 0, serie / "assets/readme/f.png", "alt",
                       serie_root=serie)


def test_extract_figure_output_no_png(tmp_path):
    serie = tmp_path / "S"
    nb = {"cells": [{
        "cell_type": "code", "execution_count": 1, "source": ["print(1)\n"],
        "outputs": [{"output_type": "stream", "name": "stdout",
                     "text": ["1\n"]}],
        "metadata": {},
    }], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    nbp = serie / "nb.ipynb"
    nbp.parent.mkdir(parents=True, exist_ok=True)
    nbp.write_text(json.dumps(nb), encoding="utf-8")
    with pytest.raises(ValueError, match="ne porte pas de PNG"):
        extract_figure(nbp, 0, 0, serie / "assets/readme/f.png", "alt",
                       serie_root=serie)


# ----------------------------------------------------------- _optimize_with_pil
def test_optimize_downscale_respects_max_dim():
    pil = pytest.importorskip("PIL")  # skip si PIL absent
    raw = _make_png(800, 600)
    opt, used_pil = _optimize_with_pil(raw, max_dim=200)
    assert used_pil is True
    w, h = _png_dimensions(opt)
    # le grand cote (800) doit etre ramene a <= 200
    assert max(w, h) <= 200


def test_optimize_raw_fallback_on_garbage():
    # bytes non-PNG : _optimize_with_pil retombe sur raw sans lever
    opt, used_pil = _optimize_with_pil(b"garbage not png", max_dim=100)
    assert used_pil is False
    assert opt == b"garbage not png"


# ----------------------------------------------------------- resolve_repo_path (F2)
def _make_fake_repo(tmp_path, nb_name="x.ipynb"):
    """Repo factice : <repo>/MyIA.AI.Notebooks/RL/<nb> existe sur disque."""
    repo = tmp_path / "repo"
    nb = repo / "MyIA.AI.Notebooks" / "RL" / nb_name
    nb.parent.mkdir(parents=True, exist_ok=True)
    nb.write_bytes(b"fake notebook")
    return repo, nb


def test_resolve_repo_path_absolute_passthrough(tmp_path):
    import os
    repo, nb = _make_fake_repo(tmp_path)
    abs_arg = str(nb.resolve())
    # path absolu -> retourne tel quel (Path egal, peu importe la string exacte)
    assert resolve_repo_path(abs_arg, repo).resolve() == nb.resolve()


def test_resolve_repo_path_full_repo_relative_no_double_prefix(tmp_path):
    # F2 core : repo-relatif complet ne doit PAS etre double-prefixe.
    repo, nb = _make_fake_repo(tmp_path)
    got = resolve_repo_path("MyIA.AI.Notebooks/RL/x.ipynb", repo)
    assert got.exists()                       # le path resout existe reellement
    assert got.resolve() == nb.resolve()
    # anti-regression : pas de "MyIA.AI.Notebooks/MyIA.AI.Notebooks" dans le path
    assert "MyIA.AI.Notebooks/MyIA.AI.Notebooks" not in str(got).replace("\\", "/")


def test_resolve_repo_path_serie_relative_fallback(tmp_path):
    # serie-relatif (RL/x.ipynb) -> prefixage MyIA.AI.Notebooks/ applique.
    repo, nb = _make_fake_repo(tmp_path)
    got = resolve_repo_path("RL/x.ipynb", repo)
    assert got.exists()
    assert got.resolve() == nb.resolve()
