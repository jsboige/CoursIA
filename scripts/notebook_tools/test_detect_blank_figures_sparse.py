#!/usr/bin/env python3
"""Tests de non-regression pour detect_blank_figures.py : degenerescence + advisory sparse-grid (#10319).

Construit des grilles synthetiques (PIL) reproduisant le cas fondateur #10305
(grille 4x4 dont 2 rangees quasi-uniformes + 2 rangees riches) et les verrous
anti-FP (grille entierement riche, grille entierement vide, petite figure).
"""
from __future__ import annotations

import base64
import io
import json
import random
import sys
from pathlib import Path

import pytest

# Rendre le package importable quel que soit le cwd d'execution.
sys.path.insert(0, str(Path(__file__).resolve().parent))

import detect_blank_figures as dbf  # noqa: E402

pil = pytest.importorskip("PIL.Image", reason="Pillow requis pour les tests sparse-grid")


# ---------------------------------------------------------------------------
# Helpers : construction d'images synthetiques
# ---------------------------------------------------------------------------


def _png_bytes(im) -> bytes:
    """Encode a PIL image as PNG bytes."""
    buf = io.BytesIO()
    im.save(buf, format="PNG")
    return buf.getvalue()


def _rich_tile(size=128, seed=0):
    """Une tuile riche en couleurs (bruit RGB pseudo-aleatoire) -> centaines de couleurs."""
    rng = random.Random(seed)
    im = pil.new("RGB", (size, size))
    px = im.load()
    for y in range(size):
        for x in range(size):
            px[x, y] = (rng.randint(0, 255), rng.randint(0, 255), rng.randint(0, 255))
    return im


def _uniform_tile(color=(230, 220, 200), size=128):
    """Une tuile quasi-uniforme (beige plein) -> 1 couleur."""
    return pil.new("RGB", (size, size), color)


def _grid(rows: int, cols: int, tile_size=128, empty_rows=0, seed=0) -> "pil.Image":
    """Assemble une grille rows x cols de tuiles.

    Les ``empty_rows`` premieres rangees sont quasi-uniformes (beige), le reste
    est riche. ``empty_rows=0`` => grille entierement riche.
    """
    cell = _rich_tile(tile_size, seed=seed)
    blank = _uniform_tile(size=tile_size)
    grid = pil.new("RGB", (cols * tile_size, rows * tile_size))
    for r in range(rows):
        for c in range(cols):
            src = blank if r < empty_rows else cell
            # Vary the rich tile seed per position so colors differ across cells.
            if r >= empty_rows:
                src = _rich_tile(tile_size, seed=seed + r * cols + c)
            grid.paste(src, (c * tile_size, r * tile_size))
    return grid


def _nb_with_image(raw_png: bytes) -> dict:
    """Notebook minimal avec une cellule code portant une sortie image/png."""
    b64 = base64.b64encode(raw_png).decode("ascii")
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [
                    {
                        "output_type": "display_data",
                        "data": {"image/png": b64},
                    }
                ],
            }
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
    }


# ---------------------------------------------------------------------------
# _parse_tiles / _auto_tiles
# ---------------------------------------------------------------------------


def test_parse_tiles_rxc():
    assert dbf._parse_tiles("4x4") == (4, 4)
    assert dbf._parse_tiles("2x3") == (2, 3)
    assert dbf._parse_tiles("1x1") == (1, 1)


def test_parse_tiles_auto_and_none():
    assert dbf._parse_tiles(None) is None
    assert dbf._parse_tiles("auto") is None


@pytest.mark.parametrize("bad", ["4", "4x", "x4", "4by4", "0x4", "4x0", "-1x2"])
def test_parse_tiles_rejects_malformed(bad):
    with pytest.raises(ValueError):
        dbf._parse_tiles(bad)


def test_auto_tiles_large_square():
    assert dbf._auto_tiles(800, 800) == (4, 4)


def test_auto_tiles_too_small_returns_none():
    assert dbf._auto_tiles(300, 300) is None
    assert dbf._auto_tiles(399, 800) is None


def test_auto_tiles_elongated_horizontal():
    # w >= 3*h => etire les colonnes
    assert dbf._auto_tiles(1500, 400) == (4, 8)


def test_auto_tiles_elongated_vertical():
    assert dbf._auto_tiles(400, 1500) == (8, 4)


# ---------------------------------------------------------------------------
# _tile_color_counts : uniforme vs riche
# ---------------------------------------------------------------------------


def test_tile_color_counts_uniform_vs_rich():
    grid = _grid(4, 4, empty_rows=2)  # 2 rangees uniformes, 2 riches
    counts = dbf._tile_color_counts(grid, 4, 4)
    assert len(counts) == 4 and all(len(row) == 4 for row in counts)
    flat = [c for row in counts for c in row]
    uniform = [c for c in flat if c < dbf.SPARSE_TILE_MIN_COLORS]
    rich = [c for c in flat if c >= dbf.SPARSE_TILE_MIN_COLORS]
    assert len(uniform) == 8, "2 rangees x 4 cols = 8 tuiles uniformes attendues"
    assert len(rich) == 8, "2 rangees x 4 cols = 8 tuiles riches attendues"
    assert uniform[0] == 1, "une tuile beige pleine = exactement 1 couleur"


# ---------------------------------------------------------------------------
# _sparse_grid_finding : cas fondateur #10305 et anti-FP
# ---------------------------------------------------------------------------


def test_sparse_grid_flags_partially_empty_4x4():
    """Cas fondateur #10305 : 4x4 avec 2 rangees quasi-uniformes -> signale."""
    grid = _grid(4, 4, empty_rows=2)
    raw = _png_bytes(grid)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=(4, 4))
    assert finding is not None
    assert finding["kind"] == "sparse_grid"
    assert finding["advisory"] is True
    assert finding["uniform_tiles"] == 8
    assert finding["total_tiles"] == 16
    assert finding["uniform_fraction"] == 0.5


def test_sparse_grid_does_not_flag_fully_rich():
    """Une grille entierement riche ne doit PAS etre signalee (pas de defaut)."""
    grid = _grid(4, 4, empty_rows=0)
    raw = _png_bytes(grid)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=(4, 4))
    assert finding is None


def test_sparse_grid_does_not_flag_fully_uniform():
    """Une image entierement uniforme n'est PAS le defaut vise (pas de contraste)."""
    grid = _uniform_tile(size=512)
    raw = _png_bytes(grid)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=(4, 4))
    assert finding is None


def test_sparse_grid_tolerates_one_empty_subplot():
    """Un seul subplot vide dans une 2x2 (25%) < seuil 40% -> NON signale (legitime)."""
    grid = _grid(2, 2, empty_rows=1)  # rangee 0 = uniforme => 2/4 = 50% ... trop
    # Pour un vrai cas 25%, construire 1 seule tuile vide sur 4 :
    cell = _rich_tile(128, seed=7)
    blank = _uniform_tile(size=128)
    g = pil.new("RGB", (256, 256))
    g.paste(blank, (0, 0))  # 1 tuile vide
    g.paste(cell, (128, 0))
    g.paste(_rich_tile(128, seed=8), (0, 128))
    g.paste(_rich_tile(128, seed=9), (128, 128))
    raw = _png_bytes(g)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=(2, 2))
    assert finding is None, "1/4 uniforme = 25% < 40% seuil => legitime, non signale"


def test_sparse_grid_adaptive_default_large_image():
    """Sans --tiles explicite, une grande image utilise la grille auto (4x4)."""
    grid = _grid(4, 4, empty_rows=2, tile_size=160)  # 640x640 >= SPARSE_AUTO_MIN_DIM
    raw = _png_bytes(grid)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=None)
    assert finding is not None
    assert finding["tiles"] == [4, 4]


def test_sparse_grid_adaptive_skips_small_image():
    """Une petite image (< SPARSE_AUTO_MIN_DIM) sans --tiles explicite -> non signalee."""
    grid = _grid(4, 4, empty_rows=2, tile_size=50)  # 200x200 < 400
    raw = _png_bytes(grid)
    finding = dbf._sparse_grid_finding("image/png", raw, tiles=None)
    assert finding is None


# ---------------------------------------------------------------------------
# Degenerescence (hard check) inchangee par l'ajout sparse
# ---------------------------------------------------------------------------


def test_degenerate_1x1_still_flagged_hard():
    """Le PNG 1x1 (cas #6891) reste un finding hard, pas advisory."""
    raw = _png_bytes(pil.new("RGB", (1, 1), (255, 255, 255)))
    finding = dbf._classify_image("image/png", raw, dbf.MIN_DIM, dbf.MIN_BYTES)
    assert finding is not None
    assert finding["kind"] == "degenerate"
    assert "advisory" not in finding or finding.get("advisory") is False or True
    # degenerate findings n'ont pas le flag advisory :
    assert finding.get("advisory") is None or finding.get("advisory") is False


def test_degenerate_check_unaffected_by_sparse_layer():
    """detect_cell avec tiles active ne casse pas la detection hard."""
    raw = _png_bytes(pil.new("RGB", (1, 1), (0, 0, 0)))
    cell = {"outputs": [{"data": {"image/png": base64.b64encode(raw).decode()}}]}
    findings = dbf.detect_cell(cell, tiles=(4, 4))
    assert len(findings) == 1
    assert findings[0]["kind"] == "degenerate"


# ---------------------------------------------------------------------------
# scan_notebook : split hits / sparse
# ---------------------------------------------------------------------------


def test_scan_notebook_splits_hits_and_sparse(tmp_path):
    """Une grille partiellement vide -> sparse[], pas hits[] ; --check reste vert."""
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    res = dbf.scan_notebook(p, tiles=(4, 4))
    assert res["hits"] == [], "une grille riche/grande n'est pas 'degeneree' hard"
    assert len(res["sparse"]) == 1
    assert res["sparse"][0]["kind"] == "sparse_grid"
    assert res["sparse"][0]["cell_index"] == 0


def test_scan_notebook_no_sparse_without_tiles_flag(tmp_path):
    """Sans --sparse/--tiles, aucun finding sparse (comportement defaut inchange)."""
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    res = dbf.scan_notebook(p)  # tiles=None
    assert res["hits"] == []
    assert res["sparse"] == []


# ---------------------------------------------------------------------------
# CLI : --check vs --check-sparse
# ---------------------------------------------------------------------------


def test_cli_check_does_not_fail_on_sparse(tmp_path, capsys):
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    # --check (hard only) doit rester a 0 : pas de figure degeneree, juste advisory.
    rc = dbf.main([str(p), "--sparse", "--tiles", "4x4", "--check"])
    captured = capsys.readouterr()
    assert rc == 0, f"--check ne doit pas echouer sur advisory. stdout:\n{captured.out}"
    assert "Sparse-grid (adv)  : 1" in captured.out


def test_cli_check_sparse_fails_on_sparse(tmp_path, capsys):
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    rc = dbf.main([str(p), "--sparse", "--tiles", "4x4", "--check-sparse"])
    assert rc == 1, "--check-sparse doit echouer (exit 1) sur un finding sparse"


def test_cli_check_sparse_clean_on_rich_grid(tmp_path):
    grid = _grid(4, 4, empty_rows=0)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    rc = dbf.main([str(p), "--sparse", "--tiles", "4x4", "--check-sparse"])
    assert rc == 0


def test_cli_json_payload_has_sparse_field(tmp_path, capsys):
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    rc = dbf.main([str(p), "--sparse", "--tiles", "4x4", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["total_hits"] == 0
    assert payload["total_sparse"] == 1
    assert payload["results"][0]["sparse"][0]["uniform_fraction"] == 0.5


def test_cli_tiles_implies_sparse(tmp_path, capsys):
    """--tiles sans --sparse active quand meme la couche advisory."""
    grid = _grid(4, 4, empty_rows=2)
    nb = _nb_with_image(_png_bytes(grid))
    p = tmp_path / "fake.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    dbf.main([str(p), "--tiles", "4x4", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["total_sparse"] == 1


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
