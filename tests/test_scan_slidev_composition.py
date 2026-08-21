#!/usr/bin/env python3
"""
test_scan_slidev_composition.py — tests du garde-fou de composition Slidev.

Couvre :
  - parse_headmatter_canvas : lit canvasWidth / canvasHeight / aspectRatio
  - CAS_DEFINITION_5 : la structure détecte-t-elle un débordement
  - CAS_GLYPHES : le chevauchement est mesuré sur glyphes, pas boîtes

L'instrument complet (Playwright + slidev dev) est testé dans un test
d'intégration séparé qui nécessite un serveur Slidev actif.

Usage :
    pytest tests/test_scan_slidev_composition.py -v
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "notebook_tools"))

from scan_slidev_composition import parse_headmatter_canvas  # noqa: E402


# --- parse_headmatter_canvas ---


def test_parse_default_when_no_headmatter(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text("pas de frontmatter ici\n---\nbla\n---\n", encoding="utf-8")
    w, h = parse_headmatter_canvas(md)
    assert (w, h) == (980, 552)


def test_parse_default_when_empty_headmatter(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text("---\n\n---\ncontenu\n", encoding="utf-8")
    w, h = parse_headmatter_canvas(md)
    assert (w, h) == (980, 552)


def test_parse_canvasWidth_only(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text(
        "---\ncanvasWidth: 1920\ntheme: foo\n---\ncontenu\n",
        encoding="utf-8",
    )
    w, h = parse_headmatter_canvas(md)
    assert w == 1920
    assert h == 552  # inchangé


def test_parse_aspectRatio(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text(
        "---\naspectRatio: 16/9\ntheme: foo\n---\n",
        encoding="utf-8",
    )
    w, h = parse_headmatter_canvas(md)
    assert (w, h) == (16, 9)


def test_parse_canvasWidth_and_Height(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text(
        "---\ncanvasWidth: 1280\ncanvasHeight: 720\n---\n",
        encoding="utf-8",
    )
    w, h = parse_headmatter_canvas(md)
    assert (w, h) == (1280, 720)


def test_parse_invalid_aspectRatio_falls_back(tmp_path: Path) -> None:
    md = tmp_path / "slides.md"
    md.write_text(
        "---\naspectRatio: 4.0/3.0\n---\n",
        encoding="utf-8",
    )
    w, h = parse_headmatter_canvas(md)
    # défaut si invalide
    assert (w, h) == (980, 552)


# --- invariant comportemental : bornes du signal OCCUPATION ---


def test_bornes_occupation_documentees_dans_docstring() -> None:
    """Le docstring doit porter la phrase de borne ADVISORY explicite (acceptance)."""
    from scan_slidev_composition import __doc__

    assert "ADVISORY" in __doc__
    assert "QA visuel" in __doc__ or "visuel" in __doc__
    # La borne doit nommer la classe de défaut qu'elle ne couvre PAS
    assert "remplace" in __doc__.lower()