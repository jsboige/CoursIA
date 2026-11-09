"""Tests de scan_slidev_overflow (EPIC #11508 L2) — PNG synthétiques couvrant les verdicts."""

import sys
from pathlib import Path

from PIL import Image, ImageDraw

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scan_slidev_overflow import main, scan_export_dir  # noqa: E402


def _png(path: Path, w: int, h: int, rects):
    """Écrit un PNG blanc avec des rectangles noirs (x0, y0, x1, y1)."""
    img = Image.new("L", (w, h), 255)
    draw = ImageDraw.Draw(img)
    for x0, y0, x1, y1 in rects:
        draw.rectangle([x0, y0, x1, y1], fill=0)
    img.save(path)


def _make_export(root: Path):
    d = root / "export"
    d.mkdir()
    # 1.png : contenu au centre, bas propre -> pas de débordement
    _png(d / "1.png", 200, 100, [(20, 20, 180, 60)])
    # 2.png : barre noire mordant les 2 dernières lignes sur 60 % de la largeur
    _png(d / "2.png", 200, 100, [(20, 20, 140, 99)])
    # 3.png : encre uniquement dans la bande droite ignorée (numéro de page)
    _png(d / "3.png", 200, 100, [(185, 97, 195, 99)])
    return d


def test_overflow_detected_and_clean_passed(tmp_path):
    report = scan_export_dir(_make_export(tmp_path), rows=6, threshold=0.01,
                             ignore_right_frac=0.10)
    verdicts = {s["slide"]: s["overflow"] for s in report["slides"]}
    assert verdicts == {"1.png": False, "2.png": True, "3.png": False}


def test_natural_sort_order(tmp_path):
    d = _make_export(tmp_path)
    _png(d / "10.png", 200, 100, [(20, 20, 180, 60)])
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    assert [s["slide"] for s in report["slides"]] == ["1.png", "2.png", "3.png", "10.png"]


def test_page_number_zone_is_measured_when_not_ignored(tmp_path):
    """Sans bande ignorée, l'encre du numéro de page compte : garde anti-régression
    du choix --ignore-right-frac par défaut (sinon toute slide numérotée déborde)."""
    report = scan_export_dir(_make_export(tmp_path), rows=6, threshold=0.01,
                             ignore_right_frac=0.0)
    verdicts = {s["slide"]: s["overflow"] for s in report["slides"]}
    assert verdicts["3.png"] is True


def test_unreadable_png_reported_not_silent(tmp_path):
    d = _make_export(tmp_path)
    (d / "corrupt.png").write_bytes(b"pas un png")
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    names = [u["slide"] for u in report["unreadable"]]
    assert names == ["corrupt.png"]
    assert len(report["slides"]) == 3  # les lisibles restent mesurées


def test_missing_dir_is_a_named_error(tmp_path):
    try:
        scan_export_dir(tmp_path / "absent", rows=6, threshold=0.01,
                        ignore_right_frac=0.10)
        raised = False
    except FileNotFoundError:
        raised = True
    assert raised


def test_empty_dir_is_a_named_error(tmp_path):
    d = tmp_path / "vide"
    d.mkdir()
    try:
        scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
        raised = False
    except FileNotFoundError:
        raised = True
    assert raised


def test_main_exit_codes(tmp_path, capsys):
    d = _make_export(tmp_path)
    assert main([str(d)]) == 1        # un débordement mesuré -> exit 1
    assert main([str(d), "--json"]) == 1
    assert main([str(tmp_path / "absent")]) == 2  # entrée illisible -> exit 2
    out = capsys.readouterr().out
    assert "1/3 slides OVERFLOW" in out
