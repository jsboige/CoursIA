"""Tests de scan_slidev_overflow (EPIC #11508 L2) — PNG synthétiques couvrant les verdicts."""

import hashlib
import json
import sys
from pathlib import Path

from PIL import Image, ImageDraw

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scan_slidev_overflow import (  # noqa: E402
    archive_report,
    compare_artifacts,
    main,
    scan_export_dir,
)


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


# --- opposabilite d'un releve (#24171) -------------------------------------

def test_report_carries_the_font_dependency_and_the_machine(tmp_path):
    """Le releve dit sur QUELLE machine il a ete pris et qu'il n'est pas
    opposable d'une machine a l'autre : sans cette ligne, deux releves
    divergents se comparent sans que personne ne le sache (#24171)."""
    report = scan_export_dir(_make_export(tmp_path), rows=6, threshold=0.01,
                             ignore_right_frac=0.10)
    assert "polices systeme" in report["font_dependency"]
    assert set(report["platform"]) >= {"system", "release", "machine"}


def test_archive_carries_the_hash_of_every_measured_png(tmp_path):
    d = _make_export(tmp_path)
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    target = tmp_path / "releve.json"
    artifact = archive_report(report, target)
    assert target.is_file()
    saved = json.loads(target.read_text(encoding="utf-8"))
    assert saved["kind"] == "scan_slidev_overflow"
    assert set(saved["png_sha256"]) == {"1.png", "2.png", "3.png"}
    assert all(len(h) == 64 for h in saved["png_sha256"].values())
    assert artifact["artifact_sha256"]
    # l'artefact se verifie lui-meme : son contenu porte son empreinte
    assert saved["content_sha256"] == artifact["content_sha256"]
    body = {k: v for k, v in saved.items() if k != "content_sha256"}
    recomputed = hashlib.sha256(
        json.dumps(body, ensure_ascii=False, indent=2).encode("utf-8")
    ).hexdigest()
    assert recomputed == saved["content_sha256"]


def test_archive_is_written_with_lf_line_endings(tmp_path):
    """L'artefact doit etre byte-stable entre machines : `write_text` en mode
    texte sous Windows traduit ``\\n`` en ``\\r\\n``, si bien que deux
    archives identiques divergeaient sur deux OS -- un diff ligne-a-ligne
    verrait alors un ecart fantome (#24171, suggestion S1 de la review)."""
    d = _make_export(tmp_path)
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    target = tmp_path / "releve.json"
    archive_report(report, target)
    raw = target.read_bytes()
    assert b"\r\n" not in raw
    assert raw.endswith(b"\n")


def test_compare_separates_fixed_from_new(tmp_path):
    """Comparer deux artefacts = dire ce qui a ete corrige et ce qui est
    apparu ; c'est ce que deux compteurs rejoues ne permettent pas."""
    d = _make_export(tmp_path)
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    before = archive_report(report, tmp_path / "avant.json")

    # apres correction : 2.png ne deborde plus
    _png(d / "2.png", 200, 100, [(20, 20, 140, 60)])
    _png(d / "4.png", 200, 100, [(20, 20, 140, 99)])
    after_report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    after = archive_report(after_report, tmp_path / "apres.json")

    cmp = compare_artifacts(before, after)
    assert cmp["fixed"] == ["2.png"]
    assert cmp["new"] == ["4.png"]
    assert cmp["common_overflow"] == []
    # l'image de 2.png a change -- c'est attendu pour une diapositive corrigee,
    # et ca ne rend PAS la comparaison non concluante
    assert cmp["png_changed"] == ["2.png"]
    assert cmp["png_differ"] == []


def test_compare_warns_when_the_images_differ(tmp_path):
    """Une diapositive qui deborde dans les deux releves et dont l'image a
    change : on a compare deux rendus differents de la meme slide -- la
    comparaison n'y est pas concluante, l'avertissement le dit."""
    d = _make_export(tmp_path)
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    left = archive_report(report, tmp_path / "gauche.json")

    # 2.png deborde toujours, mais son rendu a change
    _png(d / "2.png", 200, 100, [(10, 10, 150, 99)])
    report2 = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    right = archive_report(report2, tmp_path / "droite.json")

    cmp = compare_artifacts(left, right)
    assert cmp["common_overflow"] == ["2.png"]
    assert cmp["png_differ"] == ["2.png"]


def test_main_compare_prints_and_exits_on_still_overflowing(tmp_path, capsys):
    d = _make_export(tmp_path)
    report = scan_export_dir(d, rows=6, threshold=0.01, ignore_right_frac=0.10)
    archive_report(report, tmp_path / "avant.json")
    archive_report(report, tmp_path / "apres.json")
    assert main(["--compare", str(tmp_path / "avant.json"),
                 str(tmp_path / "apres.json")]) == 1
    out = capsys.readouterr().out
    assert "overflow : 1 -> 1" in out
    assert "dependance" in out
    assert main(["--compare", str(tmp_path / "absent.json"),
                 str(tmp_path / "apres.json")]) == 2
