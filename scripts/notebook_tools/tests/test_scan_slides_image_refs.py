"""Tests de scan_slides_image_refs (EPIC #11508 L4) — fixture couvrant les 4 classes."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scan_slides_image_refs import main, scan_slides_dir  # noqa: E402


def _make_deck(root: Path):
    deck = root / "slides" / "fixture-deck"
    (deck / "images").mkdir(parents=True)
    for n in ("a_active.png", "b_trapped.png", "c_marp.png", "d_nowhere.png"):
        (deck / "images" / n).write_bytes(b"x")
    (deck / "slides.md").write_text(
        "# deck\n\n"
        "![schema](images/a_active.png)\n"
        "<!-- Image: images/b_trapped.png -->\n",
        encoding="utf-8",
    )
    (deck / "slides.marp.md").write_text(
        "# marp\n![](images/c_marp.png)\n![](images/b_trapped.png)\n",
        encoding="utf-8",
    )
    # d_nowhere n'est referencee que dans le RECAP (exclu du scan) : NOWHERE
    (deck / "COURSE_RECAP_2026.md").write_text(
        "![](images/d_nowhere.png)\n", encoding="utf-8"
    )
    return deck


def test_four_classes(tmp_path):
    _make_deck(tmp_path)
    results = scan_slides_dir(tmp_path / "slides")
    assert len(results) == 1
    c = results[0]["classes"]
    assert c["ACTIVE"] == ["a_active.png"]
    assert c["COMMENT_TRAPPED"] == ["b_trapped.png"]
    assert c["MARP_ONLY"] == ["c_marp.png"]
    assert c["NOWHERE"] == ["d_nowhere.png"]
    assert results[0]["total"] == 4


def test_non_image_files_ignored(tmp_path):
    deck = _make_deck(tmp_path)
    (deck / "images" / "notes.txt").write_text("pas une image", encoding="utf-8")
    results = scan_slides_dir(tmp_path / "slides")
    assert results[0]["total"] == 4


def test_main_table_and_json(tmp_path, capsys):
    _make_deck(tmp_path)
    rc = main(["--repo", str(tmp_path)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "fixture-deck" in out
    assert "TOTAL 4 fichiers | actifs 1 (25%)" in out

    rc = main(["--repo", str(tmp_path), "--json"])
    import json

    data = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert data["grand_total"] == 4
    assert data["totals"] == {
        "ACTIVE": 1,
        "COMMENT_TRAPPED": 1,
        "MARP_ONLY": 1,
        "NOWHERE": 1,
    }


def test_main_single_deck(tmp_path, capsys):
    _make_deck(tmp_path)
    rc = main(["--repo", str(tmp_path), "--deck", "fixture-deck"])
    assert rc == 0
    assert "fixture-deck" in capsys.readouterr().out
