"""Tests pour scripts/roosync_archive_backfill.py.

Couvre :
- parse_frontmatter : format verbatim documente, tolerance champs manquants
- is_fallback_archive : pattern filename
- detect_fallback_archives : detection sur arborescence synthetique
- cmd_list : sortie formatee
- cmd_backfill : marquage idempotent
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "roosync_archive_backfill.py"

# --- Fixtures : frontmatter verbatim du body #8889 ---------------------------

SAMPLE_FRONTMATTER_FULL = """---
messageCount: 8
llmGenerated: false
fallbackTruncation: true
---
Contenu verbatim de l'archive (extrait)
"""

SAMPLE_FRONTMATTER_PARTIAL = """---
messageCount: 5
llmGenerated: false
---
Contenu
"""

SAMPLE_NO_FRONTMATTER = """Pas de frontmatter ici, juste du contenu libre.
"""

# --- Tests parse_frontmatter --------------------------------------------------

def test_parse_frontmatter_full():
    """Frontmatter complet : tous les champs sont parses."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_FRONTMATTER_FULL)
    assert fm.message_count == 8
    assert fm.llm_generated is False
    assert fm.fallback_truncation is True
    assert "messageCount" in fm.raw


def test_parse_frontmatter_partial():
    """Frontmatter partiel : champs absents = None, pas d'erreur."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_FRONTMATTER_PARTIAL)
    assert fm.message_count == 5
    assert fm.llm_generated is False
    assert fm.fallback_truncation is None  # absent


def test_parse_frontmatter_absent():
    """Pas de frontmatter : raw vide, tous champs None."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_NO_FRONTMATTER)
    assert fm.message_count is None
    assert fm.llm_generated is None
    assert fm.fallback_truncation is None
    assert fm.raw == {}


# --- Tests is_fallback_archive ------------------------------------------------

def test_is_fallback_archive_match():
    """Pattern documented #8889 : workspace-<name>-<ISO>-fallback.md."""
    from roosync_archive_backfill import is_fallback_archive
    assert is_fallback_archive(Path("workspace-CoursIA-2026-07-29T22-14-57-fallback.md"))
    assert is_fallback_archive(Path("workspace-machine-2-2026-09-21T16-30-00-fallback.md"))


def test_is_fallback_archive_no_match():
    """Fichiers non-fallback : nom ou pas de suffixe -fallback.md."""
    from roosync_archive_backfill import is_fallback_archive
    assert not is_fallback_archive(Path("workspace-CoursIA-2026-07-29T22-14-57.md"))
    assert not is_fallback_archive(Path("random_file.md"))
    assert not is_fallback_archive(Path("workspace-fallback.md"))  # pas d'ISO


# --- Tests detect_fallback_archives (integration) -----------------------------

def _make_archive(root: Path, name: str, *, llm: bool = False, fallback: bool = True,
                  messages: int = 5, body: str = "Verbatim content") -> Path:
    """Helper : cree une archive synthetique dans root."""
    archive = root / name
    archive.parent.mkdir(parents=True, exist_ok=True)
    archive.write_text(
        f"---\n"
        f"messageCount: {messages}\n"
        f"llmGenerated: {'true' if llm else 'false'}\n"
        f"fallbackTruncation: {'true' if fallback else 'false'}\n"
        f"---\n"
        f"{body}\n",
        encoding="utf-8",
    )
    return archive


def test_detect_fallback_archives_basic(tmp_path: Path):
    """Detection sur arborescence : 1 fallback reel, 1 normal (non-fallback)."""
    from roosync_archive_backfill import detect_fallback_archives
    root = tmp_path / "archive"
    # Fallback reel
    _make_archive(root, "workspace-test-2026-09-01T10-00-00-fallback.md")
    # Normal (pas de suffixe fallback)
    _make_archive(root, "workspace-test-2026-09-02T10-00-00.md", llm=True, fallback=False)
    # Fallback reel (autre workspace)
    _make_archive(root, "workspace-other-2026-09-03T11-00-00-fallback.md", messages=12)

    detected = detect_fallback_archives(root)
    assert len(detected) == 2
    isos = sorted(a.iso for a in detected)
    assert isos == ["2026-09-01T10-00-00", "2026-09-03T11-00-00"]


def test_detect_fallback_archives_filters_partial_metadata(tmp_path: Path):
    """Archives avec fallback=True mais llmGenerated=True : exclues (non-fallback reel)."""
    from roosync_archive_backfill import detect_fallback_archives
    root = tmp_path / "archive"
    _make_archive(root, "workspace-mixed-2026-09-01T10-00-00-fallback.md",
                  llm=True, fallback=True, messages=8)
    detected = detect_fallback_archives(root)
    assert len(detected) == 0


def test_detect_fallback_archives_empty_root(tmp_path: Path):
    """Racine inexistante : liste vide, pas d'erreur."""
    from roosync_archive_backfill import detect_fallback_archives
    detected = detect_fallback_archives(tmp_path / "nope")
    assert detected == []


# --- Tests subprocess : cmd_list, cmd_backfill --------------------------------

def test_cmd_list_via_subprocess(tmp_path: Path):
    """Le mode --list imprime le tableau agrege."""
    root = tmp_path / "archive"
    _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md", messages=8)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--list"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    assert "workspace-x" in result.stdout
    assert "TOTAL : 1 archives" in result.stdout


def test_cmd_report_via_subprocess(tmp_path: Path):
    """Le mode --report ecrit un JSON structure."""
    root = tmp_path / "archive"
    out = tmp_path / "out"
    _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md", messages=8)
    _make_archive(root, "workspace-x-2026-09-02T10-00-00-fallback.md", messages=12)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--report",
         "--output-dir", str(out)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    json_path = out / "roosync_archive_backfill_report.json"
    assert json_path.exists()
    report = json.loads(json_path.read_text(encoding="utf-8"))
    assert report["total_archives"] == 2
    assert "workspace-x" in report["workspaces"]


def test_cmd_backfill_via_subprocess(tmp_path: Path):
    """Le mode --backfill ajoute markForBackfill: true au frontmatter."""
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-z-2026-09-01T10-00-00-fallback.md", messages=5)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    text = target.read_text(encoding="utf-8")
    assert "markForBackfill: true" in text


def test_cmd_backfill_idempotent(tmp_path: Path):
    """Marquer 2 fois la meme archive : exit 0 + 'DEJA MARQUEE'."""
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-z-2026-09-01T10-00-00-fallback.md", messages=5)
    # Premier backfill
    subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
        check=True,
    )
    # Second backfill : doit detecter deja marquee
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0
    assert "DEJA MARQUEE" in result.stdout


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
