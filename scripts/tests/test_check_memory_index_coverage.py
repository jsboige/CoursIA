"""Tests for scripts/coordination/check_memory_index_coverage.py (#17885).

Trois cas : OK, FAIL (orphelin), FAIL (lien cassé).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "coordination" / "check_memory_index_coverage.py"


def _run(tmp_path: Path, mem_text: str) -> dict:
    """Build a minimal memory/ directory and invoke the script."""
    (tmp_path / "MEMORY.md").write_text(mem_text, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "beta.md").write_text("# beta", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    out = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--memory-dir",
            str(tmp_path),
            "--json",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert out.returncode in (0, 1), f"unexpected rc={out.returncode}: stderr={out.stderr}"
    return json.loads(out.stdout)


def test_full_coverage_ok(tmp_path: Path) -> None:
    """All files referenced => verdict OK, rc=0."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
        "- [gamma](gamma.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "OK"
    assert report["orphan_count"] == 0
    assert report["broken_link_count"] == 0
    assert report["total_files"] == 3
    assert report["referenced_files"] == 3


def test_orphan_detected(tmp_path: Path) -> None:
    """gamma.md non referenced => orphan, verdict FAIL."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "FAIL"
    assert report["orphan_count"] == 1
    assert "gamma.md" in report["orphan_files"]
    assert report["referenced_files"] == 2


def test_broken_link_detected(tmp_path: Path) -> None:
    """Lien vers missing.md qui n'existe pas => broken_link, verdict FAIL."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
        "- [gamma](gamma.md)\n"
        "- [missing](missing.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "FAIL"
    assert report["broken_link_count"] == 1
    assert any(u == "missing.md" for _, u in report["broken_links"])


def test_real_memory_dir() -> None:
    """Vérifie que l'organe fonctionne contre le MEMORY.md de la machine."""
    import os

    real_dir = Path(
        r"C:\Users\Jesse\.claude\projects\d--dev-CoursIA-2\memory"
    )
    if not real_dir.exists():
        return  # CI sans le bon chemin
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(real_dir), "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    report = json.loads(out.stdout)
    # MEMORY.md reel : on accepte OK ou FAIL (c.874 travaille a couverture 100%)
    assert report["verdict"] in ("OK", "FAIL")
    assert report["total_files"] > 100  # au moins 100 fichiers de Tells
