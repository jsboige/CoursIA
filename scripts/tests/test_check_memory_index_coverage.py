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


NL = chr(10)  # newline literal, heredoc-proof


def _run_args(tmp_path: Path, mem_text: str, extra_args: list) -> dict:
    """Comme _run mais avec des args CLI supplementaires."""
    (tmp_path / "MEMORY.md").write_text(mem_text, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "beta.md").write_text("# beta", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(tmp_path), "--json", *extra_args],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert out.returncode in (0, 1), f"unexpected rc={out.returncode}: stderr={out.stderr}"
    return json.loads(out.stdout)


def test_default_ceiling_oversize(tmp_path: Path) -> None:
    """MEMORY.md > 24 400 o au defaut #4204 => FAIL_OVERSIZE, rc=1."""
    line = "- [alpha](alpha.md)" + NL
    filler = "# Memoire" + NL + NL + (line * 1300)
    (tmp_path / "MEMORY.md").write_text(filler, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(tmp_path), "--json"],
        capture_output=True, text=True, encoding="utf-8",
    )
    report = json.loads(out.stdout)
    assert report["verdict"] == "FAIL_OVERSIZE"
    assert report["max_bytes"] == 24400
    assert out.returncode == 1


def test_alert_band_warns_without_failing(tmp_path: Path) -> None:
    """21 960 < taille <= 24 400 => size_alert vrai, verdict reste OK."""
    head = (
        "# Memoire" + NL + NL
        + "- [alpha](alpha.md)" + NL
        + "- [beta](beta.md)" + NL
        + "- [gamma](gamma.md)" + NL + NL
    )
    pad = "x" * (22500 - len(head))
    report = _run_args(tmp_path, head + pad, [])
    assert report["size_bytes"] > 21960
    assert report["size_bytes"] <= 24400
    assert report["size_alert"] is True
    assert report["verdict"] == "OK"


def test_no_max_bytes_binary_only(tmp_path: Path) -> None:
    """--no-max-bytes : pas de plafond, verdict binaire seul (pre-#4204)."""
    head = (
        "# Memoire" + NL + NL
        + "- [alpha](alpha.md)" + NL
        + "- [beta](beta.md)" + NL
        + "- [gamma](gamma.md)" + NL + NL
    )
    pad = "x" * (25000 - len(head))  # > 24 400 o
    report = _run_args(tmp_path, head + pad, ["--no-max-bytes"])
    assert report["max_bytes"] is None
    assert report["alert_bytes"] is None
    assert report["size_alert"] is False
    assert report["verdict"] == "OK"
