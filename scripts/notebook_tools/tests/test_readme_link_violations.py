"""Tests for the F2 of #18970 -- dump_readme_link_violations + diff comparator.

Why this test file exists
-------------------------
The guard is delta-only : the argv captures violations as JSON and the
delta_argv comparator decides the verdict. Without these tests, a refactor
of the JSON shape (e.g. dropping `class` or renaming `href`) would silently
break the comparator and the PR gate would stop catching NEW STALE_LINK
introductions. Pinned here :

  1. The JSON shape (classe / readme / href) is preserved end-to-end.
  2. A NEW violation injected in head (missing in base) flips the verdict
     to `exit=1` and emits `::error::STALE_LINK` on stderr.
  3. A PR that does not change violations passes (`exit=0`).
  4. The stderr/stdout split is what allows the workflow's own grep
     `2>&1 | grep -E '^::error::STALE_LINK '` to keep working (F1).

These are the four conditions that the merge-gate relies on. Touch them
with the corresponding test name visible in the diff.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
DUMP = REPO_ROOT / "scripts" / "notebook_tools" / "dump_readme_link_violations.py"
DIFF = REPO_ROOT / "scripts" / "notebook_tools" / "diff_readme_link_violations.py"


def _run_dump() -> dict:
    proc = subprocess.run(
        [sys.executable, str(DUMP)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, f"dump exit={proc.returncode} stderr={proc.stderr}"
    return json.loads(proc.stdout)


def _run_diff(base: dict, head: dict, tmp_path: Path) -> subprocess.CompletedProcess:
    base_p = tmp_path / "base.json"
    head_p = tmp_path / "head.json"
    base_p.write_text(json.dumps(base), encoding="utf-8")
    head_p.write_text(json.dumps(head), encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(DIFF), str(base_p), str(head_p)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def test_json_shape_preserved() -> None:
    payload = _run_dump()
    assert isinstance(payload, dict)
    assert isinstance(payload.get("violations"), list)
    assert payload["n_violations"] == len(payload["violations"])
    if payload["violations"]:
        v0 = payload["violations"][0]
        # Les trois cles sont exigees par le comparator (et par la garde
        # workflow qui grep `::error::<cls> <readme> -> <href>`).
        for key in ("class", "readme", "href"):
            assert key in v0, f"cle `{key}` absente du JSON : {v0}"
        # La classe est bornee aux 3 categories de regen_quarto_render.py
        # (cf scripts/regen_quarto_render.py l.440-460).
        assert v0["class"] in {"STALE_LINK", "BROKEN", "DEAD_RENDER"}


def test_dump_exits_zero_even_with_violations() -> None:
    # L'audit BRUT rend 2432 violations au 2026-10-03 ; argv ne doit PAS
    # en faire un rouge (sinon la phase 1 du fast-lane s'arreterait avant
    # d'avoir capture le JSON pour le comparator). Seul delta_argv tranche.
    payload = _run_dump()
    assert payload["n_violations"] > 0, "temoin casse : la branche ne contient pas le backlog attendu"


def test_diff_passes_when_no_new_violation(tmp_path: Path) -> None:
    base = _run_dump()
    head = dict(base)
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout


def test_diff_fails_on_injected_stale_link(tmp_path: Path) -> None:
    # Témoin F2 : une STALE_LINK injectée dans HEAD doit faire NOUVELLES=1
    # (=exit 1) -- c'est ce que la garde workflow vérifie en CI.
    base = _run_dump()
    head = dict(base)
    head["violations"] = list(base["violations"]) + [
        {"class": "STALE_LINK", "readme": "WITNESS_README.md", "href": "WITNESS.ipynb"}
    ]
    head["n_violations"] = len(head["violations"])
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=1" in proc.stdout
    # F1 contreexemple : le format `::error::STALE_LINK ...` doit etre emis
    # sur STDERR (le workflow greperait sans 2>&1 sinon). C'est la condition
    # qui a fait rougir le run originel 37109571492 sans etre vue.
    assert "::error::STALE_LINK WITNESS_README.md -> WITNESS.ipynb" in proc.stderr
