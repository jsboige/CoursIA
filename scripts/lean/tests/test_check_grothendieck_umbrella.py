#!/usr/bin/env python3
"""Tests for check_grothendieck_umbrella.py (#16154 FR-only umbrella guard).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_grothendieck_umbrella.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Proves the drift measure *detects* each axis -- missing FR, imported `_en`,
phantom import -- on a synthetic mini-lake, so the always-on organ is a real
detector and not merely green today (#16048 lesson: FR drifted to 72/72 only
after #16068; nothing held it).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "ci"))

from check_grothendieck_umbrella import drift  # noqa: E402


def _mk(tmp_path: Path, imports: str, mods: dict[str, str]) -> tuple[Path, Path]:
    mods_dir = tmp_path / "Grothendieck"
    umbrella = tmp_path / "Grothendieck.lean"
    umbrella.write_text(imports, encoding="utf-8")
    for rel, body in mods.items():
        f = mods_dir / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(body, encoding="utf-8")
    return mods_dir, umbrella


def test_clean(tmp_path):
    mods_dir, umbrella = _mk(
        tmp_path,
        "import Grothendieck.Foo\nimport Grothendieck.SheafCohomology.Basic\n",
        {"Foo.lean": "", "Foo_en.lean": "", "SheafCohomology/Basic.lean": ""},
    )
    assert drift(mods_dir, umbrella) == {
        "missing_fr": [],
        "en_imported": [],
        "phantom": [],
    }


def test_missing_fr_detected(tmp_path):
    mods_dir, umbrella = _mk(
        tmp_path, "import Grothendieck.Foo\n", {"Foo.lean": "", "Bar.lean": ""}
    )
    assert drift(mods_dir, umbrella)["missing_fr"] == ["Grothendieck.Bar"]


def test_en_imported_detected(tmp_path):
    mods_dir, umbrella = _mk(
        tmp_path,
        "import Grothendieck.Foo\nimport Grothendieck.Foo_en\n",
        {"Foo.lean": "", "Foo_en.lean": ""},
    )
    assert drift(mods_dir, umbrella)["en_imported"] == ["Grothendieck.Foo_en"]


def test_phantom_import_detected(tmp_path):
    mods_dir, umbrella = _mk(
        tmp_path, "import Grothendieck.Ghost\n", {"Foo.lean": ""}
    )
    assert drift(mods_dir, umbrella)["phantom"] == ["Grothendieck.Ghost"]


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
