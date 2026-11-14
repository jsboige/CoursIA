"""Tests de l'organe de deduplication / exposition licence (grain #16457 Axe 2).

Joue hors-ligne sur le manifeste et le fixture engages. Le test de derive ajoute un
chemin fictif au manifeste : l'organe doit le drapper (exit 1), pas l'ignorer.
"""

from __future__ import annotations

import importlib.util
import json
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ORGAN = REPO_ROOT / "scripts" / "research" / "argumentation_capacity_dedup.py"
MANIFEST = REPO_ROOT / "docs" / "reference" / "argumentation-capacities.json"
FIXTURE = REPO_ROOT / "scripts" / "tests" / "fixtures" / "argumentation_student_tree.json"


def _organ():
    spec = importlib.util.spec_from_file_location("argumentation_capacity_dedup", ORGAN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _tree() -> set:
    return _organ().load_tree(FIXTURE)


def _manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_check_passes_on_committed_manifest():
    mod = _organ()
    assert mod.cmd_check(_manifest(), _tree()) == 0


def test_check_flags_invented_path_as_drift():
    mod = _organ()
    man = _manifest()
    man["capabilities"][0]["platform"].append("this/path/does_not_exist.py")
    assert mod.cmd_check(man, _tree()) == 1


def test_dedup_flags_vendorised_duplicates_and_binaries():
    mod = _organ()
    with tempfile.TemporaryDirectory() as d:
        out = Path(d) / "rapport.md"
        assert mod.cmd_dedup(_manifest(), _tree(), out) == 0
        rep = json.loads(out.with_suffix(".json").read_text(encoding="utf-8"))
        md = out.read_text(encoding="utf-8")
    assert len(rep["vendorisees"]) >= 5
    assert "conflict_resolution.py" in rep["modules_dupliques"]
    assert len(rep["modules_dupliques"]["conflict_resolution.py"]) == 3
    tot = sum(v["count"] for v in rep["exposition_licence"].values())
    assert tot == 16
    assert sum(v["with_license"] for v in rep["exposition_licence"].values()) == 0
    assert "vendoris" in md.lower()


def test_no_binary_has_adjacent_license_file():
    mod = _organ()
    tree = _tree()
    for b in _manifest()["vendored_binaries"]:
        assert mod.license_file_present(b["path"], tree) is False, b["path"]
