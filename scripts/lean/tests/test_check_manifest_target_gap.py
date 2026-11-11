#!/usr/bin/env python3
"""Tests for check_manifest_target_gap.py (census des modules hors gate, #8782).

Dual-mode : executable directement (``python scripts/lean/tests/test_check_manifest_target_gap.py``)
ou collecte par pytest (scripts-tests.yml, tout changement ``scripts/**``).

Verrouille le contrat du recensement :

  - ``exit 0`` inconditionnel (advisory, jamais bloquant) ;
  - les trois etats du manifeste restent distincts : liste bornee (ecart
    mesure), ``"*"`` (liste derivee a l'execution, couverture totale),
    liste vide (aucun gate) ;
  - l'ecart se mesure sur les modules **compiles** (globs du lakefile), avec
    la semantique reelle de Lake : `X.*` inclut la racine `X.lean`, seul
    `X.+` (ou `.submodules `X``) l'exclut ;
  - le compte de sorry vient de l'instrument canonique (``scan_file``) ;
  - le prescreen des classes ``forbidden`` signale, il ne dispense pas.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

_SCRIPT = Path(__file__).resolve().parent.parent / "check_manifest_target_gap.py"
sys.path.insert(0, str(_SCRIPT.parent))


def _load():
    spec = importlib.util.spec_from_file_location("check_manifest_target_gap", _SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


m = _load()


def _lake(root: Path, name: str, globs: str, files: dict[str, str]) -> None:
    lake = root / "lakes" / name
    lake.mkdir(parents=True, exist_ok=True)
    (lake / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n\n"
        f"@[default_target]\nlean_lib Demo where\n  globs := #{globs}\n",
        encoding="utf-8",
    )
    for rel, body in files.items():
        path = lake / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")


def _manifest(root: Path, entries: list[dict]) -> None:
    path = root / "scripts" / "lean" / "ci_lakes.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"lakes": entries}, ensure_ascii=False), encoding="utf-8")


def _entry(lake: str, targets: str | None) -> dict:
    entry = {
        "lake": lake,
        "project-path": f"lakes/{lake}",
        "sorry-baseline": "0",
        "sorry-filter-mode": "real",
    }
    if targets is not None:
        entry["axiom-target-modules"] = targets
    return entry


@pytest.fixture()
def fake_repo(tmp_path, monkeypatch):
    monkeypatch.setattr(m, "_REPO_ROOT", tmp_path)
    return tmp_path


def test_bounded_list_reports_compiled_module_outside(fake_repo):
    _lake(fake_repo, "demo", "[`Demo.*]",
          {"Demo/Basic.lean": "theorem t : True := trivial\n",
           "Demo/Extra.lean": "theorem u : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    report = m.measure()
    row = report["lakes"][0]
    assert row["state"] == "bounded"
    assert [item["module"] for item in row["missing"]] == ["Demo.Extra"]
    assert row["missing"][0]["code_sorry"] == 0


def test_star_glob_includes_the_root_file(fake_repo):
    # `Demo.*` est un `Glob.andSubmodules` : la racine `Demo.lean` **est**
    # compilee par Lake (« including itself »). Elle n'est donc pas
    # « non compilee » : elle sort de la liste de cibles, et c'est l'ecart
    # que le recensement doit signaler.
    _lake(fake_repo, "demo", "[`Demo.*]",
          {"Demo.lean": "import Demo.Basic\n",
           "Demo/Basic.lean": "theorem t : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    row = m.measure()["lakes"][0]
    assert row["compiled"] == 2
    assert "Demo" not in row["not_compiled"]
    assert [item["module"] for item in row["missing"]] == ["Demo"]


def test_plus_glob_excludes_the_root_file(fake_repo):
    # `Demo.+` est un `Glob.submodules` : les modules sous `Demo/`, **sans**
    # `Demo.lean`. La racine n'est alors pas compilee et ne doit pas etre
    # proposee au gate.
    _lake(fake_repo, "demo", "[`Demo.+]",
          {"Demo.lean": "import Demo.Basic\n",
           "Demo/Basic.lean": "theorem t : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    row = m.measure()["lakes"][0]
    assert row["compiled"] == 1
    assert row["missing"] == []
    assert "Demo" in row["not_compiled"]


def test_submodules_glob_covers_the_directory(fake_repo):
    _lake(fake_repo, "demo", "[.submodules `Demo]",
          {"Demo/Basic.lean": "theorem t : True := trivial\n",
           "Demo/Deep/More.lean": "theorem v : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    row = m.measure()["lakes"][0]
    assert row["compiled"] == 2
    assert [item["module"] for item in row["missing"]] == ["Demo.Deep.More"]


def test_star_means_full_coverage(fake_repo):
    _lake(fake_repo, "demo", "[`Demo.*]", {"Demo/Basic.lean": "theorem t : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "*")])

    row = m.measure()["lakes"][0]
    assert row["state"] == "full"
    assert row["missing"] == []


def test_empty_list_is_no_gate_not_a_gap(fake_repo):
    _lake(fake_repo, "demo", "[`Demo.*]", {"Demo/Basic.lean": "theorem t : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", None)])

    row = m.measure()["lakes"][0]
    assert row["state"] == "no_gate"
    assert row["missing"] == []


def test_code_sorry_is_counted_per_module(fake_repo):
    _lake(fake_repo, "demo", "[`Demo.*]",
          {"Demo/Basic.lean": "theorem t : True := sorry\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Other")])

    row = m.measure()["lakes"][0]
    assert row["missing"][0]["module"] == "Demo.Basic"
    assert row["missing"][0]["code_sorry"] == 1


def test_forbidden_prescreen_flags_native_decide(fake_repo):
    _lake(fake_repo, "demo", "[`Demo.*]",
          {"Demo/Basic.lean": "theorem t : Nat := by native_decide\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Other")])

    row = m.measure()["lakes"][0]
    assert row["missing"][0]["forbidden"]["native_decide"] == 1


def test_main_exits_zero_even_with_findings(fake_repo, capsys):
    _lake(fake_repo, "demo", "[`Demo.*]", {"Demo/Extra.lean": "theorem u : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    assert m.main(["--lake", "demo"]) == 0
    out = capsys.readouterr().out
    assert "Demo.Extra" in out


def test_json_output_is_machine_readable(fake_repo, capsys):
    _lake(fake_repo, "demo", "[`Demo.*]", {"Demo/Extra.lean": "theorem u : True := trivial\n"})
    _manifest(fake_repo, [_entry("demo", "Demo.Basic")])

    assert m.main(["--lake", "demo", "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["lakes"][0]["missing"][0]["module"] == "Demo.Extra"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
