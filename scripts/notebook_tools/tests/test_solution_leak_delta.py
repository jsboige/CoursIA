"""Tests for scripts/notebook_tools/solution_leak_delta.py — HIGH delta guard.

Mirrors the contract of pip_leak_delta.py: exit 0 when HEAD introduces no new
HIGH solution leaks vs BASE, exit 1 on a positive HIGH delta, exit 2 on IO/JSON
error. Findings are matched on (normalised path, cell_index) so editing the prose
of an already-leaking cell is not a false regression.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import solution_leak_delta as delta


def _finding(path, severity, cell_index):
    return {"path": path, "severity": severity, "cell_index": cell_index, "message": "x"}


def _write(path: Path, findings):
    path.write_text(json.dumps(findings), encoding="utf-8")
    return path


def test_count_high_ignores_medium_and_low():
    data = [
        _finding("a.ipynb", "HIGH", 3),
        _finding("a.ipynb", "MEDIUM", 4),
        _finding("b.ipynb", "LOW", 1),
        _finding("c.ipynb", "HIGH", 0),
    ]
    assert delta.count_high(data) == 2


def test_high_keys_normalises_backslashes():
    data = [_finding("dir\\nb.ipynb", "HIGH", 7)]
    keys = list(delta.high_keys(data))
    assert keys == [("dir/nb.ipynb", 7)]


def test_no_delta_exits_zero(tmp_path, capsys):
    findings = [_finding("a.ipynb", "HIGH", 1), _finding("a.ipynb", "HIGH", 2)]
    base = _write(tmp_path / "base.json", findings)
    head = _write(tmp_path / "head.json", findings)
    rc = delta.main([str(base), str(head)])
    assert rc == 0
    assert "delta=+0" in capsys.readouterr().out


def test_positive_delta_exits_one(tmp_path, capsys):
    base = _write(tmp_path / "base.json", [_finding("a.ipynb", "HIGH", 1)])
    head = _write(
        tmp_path / "head.json",
        [_finding("a.ipynb", "HIGH", 1), _finding("b.ipynb", "HIGH", 5)],
    )
    rc = delta.main([str(base), str(head)])
    assert rc == 1
    err = capsys.readouterr().err
    assert "delta=+1" in err or "+1" in err
    assert "b.ipynb" in err  # the worsened notebook is reported


def test_decreasing_delta_exits_zero(tmp_path):
    # HEAD has fewer HIGH than BASE (cleanup) — not a regression.
    base = _write(
        tmp_path / "base.json", [_finding("a.ipynb", "HIGH", 1), _finding("b.ipynb", "HIGH", 2)]
    )
    head = _write(tmp_path / "head.json", [_finding("a.ipynb", "HIGH", 1)])
    assert delta.main([str(base), str(head)]) == 0


def test_missing_file_exits_two(tmp_path):
    rc = delta.main([str(tmp_path / "nope.json"), str(tmp_path / "nope2.json")])
    assert rc == 2


def test_invalid_json_exits_two(tmp_path):
    bad = tmp_path / "bad.json"
    bad.write_text("not json", encoding="utf-8")
    ok = _write(tmp_path / "ok.json", [])
    assert delta.main([str(bad), str(ok)]) == 2
