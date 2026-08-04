#!/usr/bin/env python3
"""Tests pour download_kaggle.py — Kaggle CLI dataset downloader.

Covers the importable pure helpers of the Kaggle dataset downloader (a sibling
of ``download_qc_data.py``, same subprocess-CLI-wrapper shape): the kaggle-CLI
presence guard, the search/download command builders, and the ``main`` CLI
wiring (mutually-exclusive ``--dataset`` / ``--list`` group, ``--no-unzip``).

Scope (hermetic, 0 network / 0 kaggle CLI): ``subprocess.run`` is monkeypatched
to a fake returning canned (returncode, stdout, stderr), so no real ``kaggle``
binary is invoked. ``main`` parses ``sys.argv`` directly (no positional), so it
is driven via ``monkeypatch.setattr(dk.sys, "argv", [...])``.

Run: ``python -m pytest scripts/datasets/tests/test_download_kaggle.py -q``
"""
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DATASETS_DIR = HERE.parent  # scripts/datasets/ (where download_kaggle.py lives)
sys.path.insert(0, str(DATASETS_DIR))

import download_kaggle as dk  # noqa: E402


class _FakeResult:
    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


# ---------------------------------------------------------------------------
# DEFAULT_OUTPUT sanity
# ---------------------------------------------------------------------------

def test_default_output_points_to_kaggle_datasets():
    # DEFAULT_OUTPUT = repo / MyIA.AI.Notebooks / QuantConnect / datasets / kaggle
    assert "QuantConnect" in dk.DEFAULT_OUTPUT.parts
    assert dk.DEFAULT_OUTPUT.name == "kaggle"
    assert dk.DEFAULT_OUTPUT.parent.name == "datasets"


# ---------------------------------------------------------------------------
# _check_kaggle_cli
# ---------------------------------------------------------------------------

def test_check_cli_ok_does_not_exit(monkeypatch):
    monkeypatch.setattr(dk.subprocess, "run", lambda *a, **k: _FakeResult(0, "1.6\n", ""))
    # Should return None without raising/exiting.
    assert dk._check_kaggle_cli() is None


def test_check_cli_nonzero_rc_exits(monkeypatch):
    monkeypatch.setattr(dk.subprocess, "run", lambda *a, **k: _FakeResult(1, "", "boom"))
    with pytest.raises(SystemExit) as ei:
        dk._check_kaggle_cli()
    assert ei.value.code == 1


def test_check_cli_filenotfound_exits(monkeypatch):
    def _boom(*a, **k):
        raise FileNotFoundError
    monkeypatch.setattr(dk.subprocess, "run", _boom)
    with pytest.raises(SystemExit) as ei:
        dk._check_kaggle_cli()
    assert ei.value.code == 1


def test_check_cli_timeout_exits(monkeypatch):
    import subprocess as sp

    def _slow(*a, **k):
        raise sp.TimeoutExpired(cmd=a, timeout=10)
    monkeypatch.setattr(dk.subprocess, "run", _slow)
    with pytest.raises(SystemExit) as ei:
        dk._check_kaggle_cli()
    assert ei.value.code == 1


# ---------------------------------------------------------------------------
# search_datasets
# ---------------------------------------------------------------------------

def test_search_builds_list_cmd_and_prints(monkeypatch, capsys):
    captured = {}

    def _fake(cmd, **k):
        captured["cmd"] = cmd
        return _FakeResult(0, "ref,title,size\nds1,Foo,1MB\n", "")

    monkeypatch.setattr(dk.subprocess, "run", _fake)
    dk.search_datasets("crypto historical", max_results=5)
    cmd = captured["cmd"]
    assert cmd[:3] == ["kaggle", "datasets", "list"]
    assert "-s" in cmd and "crypto historical" in cmd
    assert "--max-size" in cmd and "5" in cmd
    assert "--csv" in cmd
    out = capsys.readouterr().out
    assert "ref,title,size" in out  # stdout printed


def test_search_passes_default_max_results(monkeypatch):
    captured = {}

    def _fake(cmd, **k):
        captured["cmd"] = cmd
        return _FakeResult(0, "h\n", "")

    monkeypatch.setattr(dk.subprocess, "run", _fake)
    dk.search_datasets("anything")  # default max_results
    assert "10" in captured["cmd"]


# ---------------------------------------------------------------------------
# download
# ---------------------------------------------------------------------------

def test_download_builds_cmd_with_unzip(monkeypatch, tmp_path):
    captured = {}

    def _fake(cmd, **k):
        captured["cmd"] = cmd
        return _FakeResult(0, "", "")

    monkeypatch.setattr(dk.subprocess, "run", _fake)
    target = dk.download("user/my-dataset", tmp_path, unzip=True)
    cmd = captured["cmd"]
    assert cmd[:3] == ["kaggle", "datasets", "download"]
    assert "-d" in cmd and "user/my-dataset" in cmd
    assert "-p" in cmd and str(target) in cmd
    assert "--unzip" in cmd  # default unzip=True appends --unzip


def test_download_builds_cmd_without_unzip(monkeypatch, tmp_path):
    captured = {}

    def _fake(cmd, **k):
        captured["cmd"] = cmd
        return _FakeResult(0, "", "")

    monkeypatch.setattr(dk.subprocess, "run", _fake)
    dk.download("user/my-dataset", tmp_path, unzip=False)
    assert "--unzip" not in captured["cmd"]


def test_download_target_path_replaces_slash(monkeypatch, tmp_path):
    monkeypatch.setattr(dk.subprocess, "run", lambda *a, **k: _FakeResult(0, "", ""))
    target = dk.download("user/my-dataset", tmp_path, unzip=True)
    # dataset slug "user/my-dataset" -> dir "user__my-dataset"
    assert target == tmp_path / "user__my-dataset"
    assert target.is_dir()  # mkdir(parents=True, exist_ok=True) ran


def test_download_nonzero_rc_exits(monkeypatch, tmp_path):
    # Discriminate by command: the version-check (["kaggle","--version"]) must
    # pass (rc=0) so we reach the download command, which then fails (rc=2) and
    # triggers exit(1). A blanket rc!=0 fake would exit at the check, not here.
    def _fake(cmd, **k):
        if "--version" in cmd:
            return _FakeResult(0, "1.6\n", "")
        return _FakeResult(2, "", "forbidden")
    monkeypatch.setattr(dk.subprocess, "run", _fake)
    with pytest.raises(SystemExit) as ei:
        dk.download("user/my-dataset", tmp_path, unzip=True)
    assert ei.value.code == 1


def test_download_returns_target_and_lists_files(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(dk.subprocess, "run", lambda *a, **k: _FakeResult(0, "", ""))
    target = dk.download("u/d", tmp_path, unzip=True)
    # seed a file so the listing branch has something to stat
    (target / "data.csv").write_bytes(b"x" * 2048)
    # re-run to capture the listing print (target already exists)
    dk.download("u/d", tmp_path, unzip=True)
    out = capsys.readouterr().out
    assert "data.csv" in out
    assert "MB" in out  # size formatting


# ---------------------------------------------------------------------------
# main (CLI wiring via sys.argv patch)
# ---------------------------------------------------------------------------

def test_main_list_routes_to_search(monkeypatch):
    called = {}

    def _fake_search(query, max_results=10):
        called["query"] = query
        called["max"] = max_results

    monkeypatch.setattr(dk, "search_datasets", _fake_search)
    monkeypatch.setattr(dk.sys, "argv",
                        ["download_kaggle.py", "--list", "--search", "etf historical"])
    dk.main()
    assert called["query"] == "etf historical"


def test_main_dataset_routes_to_download(monkeypatch, tmp_path):
    called = {}

    def _fake_download(dataset, output_dir, unzip=True):
        called["dataset"] = dataset
        called["output_dir"] = output_dir
        called["unzip"] = unzip
        return output_dir

    monkeypatch.setattr(dk, "download", _fake_download)
    monkeypatch.setattr(dk.sys, "argv",
                        ["download_kaggle.py", "--dataset", "user/ds",
                         "--output-dir", str(tmp_path)])
    dk.main()
    assert called["dataset"] == "user/ds"
    assert called["output_dir"] == tmp_path
    assert called["unzip"] is True  # default


def test_main_no_unzip_flag_propagates(monkeypatch, tmp_path):
    called = {}

    def _fake_download(dataset, output_dir, unzip=True):
        called["unzip"] = unzip
        return output_dir

    monkeypatch.setattr(dk, "download", _fake_download)
    monkeypatch.setattr(dk.sys, "argv",
                        ["download_kaggle.py", "--dataset", "user/ds",
                         "--output-dir", str(tmp_path), "--no-unzip"])
    dk.main()
    assert called["unzip"] is False


def test_main_neither_group_is_required_exits_2(monkeypatch):
    # The mutually-exclusive group is required -> argparse error -> SystemExit 2.
    monkeypatch.setattr(dk.sys, "argv", ["download_kaggle.py"])
    with pytest.raises(SystemExit) as ei:
        dk.main()
    assert ei.value.code == 2


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
