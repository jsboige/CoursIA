#!/usr/bin/env python3
"""Tests pour download_qc_data.py — QuantConnect historical-data downloader.

Covers the importable pure helpers of the QC data provisioner (the lean-cli /
object-store downloader that feeds QuantConnect notebook re-execution with
local LEAN data files). Distinct from `provision_vix_csv.py` (VIX term-structure)
and `download_yfinance.py` (yahoo-finance), tested in sibling files.

Scope (hermetic, 0 network / 0 real `lean` invocation):
  - _check_lean_cli : exit 1 when lean CLI missing/unreachable, no-op when present
  - download_object_store : output-path construction + parent-dir creation + return
  - download_lean_cli : CLI command construction, exit-on-nonzero, file globbing
  - main : mode routing (lean-cli default, object-store), --key required guard,
    filename derivation (--output fallback from key), default arguments

Every subprocess call is monkeypatched so no `lean` binary and no network are
required. tmp_path isolates all filesystem writes.

Run: ``python -m pytest scripts/datasets/tests/test_download_qc_data.py -q``
"""
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DATASETS_DIR = HERE.parent  # scripts/datasets/ (where download_qc_data.py lives)
sys.path.insert(0, str(DATASETS_DIR))

import download_qc_data as dqd  # noqa: E402


# ---------------------------------------------------------------------------
# _check_lean_cli
# ---------------------------------------------------------------------------


class _FakeResult:
    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def test_check_lean_cli_present_no_exit(monkeypatch):
    # When `lean --version` returns rc=0, _check_lean_cli returns normally.
    monkeypatch.setattr(
        dqd.subprocess, "run",
        lambda *a, **k: _FakeResult(returncode=0, stdout="lean 1.0.0"))
    # Should NOT raise SystemExit.
    dqd._check_lean_cli()


def test_check_lean_cli_nonzero_exits_1(monkeypatch, capsys):
    monkeypatch.setattr(
        dqd.subprocess, "run",
        lambda *a, **k: _FakeResult(returncode=1, stderr="boom"))
    with pytest.raises(SystemExit) as exc:
        dqd._check_lean_cli()
    assert exc.value.code == 1
    err = capsys.readouterr().err
    assert "lean CLI not found" in err


def test_check_lean_cli_not_found_exits_1(monkeypatch, capsys):
    # FileNotFoundError (lean binary absent from PATH) -> exit 1, not a crash.
    def _boom(*a, **k):
        raise FileNotFoundError("lean")
    monkeypatch.setattr(dqd.subprocess, "run", _boom)
    with pytest.raises(SystemExit) as exc:
        dqd._check_lean_cli()
    assert exc.value.code == 1
    assert "pip install lean" in capsys.readouterr().err


def test_check_lean_cli_timeout_exits_1(monkeypatch):
    import subprocess as sp

    def _slow(*a, **k):
        raise sp.TimeoutExpired(cmd="lean", timeout=10)
    monkeypatch.setattr(dqd.subprocess, "run", _slow)
    with pytest.raises(SystemExit) as exc:
        dqd._check_lean_cli()
    assert exc.value.code == 1


# ---------------------------------------------------------------------------
# download_object_store
# ---------------------------------------------------------------------------


def test_object_store_builds_path_and_makes_dir(tmp_path, capsys):
    out = dqd.download_object_store(
        key="my-datasets/spy_daily.csv",
        output="spy_daily.csv",
        output_dir=tmp_path / "qc",
    )
    assert out == tmp_path / "qc" / "spy_daily.csv"
    assert out.parent.exists() and out.parent.is_dir()
    msg = capsys.readouterr().out
    assert "my-datasets/spy_daily.csv" in msg
    assert "spy_daily.csv" in msg


def test_object_store_preserves_nested_filename(tmp_path):
    # An explicit --output (even with slashes) is used verbatim as the filename.
    out = dqd.download_object_store(
        key="k", output="sub/nested.csv", output_dir=tmp_path)
    assert out.name == "nested.csv"


# ---------------------------------------------------------------------------
# download_lean_cli
# ---------------------------------------------------------------------------


def test_lean_cli_builds_expected_command(monkeypatch, tmp_path):
    """The lean-cli subprocess is invoked with the canonical argument vector."""
    captured = {}

    def _fake_run(cmd, **kwargs):
        captured["cmd"] = cmd
        captured["kwargs"] = kwargs
        return _FakeResult(returncode=0, stdout="ok")

    monkeypatch.setattr(dqd.subprocess, "run", _fake_run)
    # _check_lean_cli must be neutralized (it also calls subprocess.run).
    monkeypatch.setattr(dqd, "_check_lean_cli", lambda: None)

    files = dqd.download_lean_cli(
        symbol="SPY", security_type="equity", resolution="daily",
        start="2020-01-01", end="2023-12-31", output_dir=tmp_path / "out")

    cmd = captured["cmd"]
    assert cmd[:3] == ["lean", "data", "download"]
    assert "--security-type" in cmd and "equity" in cmd
    assert "--resolution" in cmd and "daily" in cmd
    assert "--ticker" in cmd and "SPY" in cmd
    assert "--start" in cmd and "2020-01-01" in cmd
    assert "--end" in cmd and "2023-12-31" in cmd
    assert "--destination" in cmd
    # output_dir is created before the call.
    assert (tmp_path / "out").is_dir()
    # returns the glob of files (empty dir -> empty list).
    assert files == []


def test_lean_cli_nonzero_exits_1(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(dqd.subprocess, "run",
                       lambda *a, **k: _FakeResult(returncode=1, stderr="denied"))
    monkeypatch.setattr(dqd, "_check_lean_cli", lambda: None)
    with pytest.raises(SystemExit) as exc:
        dqd.download_lean_cli("SPY", "equity", "daily", "2020", "2021", tmp_path)
    assert exc.value.code == 1
    assert "denied" in capsys.readouterr().err


def test_lean_cli_returns_downloaded_files(monkeypatch, tmp_path):
    # Pre-create files in the output dir to verify they are globbed and returned.
    out_dir = tmp_path / "out"
    out_dir.mkdir()
    (out_dir / "SPY.csv").write_text("data", encoding="utf-8")
    (out_dir / "sub").mkdir()
    (out_dir / "sub" / "x.csv").write_text("data", encoding="utf-8")

    monkeypatch.setattr(dqd.subprocess, "run",
                       lambda *a, **k: _FakeResult(returncode=0, stdout="ok"))
    monkeypatch.setattr(dqd, "_check_lean_cli", lambda: None)

    files = dqd.download_lean_cli("SPY", "equity", "daily", "2020", "2021", out_dir)
    names = sorted(p.name for p in files)
    assert names == ["SPY.csv", "x.csv"]


# ---------------------------------------------------------------------------
# main (CLI wiring)
# ---------------------------------------------------------------------------


def test_main_defaults_route_to_lean_cli(monkeypatch, tmp_path):
    """Default mode (lean-cli) + default args invoke download_lean_cli.

    main() parses sys.argv directly (no positional arg), so we patch sys.argv.
    """
    calls = {}

    def _fake_download(symbol, security_type, resolution, start, end, output_dir):
        calls["args"] = (symbol, security_type, resolution, start, end, output_dir)
        return []

    monkeypatch.setattr(dqd, "download_lean_cli", _fake_download)
    monkeypatch.setattr(dqd.sys, "argv",
                       ["download_qc_data.py", "--output-dir", str(tmp_path / "qc")])
    rc = dqd.main()
    assert rc is None  # main returns None on the happy path
    sym, sec, res, start, end, _ = calls["args"]
    assert sym == "SPY"          # default --symbol
    assert sec == "equity"       # default --security-type
    assert res == "daily"        # default --resolution
    assert start == "2020-01-01"  # default --start


def test_main_object_store_without_key_errors(monkeypatch, tmp_path):
    # object-store mode requires --key; argparse.error -> SystemExit(2).
    monkeypatch.setattr(dqd, "download_object_store", lambda *a, **k: Path("x"))
    monkeypatch.setattr(dqd.sys, "argv",
                       ["download_qc_data.py", "--mode", "object-store",
                        "--output-dir", str(tmp_path)])
    with pytest.raises(SystemExit) as exc:
        dqd.main()
    assert exc.value.code == 2


def test_main_object_store_with_explicit_output(monkeypatch, tmp_path):
    calls = {}

    def _fake_os(key, output, output_dir):
        calls["args"] = (key, output, output_dir)
        return Path("x")

    monkeypatch.setattr(dqd, "download_object_store", _fake_os)
    monkeypatch.setattr(dqd.sys, "argv",
                       ["download_qc_data.py", "--mode", "object-store",
                        "--key", "ds/spy.csv", "--output", "renamed.csv",
                        "--output-dir", str(tmp_path)])
    dqd.main()
    key, output, _ = calls["args"]
    assert key == "ds/spy.csv"
    assert output == "renamed.csv"


def test_main_object_store_output_derived_from_key(monkeypatch, tmp_path):
    # No --output: filename = last path segment of --key.
    calls = {}

    def _fake_os(key, output, output_dir):
        calls["output"] = output
        return Path("x")

    monkeypatch.setattr(dqd, "download_object_store", _fake_os)
    monkeypatch.setattr(dqd.sys, "argv",
                       ["download_qc_data.py", "--mode", "object-store",
                        "--key", "datasets/equity/spy_daily.csv",
                        "--output-dir", str(tmp_path)])
    dqd.main()
    assert calls["output"] == "spy_daily.csv"


def test_main_passes_custom_symbol_and_resolution(monkeypatch, tmp_path):
    calls = {}

    def _fake_download(symbol, security_type, resolution, start, end, output_dir):
        calls["args"] = (symbol, security_type, resolution, start, end, output_dir)
        return []

    monkeypatch.setattr(dqd, "download_lean_cli", _fake_download)
    monkeypatch.setattr(dqd.sys, "argv",
                       ["download_qc_data.py", "--symbol", "BTCUSD",
                        "--security-type", "crypto", "--resolution", "minute",
                        "--start", "2023-01-01", "--output-dir", str(tmp_path)])
    dqd.main()
    sym, sec, res, start, _, _ = calls["args"]
    assert (sym, sec, res, start) == ("BTCUSD", "crypto", "minute", "2023-01-01")
