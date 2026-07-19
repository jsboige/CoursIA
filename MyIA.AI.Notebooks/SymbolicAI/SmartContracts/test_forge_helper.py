#!/usr/bin/env python3
"""Pytest suite for `SymbolicAI/SmartContracts/forge_helper.py`.

Co-located with the module under `SmartContracts/`. CPU-only, no network,
no real `forge`/Foundry invocation, no WSL. The module is a Foundry CLI
wrapper consumed by the SmartContracts notebooks (SC-12 Foundry Testing,
SC-24 Testnet Deploy) and had 0 dedicated Python test coverage before this PR.

Strategy: the 3 execution branches (native forge on PATH / Windows-via-WSL /
RuntimeError) and the artifact-resolution + cleanup logic are exercised by
monkeypatching `shutil.which`, `platform.system`, `subprocess.run`, and
redirecting the module-level `FOUNDRY_DIR` to a per-test tmp_path so no real
Solidity file is written into the repo. A fake artifact JSON is laid down in
`tmp/out/<name>.sol/<name>.json` to drive the read-back path.
"""
from __future__ import annotations

import importlib.util
import json
import platform
from pathlib import Path
from types import SimpleNamespace

import pytest

# Load the module by path (lives under SmartContracts/, stdlib only at import
# time: json/os/platform/shutil/subprocess/pathlib — no package-relative
# imports, no sys.path manipulation needed).
_MODULE_PATH = Path(__file__).resolve().parent / "forge_helper.py"
_spec = importlib.util.spec_from_file_location("forge_helper", _MODULE_PATH)
fh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fh)


# --------------------------------------------------------------------------
# Fakes + fixtures
# --------------------------------------------------------------------------


class _FakeProc:
    """Stand-in for subprocess.CompletedProcess."""

    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


@pytest.fixture
def fake_foundry(tmp_path, monkeypatch):
    """Redirect FOUNDRY_DIR to a tmp tree and pre-create src/out dirs.

    Returns a small holder so individual tests can lay down artifacts and
    inspect the .sol file written by the module.
    """
    src_dir = tmp_path / "src"
    out_dir = tmp_path / "out"
    src_dir.mkdir(parents=True, exist_ok=True)
    out_dir.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(fh, "FOUNDRY_DIR", tmp_path)

    return SimpleNamespace(root=tmp_path, src_dir=src_dir, out_dir=out_dir)


def _lay_artifact(fake_foundry, contract_name, abi=None, bytecode_obj="0xABC",
                  filename=None):
    """Write a fake forge artifact JSON under out/<file>.sol/<name>.json."""
    abi = abi if abi is not None else [{"type": "constructor", "inputs": []}]
    sol_dir = fake_foundry.out_dir / f"{filename or contract_name}.sol"
    sol_dir.mkdir(parents=True, exist_ok=True)
    (sol_dir / f"{contract_name}.json").write_text(
        json.dumps({"abi": abi, "bytecode": {"object": bytecode_obj}}),
        encoding="utf-8",
    )
    return sol_dir


def _capture_run(monkeypatch, proc, calls):
    """Monkeypatch subprocess.run to record (cmd, cwd) and return `proc`."""

    def _fake_run(cmd, **kwargs):
        calls.append({"cmd": list(cmd), "cwd": kwargs.get("cwd")})
        return proc

    monkeypatch.setattr(fh.subprocess, "run", _fake_run)


# --------------------------------------------------------------------------
# _is_forge_available
# --------------------------------------------------------------------------


def test_is_forge_available_true_when_on_path(monkeypatch):
    monkeypatch.setattr(fh.shutil, "which", lambda cmd: "/usr/local/bin/forge")
    assert fh._is_forge_available() is True


def test_is_forge_available_false_when_absent(monkeypatch):
    monkeypatch.setattr(fh.shutil, "which", lambda cmd: None)
    assert fh._is_forge_available() is False


# --------------------------------------------------------------------------
# _run_forge — branch selection (native / WSL / RuntimeError)
# --------------------------------------------------------------------------


def test_run_forge_native_branch_uses_forge_cmd(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    calls = []
    _capture_run(monkeypatch, _FakeProc(0), calls)
    _lay_artifact(fake_foundry, "Counter")
    fh._run_forge("contract Counter {}", "Counter")
    assert calls[0]["cmd"] == ["forge", "build", "--force", "--silent"]
    assert calls[0]["cwd"] == str(fake_foundry.root)


def test_run_forge_windows_branch_invokes_wsl(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: False)
    monkeypatch.setattr(fh.platform, "system", lambda: "Windows")
    calls = []
    _capture_run(monkeypatch, _FakeProc(0), calls)
    _lay_artifact(fake_foundry, "Counter")
    fh._run_forge("contract Counter {}", "Counter")
    cmd = calls[0]["cmd"]
    assert cmd[0] == "wsl"
    # The bash -c payload must cd into the foundry dir and run forge.
    payload = " ".join(cmd[5:])
    assert "forge build --force --silent" in payload
    assert "cd " in payload


def test_run_forge_non_windows_no_forge_raises_runtime_error(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: False)
    monkeypatch.setattr(fh.platform, "system", lambda: "Linux")
    calls = []
    _capture_run(monkeypatch, _FakeProc(0), calls)
    _lay_artifact(fake_foundry, "Counter")
    with pytest.raises(RuntimeError, match="forge not found"):
        fh._run_forge("contract Counter {}", "Counter")
    # RuntimeError branch never shells out.
    assert calls == []


# --------------------------------------------------------------------------
# _run_forge — returncode != 0 error
# --------------------------------------------------------------------------


def test_run_forge_nonzero_returncode_raises_with_output(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(
        monkeypatch,
        _FakeProc(1, stdout="boom-out", stderr="boom-err"),
        [],
    )
    with pytest.raises(RuntimeError) as excinfo:
        fh._run_forge("contract Counter {}", "Counter")
    msg = str(excinfo.value)
    assert "forge build failed" in msg
    assert "boom-out" in msg
    assert "boom-err" in msg


# --------------------------------------------------------------------------
# _run_forge — artifact resolution
# --------------------------------------------------------------------------


def test_run_forge_reads_canonical_artifact(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(0), [])
    _lay_artifact(fake_foundry, "Counter", abi=["ABI"], bytecode_obj="0xDEAD")
    artifact = fh._run_forge("contract Counter {}", "Counter")
    assert artifact["abi"] == ["ABI"]
    assert artifact["bytecode"]["object"] == "0xDEAD"


def test_run_forge_artifact_glob_fallback(fake_foundry, monkeypatch):
    # Canonical path out/Counter.sol/Counter.json absent, but a sibling .json
    # exists in the out dir -> glob fallback picks the first match.
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(0), [])
    sol_dir = _lay_artifact(fake_foundry, "Counter")
    # Remove canonical, leave only a renamed sibling.
    (sol_dir / "Counter.json").unlink()
    (sol_dir / "SomethingElse.json").write_text(
        json.dumps({"abi": [], "bytecode": {"object": "0xFALLBACK"}}),
        encoding="utf-8",
    )
    artifact = fh._run_forge("contract Counter {}", "Counter")
    assert artifact["bytecode"]["object"] == "0xFALLBACK"


def test_run_forge_empty_out_dir_raises_filenotfound(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(0), [])
    # out/Counter.sol dir exists but has no .json
    (fake_foundry.out_dir / "Counter.sol").mkdir(parents=True)
    with pytest.raises(FileNotFoundError, match="No artifacts"):
        fh._run_forge("contract Counter {}", "Counter")


def test_run_forge_missing_out_dir_raises_filenotfound(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(0), [])
    # No out/Counter.sol dir at all.
    with pytest.raises(FileNotFoundError, match="Build output dir not found"):
        fh._run_forge("contract Counter {}", "Counter")


# --------------------------------------------------------------------------
# _run_forge — cleanup in finally
# --------------------------------------------------------------------------


def test_run_forge_cleans_up_source_on_success(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(0), [])
    _lay_artifact(fake_foundry, "Counter")
    fh._run_forge("contract Counter {}", "Counter")
    # The .sol written into src/ must be removed by the finally block.
    assert not (fake_foundry.src_dir / "Counter.sol").exists()


def test_run_forge_cleans_up_source_even_on_error(fake_foundry, monkeypatch):
    monkeypatch.setattr(fh, "_is_forge_available", lambda: True)
    _capture_run(monkeypatch, _FakeProc(1, stdout="", stderr=""), [])
    with pytest.raises(RuntimeError):
        fh._run_forge("contract Counter {}", "Counter")
    # Source must still be cleaned up despite the failure.
    assert not (fake_foundry.src_dir / "Counter.sol").exists()


# --------------------------------------------------------------------------
# forge_compile
# --------------------------------------------------------------------------


def test_forge_compile_returns_abi_and_bytecode(monkeypatch):
    monkeypatch.setattr(
        fh, "_run_forge",
        lambda src, name: {"abi": ["A"], "bytecode": {"object": "0xBEEF"}},
    )
    abi, bytecode = fh.forge_compile("contract C {}", "C")
    assert abi == ["A"]
    assert bytecode == "0xBEEF"


def test_forge_compile_threads_source_and_name(monkeypatch):
    seen = {}
    monkeypatch.setattr(fh, "_run_forge", lambda src, name: seen.update(
        {"src": src, "name": name}) or {"abi": [], "bytecode": {"object": "0x0"}}
    )
    fh.forge_compile("SRC", "MyContract")
    assert seen == {"src": "SRC", "name": "MyContract"}


# --------------------------------------------------------------------------
# forge_compile_and_deploy
# --------------------------------------------------------------------------


class _FakeConstructor:
    def __init__(self, recorder, args):
        self._recorder = recorder
        self._args = args

    def transact(self, tx_kwargs):
        self._recorder.append({"args": self._args, "tx_kwargs": dict(tx_kwargs)})
        return "0xTXHASH"


class _FakeContractFactory:
    def __init__(self, recorder, abi, bytecode):
        self._recorder = recorder
        self.abi = abi
        self.bytecode = bytecode

    def constructor(self, *args):
        return _FakeConstructor(self._recorder, list(args))


class _FakeW3:
    """Minimal Web3 stand-in recording the deploy flow."""

    def __init__(self, contract_address="0xDEPLOYED"):
        self.recorder = []
        self._contract_address = contract_address
        self.last_factory = None

        class _Eth:
            def __init__(self, outer):
                self._outer = outer

            def contract(self, abi=None, bytecode=None, address=None):
                if bytecode is not None:
                    # constructor call path
                    self._outer.last_factory = _FakeContractFactory(
                        self._outer.recorder, abi, bytecode
                    )
                    return self._outer.last_factory
                # instance lookup path (address given)
                return {"address": address, "abi": abi}

            def wait_for_transaction_receipt(self, tx_hash):
                class _Receipt:
                    contractAddress = self._outer._contract_address
                return _Receipt()

        self.eth = _Eth(self)


def test_forge_compile_and_deploy_returns_instance_and_receipt(monkeypatch):
    monkeypatch.setattr(fh, "forge_compile",
                       lambda src, name: (["ABI"], "0xCODE"))
    w3 = _FakeW3("0xCAFE")
    instance, receipt = fh.forge_compile_and_deploy(
        w3, "contract C {}", "C", "0xDEPLOYER", 42, "arg"
    )
    assert receipt.contractAddress == "0xCAFE"
    # The instance built from the receipt address carries the abi.
    assert instance["address"] == "0xCAFE"
    assert instance["abi"] == ["ABI"]
    # Constructor was invoked with the positional args + from=deployer.
    assert w3.recorder[0]["args"] == [42, "arg"]
    assert w3.recorder[0]["tx_kwargs"] == {"from": "0xDEPLOYER"}


def test_forge_compile_and_deploy_no_constructor_args(monkeypatch):
    monkeypatch.setattr(fh, "forge_compile",
                       lambda src, name: ([], "0xCODE"))
    w3 = _FakeW3()
    _, receipt = fh.forge_compile_and_deploy(
        w3, "contract C {}", "C", "0xDEPLOYER"
    )
    assert receipt.contractAddress == "0xDEPLOYED"
    # No *constructor_args -> empty arg list.
    assert w3.recorder[0]["args"] == []
