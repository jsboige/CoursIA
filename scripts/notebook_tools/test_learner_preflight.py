"""Tests for learner_preflight.py.

Couvre chaque classe de manque via des fixtures (mocks), sans dépendre
de l'état réel de la machine. Le but : qu'un CI puisse exécuter ces
tests sur n'importe quelle machine (clone vierge inclus).

Note: ces tests utilisent `unittest.mock` pour stub les appels externes
(`shutil.which`, `subprocess.run`). Ils ne lancent ni Jupyter, ni
dotnet, ni Docker, ni WSL, ni GPU.
"""
from __future__ import annotations

import json
import subprocess
import sys
from unittest import mock

import pytest

from learner_preflight import (
    Finding,
    Report,
    run_preflight,
    _python_version_ok,
    _jupyter_present,
    _kernels_present,
    _dotnet_sdk_present,
    _lean_present,
    _gpu_present,
    _docker_present,
    _api_keys_present,
)


# ---------- Cas "tout va bien" ---------------------------------------------


def test_python_version_ok():
    f = _python_version_ok()
    assert f.ok, f.detail
    assert f.name == "python_version"


# ---------- Cas de manque typiques -----------------------------------------


def test_jupyter_missing():
    with mock.patch("shutil.which", return_value=None):
        f = _jupyter_present()
    assert not f.ok
    assert "absent" in f.detail
    assert f.repair


def test_kernels_all_present():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="\n".join([
            "Available kernels:",
            "  python3    /usr/share/jupyter/kernels/python3",
            "  .net-csharp   /home/x/.local/share/jupyter/kernels/.net-csharp",
        ]),
        stderr="",
    )
    with mock.patch("subprocess.run", return_value=fake_out):
        findings = _kernels_present(("python3", ".net-csharp"))
    assert len(findings) == 1
    assert findings[0].ok


def test_kernels_missing():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="\n".join([
            "Available kernels:",
            "  python3    /usr/share/jupyter/kernels/python3",
        ]),
        stderr="",
    )
    with mock.patch("subprocess.run", return_value=fake_out):
        findings = _kernels_present(("python3", ".net-csharp"))
    assert not findings[0].ok
    assert ".net-csharp" in findings[0].detail


def test_kernels_jupiter_missing():
    err = FileNotFoundError("jupyter not found")
    with mock.patch("subprocess.run", side_effect=err):
        findings = _kernels_present(("python3",))
    assert not findings[0].ok
    assert "jupyter kernelspec" in findings[0].detail


def test_dotnet_sdk_missing():
    with mock.patch("shutil.which", return_value=None):
        f = _dotnet_sdk_present()
    assert not f.ok
    assert "dotnet" in f.detail


def test_dotnet_sdk_present():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="9.0.0\n", stderr="",
    )
    with mock.patch("shutil.which", return_value="/usr/bin/dotnet"), \
         mock.patch("subprocess.run", return_value=fake_out):
        f = _dotnet_sdk_present()
    assert f.ok
    assert "9.0.0" in f.detail


def test_lean_present_no_wsl():
    with mock.patch("shutil.which", return_value=None):
        f = _lean_present()
    assert not f.ok
    assert "WSL" in f.detail


def test_gpu_present():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="NVIDIA GeForce RTX 3090, 24576 MiB\n",
        stderr="",
    )
    with mock.patch("shutil.which", return_value="/usr/bin/nvidia-smi"), \
         mock.patch("subprocess.run", return_value=fake_out):
        f = _gpu_present()
    assert f.ok
    assert "RTX" in f.detail


def test_gpu_no_binary():
    with mock.patch("shutil.which", return_value=None):
        f = _gpu_present()
    assert not f.ok
    assert "nvidia-smi" in f.detail


def test_docker_present():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="Server: Docker Desktop\n\nServer Version: 24.0.0\n",
        stderr="",
    )
    with mock.patch("shutil.which", return_value="/usr/bin/docker"), \
         mock.patch("subprocess.run", return_value=fake_out):
        f = _docker_present()
    assert f.ok
    assert "docker" in f.detail


def test_docker_daemon_down():
    fake_out = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="Cannot connect to Docker daemon",
    )
    with mock.patch("shutil.which", return_value="/usr/bin/docker"), \
         mock.patch("subprocess.run", return_value=fake_out):
        f = _docker_present()
    assert not f.ok


def test_api_keys_all_present():
    env = {"HF_TOKEN": "x", "OPENAI_API_KEY": "y"}
    with mock.patch.dict(os.environ if (os := __import__("os")) else {}, env, clear=False):
        findings = _api_keys_present(["HF_TOKEN", "OPENAI_API_KEY"])
    assert all(f.ok for f in findings)


def test_api_keys_missing():
    env = {"PATH": "/tmp"}
    with mock.patch.dict(os.environ if (os := __import__("os")) else {}, env, clear=True):
        findings = _api_keys_present(["HF_TOKEN", "OPENAI_API_KEY"])
    assert not any(f.ok for f in findings)
    assert any("HF_TOKEN" in f.detail or f.name == "env_HF_TOKEN" for f in findings)


def test_api_keys_empty_for_local():
    findings = _api_keys_present([])
    assert len(findings) == 1
    assert findings[0].ok


# ---------- run_preflight : couverture par profil --------------------------


def test_run_preflight_local_runs_python_jupyter_kernels():
    fake_jout = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="\n".join([
            "Available kernels:",
            "  python3    /usr/share/jupyter/kernels/python3",
        ]),
        stderr="",
    )
    with mock.patch("subprocess.run", return_value=fake_jout):
        report = run_preflight("local")
    assert report.profile == "local"
    assert {f.name for f in report.findings} == {
        "python_version", "jupyter_cli", "kernels",
    }


def test_run_preflight_genai_runs_everything():
    fake_jout = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="\n".join([
            "Available kernels:",
            "  python3    /usr/share/jupyter/kernels/python3",
            "  .net-csharp   /home/x/.local/share/jupyter/kernels/.net-csharp",
        ]),
        stderr="",
    )
    fake_dotnet = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="9.0.0\n", stderr="",
    )
    fake_lake = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="Lake version 5.0.0 (Lean version 4.32.1)\n",
        stderr="",
    )
    fake_gpu = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="RTX 3090, 24576 MiB\n",
        stderr="",
    )
    fake_docker = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="Server Version: 24.0.0\n", stderr="",
    )

    def fake_run(args, **kwargs):
        cmd = args[0] if args else ""
        if cmd == "jupyter":
            return fake_jout
        if cmd == "dotnet":
            return fake_dotnet
        if cmd == "wsl":
            return fake_lake
        if cmd == "nvidia-smi":
            return fake_gpu
        if cmd == "docker":
            return fake_docker
        raise AssertionError(f"unexpected command: {cmd}")

    with mock.patch("shutil.which", return_value="/usr/bin/x"), \
         mock.patch.dict(os.environ if (os := __import__("os")) else {}, {}, clear=True), \
         mock.patch("subprocess.run", side_effect=fake_run):
        report = run_preflight("genai")
    names = {f.name for f in report.findings}
    assert "python_version" in names
    assert "kernels" in names
    assert "dotnet_sdk" in names
    assert "lean4_wsl" in names
    assert "gpu_nvidia" in names
    assert "docker" in names
    assert "env_HF_TOKEN" in names


def test_run_preflight_unknown_profile():
    with pytest.raises(ValueError, match="Profil inconnu"):
        run_preflight("policier")


def test_report_to_dict_serializable():
    report = Report(profile="local")
    report.findings.append(Finding(
        name="x", ok=True, detail="d", repair="r",
    ))
    d = report.to_dict()
    json.dumps(d)  # must not raise
    assert d["profile"] == "local"
    assert d["ready"] is True
    assert d["findings"][0]["name"] == "x"


def test_report_not_ready_when_any_finding_fails():
    report = Report(profile="local")
    report.findings.append(Finding(name="a", ok=True, detail=""))
    report.findings.append(Finding(name="b", ok=False, detail="missing"))
    assert report.ready is False