"""Le préfixe attendu ne suffit pas à prouver que le noyau est un venv."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from unittest import mock

import pytest


_PATH = Path(__file__).resolve().parents[1] / "verify_kernel_env_runtime.py"
_SPEC = importlib.util.spec_from_file_location("verify_kernel_env_runtime", _PATH)
module = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(module)


@pytest.mark.parametrize(
    "prefix,base,expected,verdict",
    [
        ("/python", "/python", "/python", 1),
        ("/venv", "/python", "/venv", 0),
        ("/other", "/python", "/venv", 1),
    ],
)
def test_system_python_is_not_a_matching_venv(monkeypatch, capsys, prefix, base, expected, verdict):
    monkeypatch.setattr(sys, "argv", [str(_PATH), "--venv", expected])
    def execute_stub(command, **kwargs):
        output = {
            "cells": [{"outputs": [{"output_type": "stream", "name": "stdout",
                "text": ["RUNTIME sys.executable.basename=python3\n",
                         f"RUNTIME sys.prefix={prefix}\n",
                         f"RUNTIME sys.base_prefix={base}\n"]}]}]
        }
        Path(command[4]).write_text(json.dumps(output), encoding="utf-8")
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(module.subprocess, "run", execute_stub)
    assert module.main() == verdict
    output = capsys.readouterr().out
    assert ("VERDICT: PASS" in output) == (verdict == 0)
    if prefix == base:
        assert "SYSTEM Python" in output
