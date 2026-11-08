"""Contrats du lanceur Kernel Gateway et fumée CPU sur une fixture temporaire."""
from __future__ import annotations

import importlib.util
import json
import os
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "kernel_gateway_service.py"
MODULE_SPEC = importlib.util.spec_from_file_location("kernel_gateway_service", SCRIPT)
assert MODULE_SPEC is not None and MODULE_SPEC.loader is not None
service = importlib.util.module_from_spec(MODULE_SPEC)
sys.modules[MODULE_SPEC.name] = service
MODULE_SPEC.loader.exec_module(service)


def fixture_notebook(directory: Path) -> Path:
    """Crée un notebook API minimal hors du dépôt, sans recopier un carnet de cours."""
    notebook = directory / "gateway_fixture.ipynb"
    document = {
        "cells": [
            {
                "cell_type": "code",
                "id": "gateway-add",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "# POST /add\n",
                    "import json\n",
                    "requete = json.loads(REQUEST) if isinstance(REQUEST, str) else REQUEST\n",
                    "corps = requete.get('body', {}) if isinstance(requete, dict) else {}\n",
                    "if isinstance(corps, str): corps = json.loads(corps)\n",
                    "print(json.dumps({'status': 'ok', 'sum': corps['a'] + corps['b']}))\n",
                ],
            }
        ],
        "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    notebook.write_text(json.dumps(document), encoding="utf-8")
    return notebook


class KernelGatewayServiceTests(unittest.TestCase):
    def test_preflight_rejects_missing_and_malformed_seed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            self.assertIn("notebook introuvable", service.preflight(folder / "absent.ipynb")[0])
            malformed = folder / "broken.ipynb"
            malformed.write_text("{", encoding="utf-8")
            errors = service.preflight(malformed)
            self.assertTrue(any("JSON invalide" in error for error in errors))

    def test_preflight_reports_missing_gateway_with_install_name(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            notebook = fixture_notebook(Path(temporary))
            with patch.object(service.importlib.util, "find_spec", return_value=None):
                errors = service.preflight(notebook)
            self.assertTrue(any("jupyter_kernel_gateway" in error for error in errors))

    def test_preflight_reports_notebook_kernel_that_is_not_installed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            notebook = fixture_notebook(Path(temporary))
            with patch("jupyter_client.kernelspec.KernelSpecManager.find_kernel_specs", return_value={}):
                errors = service.preflight(notebook)
            self.assertTrue(any("kernel Jupyter absent : 'python3'" in error for error in errors))

    def test_command_uses_notebook_directory_and_official_notebook_http_api(self) -> None:
        notebook = Path("/tmp/existing-hero.ipynb")
        command = service.build_command(notebook, "127.0.0.1", 8899)
        self.assertEqual(command[0], sys.executable)
        self.assertIn("--KernelGatewayApp.api=kernel_gateway.notebook_http", command)
        self.assertIn("--KernelGatewayApp.seed_uri=existing-hero.ipynb", command)
        self.assertIn("--KernelGatewayApp.ip=127.0.0.1", command)
        self.assertIn("--KernelGatewayApp.port=8899", command)
        self.assertIn("--KernelGatewayApp.port_retries=0", command)

    @unittest.skipUnless(importlib.util.find_spec("kernel_gateway"), "jupyter_kernel_gateway absent")
    def test_real_gateway_starts_and_calls_annotated_route_on_loopback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            notebook = fixture_notebook(Path(temporary))
            temporary_root = Path(temporary)
            kernel_directory = temporary_root / "jupyter-data" / "kernels" / "python3"
            kernel_directory.mkdir(parents=True)
            (kernel_directory / "kernel.json").write_text(
                json.dumps(
                    {
                        "argv": [sys.executable, "-m", "ipykernel_launcher", "-f", "{connection_file}"],
                        "display_name": "Python fixture",
                        "language": "python",
                    }
                ),
                encoding="utf-8",
            )
            runtime_directory = temporary_root / "jupyter-runtime"
            runtime_directory.mkdir()
            ipython_directory = temporary_root / "ipython"
            ipython_directory.mkdir()
            environment = os.environ.copy()
            environment.update(
                {
                    "JUPYTER_DATA_DIR": str(temporary_root / "jupyter-data"),
                    "JUPYTER_RUNTIME_DIR": str(runtime_directory),
                    "IPYTHONDIR": str(ipython_directory),
                }
            )
            with socket.socket() as reservation:
                reservation.bind(("127.0.0.1", 0))
                port = reservation.getsockname()[1]
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    str(notebook),
                    "--port",
                    str(port),
                    "--probe-path",
                    "/add",
                    "--probe-json",
                    '{"a": 20, "b": 22}',
                    "--probe-timeout",
                    "25",
                ],
                cwd=Path(temporary),
                env=environment,
                check=False,
                capture_output=True,
                text=True,
                timeout=35,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("HTTP 200 POST /add", result.stdout)
            self.assertIn('"sum": 42', result.stdout)


if __name__ == "__main__":
    unittest.main()
