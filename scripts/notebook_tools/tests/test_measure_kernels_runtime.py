"""Tests du relevé runtime avec noyau factice et lancement Jupyter réel séparé."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import measure_kernels_runtime as collector  # noqa: E402


class FakeClient:
    def __init__(self, events, language="python"):
        self.events = list(events)
        self.language = language

    def start_channels(self): pass
    def wait_for_ready(self, timeout): pass
    def kernel_info(self): return "info-1"
    def get_shell_msg(self, timeout):
        return {"parent_header": {"msg_id": "info-1"}, "content": {
            "language_info": {"name": self.language}}}
    def execute(self, code): return "msg-1"
    def get_iopub_msg(self, timeout): return self.events.pop(0)
    def stop_channels(self): pass


class FakeManager:
    def __init__(self, *, events=None, start_error=None, language="python"):
        self.events = events or []
        self.start_error = start_error
        self.language = language
        self.shutdowns = 0

    def start_kernel(self, **kwargs):
        assert kwargs["stdout"] == collector.subprocess.DEVNULL
        assert kwargs["stderr"] == collector.subprocess.DEVNULL
        if self.start_error:
            raise self.start_error

    def client(self): return FakeClient(self.events, self.language)
    def shutdown_kernel(self, now): self.shutdowns += 1


def _msg(kind, content):
    return {"parent_header": {"msg_id": "msg-1"},
            "msg_type": kind, "content": content}


def test_probe_accumule_les_fragments_et_ferme_le_noyau():
    line = ('COURSIA_KERNEL_RUNTIME={"python_version":"3.13.1",'
            '"executable":"/venv/bin/python", "numpy_version":"2.2.0",'
            '"numpy_status":"ok"}\n')
    midpoint = len(line) // 2
    manager = FakeManager(events=[_msg("stream", {"text": line[:midpoint]}),
                                  _msg("stream", {"text": line[midpoint:]}),
                                  _msg("status", {"execution_state": "idle"})])
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "ok", "kernel_language": "python",
                      "python_version": "3.13.1",
                      "executable": "/venv/bin/python", "numpy_version": "2.2.0",
                      "numpy_status": "ok"}
    assert manager.shutdowns == 1


def test_erreur_noyau_est_structuree_sans_texte_exception():
    manager = FakeManager(events=[_msg("error", {"ename": "ImportError",
                                                   "evalue": "secret-value"})])
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "probe_error", "error_type": "KernelExecutionError"}
    assert "secret-value" not in json.dumps(result)
    assert manager.shutdowns == 1


def test_echec_avant_demarrage_ne_tente_pas_de_fermer_un_noyau():
    manager = FakeManager(start_error=RuntimeError("credential=private"))
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "startup_error", "error_type": "RuntimeError"}
    assert manager.shutdowns == 0
    assert "private" not in json.dumps(result)


def test_timeout_est_structure_et_le_noyau_lance_est_arrete():
    class TimeoutClient(FakeClient):
        def wait_for_ready(self, timeout): raise TimeoutError("private startup detail")

    manager = FakeManager()
    manager.client = lambda: TimeoutClient([])
    result = collector._probe_kernel("demo", 0.01,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "timeout", "error_type": "TimeoutError"}
    assert manager.shutdowns == 1
    assert "private" not in json.dumps(result)


def test_kernel_non_python_et_absent_dans_le_releve():
    manager = FakeManager(language="csharp")
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "not_python", "kernel_language": "csharp"}
    assert manager.shutdowns == 1
    assert collector.collect(names=["absent"])["kernels"][0]["status"] == "kernelspec_missing"


def test_kernel_python_silencieux_est_signale_comme_echec_sonde():
    manager = FakeManager(events=[_msg("status", {"execution_state": "idle"})])
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "probe_output_missing",
                      "error_type": "MissingProbeOutput",
                      "kernel_language": "python"}
    assert manager.shutdowns == 1


@pytest.mark.parametrize("payload", [
    {},
    {"python_version": "3.12", "executable": "/python", "numpy_version": None,
     "numpy_status": "absent", "status": "ok"},
    {"python_version": 3, "executable": "/python", "numpy_version": None,
     "numpy_status": "absent"},
    {"python_version": "3.12", "executable": "/python", "numpy_version": None,
     "numpy_status": "ok"},
    [],
])
def test_sortie_incomplete_ou_incoherente_est_rejetee(payload):
    manager = FakeManager(events=[
        _msg("stream", {"text": "COURSIA_KERNEL_RUNTIME=" + json.dumps(payload) + "\n"}),
        _msg("status", {"execution_state": "idle"}),
    ])
    assert collector._probe_kernel("demo", 5, manager_factory=lambda **_: manager) == {
        "status": "invalid_probe_output", "error_type": "InvalidProbeData"
    }
    assert manager.shutdowns == 1


@pytest.mark.parametrize("numpy_fields", [
    {"numpy_version": None, "numpy_status": "absent"},
    {"numpy_version": None, "numpy_status": "error", "numpy_error_type": "ImportError"},
])
def test_sonde_valide_sans_numpy_charge(numpy_fields):
    payload = {"python_version": "3.12", "executable": "/python", **numpy_fields}
    manager = FakeManager(events=[
        _msg("stream", {"text": "COURSIA_KERNEL_RUNTIME=" + json.dumps(payload) + "\n"}),
        _msg("status", {"execution_state": "idle"}),
    ])
    assert collector._probe_kernel("demo", 5, manager_factory=lambda **_: manager) == {
        "status": "ok", "kernel_language": "python", **payload,
    }


@pytest.mark.parametrize("code,expected", [
    ("import time; time.sleep(30)", "timeout"),
    ("raise SystemExit(1)", "startup_error"),
])
def test_readiness_noyau_reel_silencieux_ou_mort(tmp_path, code, expected):
    from jupyter_client import KernelManager
    from jupyter_client.kernelspec import KernelSpecManager

    spec_dir = tmp_path / "test-kernel"
    spec_dir.mkdir()
    (spec_dir / "kernel.json").write_text(json.dumps({
        "argv": [sys.executable, "-c", code, "{connection_file}"],
        "display_name": "Test", "language": "python",
    }), encoding="utf-8")
    specs = KernelSpecManager(kernel_dirs=[str(tmp_path)], ensure_native_kernel=False)
    manager = KernelManager(kernel_name="test-kernel", kernel_spec_manager=specs)
    result = collector._probe_kernel("test-kernel", 1, manager_factory=lambda **_: manager)
    assert result["status"] == expected
    assert not manager.is_alive()


def test_autre_runtime_error_readiness_n_est_pas_un_timeout():
    class ErrorClient(FakeClient):
        def wait_for_ready(self, timeout):
            raise RuntimeError("unexpected private error")

    manager = FakeManager()
    manager.client = lambda: ErrorClient([])
    assert collector._probe_kernel("demo", 1, manager_factory=lambda **_: manager) == {
        "status": "startup_error", "error_type": "RuntimeError"
    }
    assert manager.shutdowns == 1
