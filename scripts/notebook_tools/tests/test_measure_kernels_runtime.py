"""Tests du relevé runtime avec noyau factice et lancement Jupyter réel séparé."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import measure_kernels_runtime as collector  # noqa: E402


class FakeClient:
    def __init__(self, events):
        self.events = list(events)

    def start_channels(self): pass
    def wait_for_ready(self, timeout): pass
    def execute(self, code): return "msg-1"
    def get_iopub_msg(self, timeout): return self.events.pop(0)
    def stop_channels(self): pass


class FakeManager:
    def __init__(self, *, events=None, start_error=None):
        self.events = events or []
        self.start_error = start_error
        self.shutdowns = 0

    def start_kernel(self):
        if self.start_error:
            raise self.start_error

    def client(self): return FakeClient(self.events)
    def shutdown_kernel(self, now): self.shutdowns += 1


def _msg(kind, content):
    return {"parent_header": {"msg_id": "msg-1"},
            "msg_type": kind, "content": content}


def test_probe_mesure_les_donnees_emises_et_ferme_le_noyau():
    manager = FakeManager(events=[_msg("stream", {"text":
        'COURSIA_KERNEL_RUNTIME={"python_version":"3.13.1",'
        '"executable":"/venv/bin/python", "numpy_version":"2.2.0",'
        '"numpy_status":"ok"}\n'})])
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "ok", "python_version": "3.13.1",
                      "executable": "/venv/bin/python", "numpy_version": "2.2.0",
                      "numpy_status": "ok"}
    assert manager.shutdowns == 1


def test_erreur_noyau_est_structuree_sans_texte_exception():
    manager = FakeManager(events=[_msg("error", {"ename": "ImportError",
                                                   "evalue": "secret-value"})])
    result = collector._probe_kernel("demo", 5,
                                     manager_factory=lambda **_: manager)
    assert result == {"status": "probe_error", "error_type": "ImportError"}
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
    assert collector._probe_kernel(
        "demo", 5,
        manager_factory=lambda **_: FakeManager(events=[
            _msg("status", {"execution_state": "idle"})]))["status"] == "not_python"
    assert collector.collect(names=["absent"])["kernels"][0]["status"] == "kernelspec_missing"
