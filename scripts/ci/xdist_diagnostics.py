"""Instantané du test actif par worker pour le watchdog CI."""

import os
from pathlib import Path


def _state_file():
    directory = os.environ.get("COURSIA_XDIST_DIAGNOSTICS")
    worker = os.environ.get("PYTEST_XDIST_WORKER")
    if directory and worker and worker.startswith("gw") and worker[2:].isdigit():
        return Path(directory) / worker
    return None


def pytest_runtest_protocol(item, nextitem):
    path = _state_file()
    if path:
        try:
            path.write_text(item.nodeid.split("[", 1)[0], encoding="utf-8")
        except OSError:
            pass  # Le diagnostic ne doit jamais modifier le verdict.


def pytest_runtest_logfinish(nodeid, location):
    path = _state_file()
    if path:
        try:
            path.unlink(missing_ok=True)
        except OSError:
            pass
