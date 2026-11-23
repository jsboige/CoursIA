"""Les anciens points d'entrée et les nouvelles cibles restent exécutables."""
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("name", [
    "check_epic_charter", "epic_body_staleness", "epic_neglect_sweep",
])
def test_old_and_new_entrypoints_show_help(name):
    for path in (ROOT / "scripts" / f"{name}.py",
                 ROOT / "scripts" / "epic" / f"{name}.py"):
        run = subprocess.run([sys.executable, str(path), "--help"],
                             capture_output=True, text=True, cwd=ROOT)
        assert run.returncode == 0, run.stderr
        assert "usage:" in run.stdout.lower()


def test_old_and_new_neglect_self_tests_match():
    runs = [subprocess.run([sys.executable, str(path), "--self-test"],
                           capture_output=True, text=True, cwd=ROOT)
            for path in (ROOT / "scripts/epic_neglect_sweep.py",
                         ROOT / "scripts/epic/epic_neglect_sweep.py")]
    assert all(run.returncode == 0 for run in runs)
    assert runs[0].stdout == runs[1].stdout
    assert "SELF-TEST OK" in runs[0].stdout
