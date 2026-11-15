"""Contrat CLI du compagnon POSIX de launch_capped.ps1."""
import os
import subprocess
import sys
from pathlib import Path

import pytest


SCRIPT = (Path(__file__).resolve().parents[3] /
          "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/launchers/launch_capped.sh")


@pytest.mark.skipif(os.name == "nt", reason="Le compagnon cible bash POSIX")
def test_launch_capped_posix_quote_les_chemins_et_propage_le_code_enfant(tmp_path):
    pytest.importorskip("psutil")
    out_dir = tmp_path / "logs avec espaces"
    log_path = out_dir / "train log.txt"
    err_path = out_dir / "train err.txt"
    pid_path = out_dir / "train pid.txt"
    lock_path = out_dir / "lock dir" / "train.lock"
    child = "import sys; print('sortie enfant'); print('erreur enfant', file=sys.stderr); sys.exit(7)"

    result = subprocess.run(
        ["bash", str(SCRIPT),
         "--python-exe", sys.executable,
         "--memory-cap-gib", "1",
         "--reserve-gib", "0.1",
         "--max-commit-charge-pct", "90",
         "--log-path", str(log_path),
         "--err-path", str(err_path),
         "--pid-path", str(pid_path),
         "--lock-path", str(lock_path),
         "--", sys.executable, "-c", child],
        text=True, capture_output=True, timeout=30,
    )

    assert result.returncode == 7, result.stdout + result.stderr
    assert "sortie enfant" in log_path.read_text(encoding="utf-8")
    assert "erreur enfant" in err_path.read_text(encoding="utf-8")
    assert pid_path.read_text(encoding="utf-8").strip().isdigit()
    assert "NON APPLICABLE" in log_path.read_text(encoding="utf-8")


@pytest.mark.skipif(os.name == "nt", reason="Le compagnon cible bash POSIX")
def test_launch_capped_posix_refuse_une_commande_absente():
    result = subprocess.run(
        ["bash", str(SCRIPT), "--log-path", "run.log", "--err-path", "run.err",
         "--pid-path", "run.pid"],
        text=True, capture_output=True, timeout=10,
    )
    assert result.returncode == 2
    assert "Commande absente" in result.stderr
