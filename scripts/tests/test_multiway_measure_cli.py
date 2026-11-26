"""Le collecteur refuse les mesures invalides même en mode optimisé."""
import os
import subprocess
import sys
from pathlib import Path


RUNNER = Path(__file__).resolve().parents[1] / "hypergraph" / "measure_multiway.py"


def _moteur(tmp_path: Path) -> Path:
    """Faux moteur : observation invalide (states=999) dès la profondeur 16.

    Sous Windows, CreateProcess n'exécute pas un script shebang : un
    ``.cmd`` relaie vers le même Python que pytest (issue #27685).
    """
    corps = (
        "import json, sys\n"
        "if sys.argv[1] != '--self-test':\n"
        "    print(json.dumps({'depth': int(sys.argv[1]), 'states': 999, "
        "'seconds': 1.0, 'witness': True}))\n"
    )
    if os.name == "nt":
        script = tmp_path / "moteur.py"
        script.write_text(corps, encoding="utf-8")
        moteur = tmp_path / "moteur.cmd"
        moteur.write_text(f'@"{sys.executable}" "{script}" %*\n', encoding="utf-8")
        return moteur
    moteur = tmp_path / "moteur"
    moteur.write_text("#!/usr/bin/env python3\n" + corps, encoding="utf-8")
    moteur.chmod(0o755)
    return moteur


def test_cli_rejects_invalid_observation_under_optimized_python(tmp_path: Path) -> None:
    engine = _moteur(tmp_path)
    output, raw = tmp_path / "result.json", tmp_path / "raw.json"
    result = subprocess.run(
        [sys.executable, "-O", str(RUNNER), str(engine), "--output", str(output), "--raw", str(raw)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=False,
    )
    assert result.returncode != 0
    assert "Observation invalide" in result.stderr
    assert "profondeur 16" in result.stderr
    assert not output.exists()
    assert not raw.exists()
