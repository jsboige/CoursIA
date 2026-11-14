"""Le collecteur refuse les mesures invalides même en mode optimisé."""
import subprocess
import sys
from pathlib import Path


RUNNER = Path(__file__).resolve().parents[1] / "hypergraph" / "measure_multiway.py"


def test_cli_rejects_invalid_observation_under_optimized_python(tmp_path: Path) -> None:
    engine = tmp_path / "moteur"
    engine.write_text(
        "#!/usr/bin/env python3\n"
        "import json, sys\n"
        "if sys.argv[1] != '--self-test':\n"
        "    print(json.dumps({'depth': int(sys.argv[1]), 'states': 999, "
        "'seconds': 1.0, 'witness': True}))\n",
        encoding="utf-8",
    )
    engine.chmod(0o755)
    output, raw = tmp_path / "result.json", tmp_path / "raw.json"
    result = subprocess.run(
        [sys.executable, "-O", str(RUNNER), str(engine), "--output", str(output), "--raw", str(raw)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode != 0
    assert "Observation invalide" in result.stderr
    assert "profondeur 16" in result.stderr
    assert not output.exists()
    assert not raw.exists()
