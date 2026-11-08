import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts/research/aima_mapping.py"
ARTIFACT_DIR = REPO_ROOT / "docs/curriculum/aima-mapping"
FILES = (
    "aima3e-toc.csv",
    "aima4e-toc.csv",
    "aima-walk-sections.csv",
    "aima-walk-chapitres.csv",
    "aima-hors-livre.csv",
    "aima-mapping-resume.json",
)


def _copy_artifacts(destination: Path) -> dict[str, bytes]:
    snapshots = {}
    for name in FILES:
        source = ARTIFACT_DIR / name
        data = source.read_bytes()
        snapshots[name] = data
        (destination / name).write_bytes(data)
    return snapshots


def _run_check(out_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), "check", "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def test_check_replays_map_and_reports_artifact_drift(tmp_path: Path) -> None:
    snapshots = _copy_artifacts(tmp_path)

    valid = _run_check(tmp_path)
    assert valid.returncode == 0, valid.stdout + valid.stderr

    (tmp_path / "aima-hors-livre.csv").write_bytes(
        snapshots["aima-hors-livre.csv"] + b"ligne ajoutee\n"
    )
    drift = _run_check(tmp_path)
    assert drift.returncode == 1
    assert "drift détecté : aima-hors-livre.csv" in drift.stderr
    assert "-ligne ajoutee" in drift.stderr

    assert {name: (ARTIFACT_DIR / name).read_bytes() for name in FILES} == snapshots


@pytest.mark.parametrize(
    "name",
    ["aima-walk-sections.csv", "aima-walk-chapitres.csv", "aima-mapping-resume.json"],
)
def test_check_names_each_drifted_artifact(tmp_path: Path, name: str) -> None:
    _copy_artifacts(tmp_path)
    artifact = tmp_path / name
    artifact.write_bytes(artifact.read_bytes() + b"drift\n")

    result = _run_check(tmp_path)

    assert result.returncode == 1
    assert f"drift détecté : {name}" in result.stderr
