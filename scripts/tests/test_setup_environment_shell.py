"""Exécute le script de configuration avec des commandes externes simulées."""

import os
from pathlib import Path
import subprocess

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "environment/setup_environment.sh"


@pytest.fixture
def setup(tmp_path: Path):
    commands = tmp_path / "bin"
    commands.mkdir()
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    def stub(name: str, body: str) -> None:
        path = commands / name
        path.write_text("#!/bin/bash\n" + body + "\n")
        path.chmod(0o755)

    stub("python3", '''if [[ "$1" == --version ]]; then echo 'Python 3.12'; fi
if [[ "$1 $2" == '-m ipykernel' && "${FAIL_STEP:-}" == python ]]; then exit 1; fi
exit 0''')
    stub("dotnet", '''case "$*" in
  'nuget list source') [[ "${FAIL_STEP:-}" == nuget ]] && exit 1; echo nuget.org;;
  'nuget add source'*) exit 1;;
  'tool list -g') [[ "${FAIL_STEP:-}" == interactive ]] && exit 1; echo microsoft.dotnet-interactive;;
  'tool install '*) exit 1;;
  'interactive jupyter install') [[ "${FAIL_STEP:-}" == dotnet ]] && exit 1;;
  '--version') echo 9.0;;
esac
exit 0''')
    stub("jupyter", '''if [[ "$1" == --data-dir ]]; then
  [[ "${FAIL_STEP:-}" == data ]] && exit 1
  [[ "${FAIL_STEP:-}" == empty ]] || echo "$DATA_DIR"
fi
exit 0''')
    stub("mkdir", '''[[ "${FAIL_STEP:-}" == mkdir ]] && exit 1
exec /bin/mkdir "$@"''')
    env = os.environ.copy()
    env.update(PATH=f'{commands}:{env["PATH"]}', DATA_DIR=str(tmp_path / "data"))

    def run(*args: str, fail: str = "") -> subprocess.CompletedProcess:
        return subprocess.run(["bash", str(SCRIPT), *args], cwd=run_dir,
                              env=env | {"FAIL_STEP": fail}, text=True,
                              capture_output=True, check=False)

    return run_dir, run


@pytest.mark.parametrize("failure,checkpoint,label", [
    ("data", "jupyter_directory_setup", "Répertoire Jupyter"),
    ("empty", "jupyter_directory_setup", "Répertoire Jupyter"),
    ("mkdir", "jupyter_directory_setup", "Répertoire Jupyter"),
    ("python", "python_kernel_install", "Kernel Python"),
    ("dotnet", "dotnet_kernel_install", "Kernels .NET"),
    ("nuget", "dotnet_nuget_config", "Configuration NuGet"),
    ("interactive", "dotnet_interactive_install", "Installation .NET Interactive"),
])
def test_failure_and_resume(setup, failure, checkpoint, label):
    run_dir, run = setup
    failed = run("--auto-fix", fail=failure)
    assert failed.returncode == 2, failed.stdout + failed.stderr
    assert label in failed.stdout and "CONFIGURATIONS ÉCHOUÉES" in failed.stdout
    assert checkpoint not in (run_dir / "setup_checkpoint.txt").read_text().splitlines()
    resumed = run("--auto-fix", "--resume")
    assert resumed.returncode == 0, resumed.stdout + resumed.stderr
    assert checkpoint in (run_dir / "setup_checkpoint.txt").read_text().splitlines()


def test_dry_and_force_resume(setup):
    run_dir, run = setup
    dry = run("--check", "--force", "--auto-fix", "--resume", fail="data")
    assert dry.returncode == 0, dry.stdout + dry.stderr
    assert "Packages requis : 9/9 (100.0%)" in dry.stdout
    assert "manquant (mode --check" not in dry.stdout
    assert not list(run_dir.iterdir())
    assert run("--auto-fix").returncode == 0
    failed = run("--auto-fix", "--resume", "--force", fail="data")
    assert failed.returncode == 2
    assert "jupyter_directory_setup" not in (run_dir / "setup_checkpoint.txt").read_text().splitlines()
    assert run("--auto-fix", "--resume").returncode == 0
