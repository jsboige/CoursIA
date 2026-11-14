"""Régressions du véritable audit Bash avec des outils système simulés."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path
from typing import Callable

import pytest


REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts/environment/audit_environment.sh"
BASH = shutil.which("bash")


STUBS = {
    "pgrep": r'''#!/usr/bin/env bash
if [[ "$PGREP_MODE" == bsd-* ]]; then
  if [[ "$1" != "-x" ]]; then echo "illegal option -- c" >&2; exit 2; fi
  case "$PGREP_MODE" in
    bsd-positive) printf '101\n202\n'; exit 0 ;;
    bsd-empty) exit 1 ;;
    bsd-error) echo "échec pgrep" >&2; exit 2 ;;
    bsd-invalid) printf '101\nPID invalide\n'; exit 0 ;;
  esac
fi
if [[ "$1" == "-xc" ]]; then
  case "$PGREP_MODE" in
    empty) printf '0\n'; exit 1 ;;
    positive) printf '2\n'; exit 0 ;;
    unsupported-zero|unsupported-positive) echo 'option -x indisponible' >&2; exit 2 ;;
    multiline) printf '0\n0\n'; exit 1 ;;
  esac
fi
if [[ "$1" == "-c" ]]; then
  if [[ "$PGREP_MODE" == unsupported-positive ]]; then printf '3\n'; exit 0; fi
  printf '0\n'; exit 1
fi
exit 2
''',
    "df": r'''#!/usr/bin/env bash
printf '%s\n' "$*" >> "$DF_CALLS"
if [[ "$1" == "-BG" ]]; then echo 'option GNU indisponible' >&2; exit 1; fi
if [[ "$1" == "-h" ]]; then
  if (( FREE_KB < 5242880 )); then available=4G
  elif (( FREE_KB < 20971520 )); then available=10G
  else available=80G
  fi
  printf 'Filesystem Size Used Avail Use%% Mounted on\n/dev/mock 100G 20G %s 20%% /mock\n' "$available"
  exit 0
fi
if [[ "$1" == "-k" ]]; then
  printf 'Filesystem 1024-blocks Used Available Capacity Mounted on\n/dev/mock 104857600 20971520 %s 20%% /mock\n' "$FREE_KB"
  exit 0
fi
exit 1
''',
    "uname": r'''#!/usr/bin/env bash
printf '%s\n' "$OS_MODE"
''',
    "python3": r'''#!/usr/bin/env bash
if [[ "$1" == "--version" ]]; then echo 'Python 3.12.0'; exit 0; fi
if [[ "$1" == "-m" && "$2" == "pip" ]]; then exit 1; fi
exit 0
''',
    "conda": r'''#!/usr/bin/env bash
if [[ "$1" == "--version" ]]; then echo 'conda 24.0'; exit 0; fi
if [[ "$1" == "env" ]]; then printf '# conda environments\nbase * /fake/base\n'; exit 0; fi
exit 0
''',
    "jupyter": r'''#!/usr/bin/env bash
if [[ "$1" == "--version" ]]; then echo 'Selected Jupyter core packages'; exit 0; fi
if [[ "$1" == "lab" ]]; then echo '4.0.0'; exit 0; fi
exit 0
''',
    "dotnet": r'''#!/usr/bin/env bash
if [[ "$1" == "--list-sdks" ]]; then echo '9.0.100 [/fake/sdk]'; exit 0; fi
if [[ "$1" == "tool" ]]; then printf 'Package Id Version\nmicrosoft.dotnet-interactive 1.0.0\n'; exit 0; fi
exit 0
''',
    "free": r'''#!/usr/bin/env bash
printf 'Mem: 16 8 8\n'
''',
    "sysctl": r'''#!/usr/bin/env bash
printf '17179869184\n'
''',
}


@pytest.fixture
def audit_runner(
    tmp_path: Path,
) -> tuple[Callable[..., subprocess.CompletedProcess[str]], Path]:
    """Prépare un PATH contrôlé sans copier la logique de l'audit."""
    if BASH is None:
        pytest.skip("bash requis pour le script compagnon")

    bindir = tmp_path / "bin"
    bindir.mkdir()
    for name, body in STUBS.items():
        executable = bindir / name
        executable.write_text(body, encoding="utf-8")
        executable.chmod(0o755)

    calls_file = tmp_path / "df-calls.txt"

    def run(
        mode: str = "empty", os_name: str = "Linux", free_kb: int = 83886080
    ) -> subprocess.CompletedProcess[str]:
        env = dict(os.environ)
        env.update(
            PATH=f"{bindir}{os.pathsep}{env['PATH']}",
            PGREP_MODE=mode,
            OS_MODE=os_name,
            FREE_KB=str(free_kb),
            DF_CALLS=str(calls_file),
        )
        return subprocess.run(
            [BASH, str(SCRIPT)],
            cwd=tmp_path,
            env=env,
            text=True,
            capture_output=True,
            timeout=15,
        )

    return run, calls_file


def test_aucun_processus_ne_provoque_pas_derreur_arithmetique(audit_runner) -> None:
    run, _ = audit_runner
    result = run("empty")

    assert result.returncode == 2  # Dépendances requises absentes dans le PATH simulé.
    assert "syntax error in expression" not in result.stderr
    assert "[WARNING] Processus jupyter" not in result.stdout


def test_processus_detecte_est_signale(audit_runner) -> None:
    run, _ = audit_runner
    result = run("positive")

    assert result.returncode == 2
    assert "[WARNING] Processus jupyter 2 instance(s) en cours" in result.stdout


@pytest.mark.parametrize(
    ("mode", "expected_warning"),
    [
        ("unsupported-zero", None),
        ("unsupported-positive", "[WARNING] Processus jupyter 3 instance(s) en cours"),
        ("multiline", None),
    ],
)
def test_pgrep_incompatible_ou_mal_forme_utilise_un_compte_valide(
    audit_runner, mode: str, expected_warning: str | None
) -> None:
    run, _ = audit_runner
    result = run(mode)

    assert result.returncode == 2
    assert "syntax error in expression" not in result.stderr
    if expected_warning is None:
        assert "[WARNING] Processus jupyter" not in result.stdout
    else:
        assert expected_warning in result.stdout


@pytest.mark.parametrize(
    ("os_name", "free_kb", "expected_status"),
    [
        ("Linux", 83886080, "OK"),
        ("Darwin", 83886080, "OK"),
        ("Darwin", 4194304, "ERROR"),
        ("Darwin", 10485760, "WARNING"),
    ],
)
def test_seuil_disque_est_lu_avec_df_k_sur_linux_et_darwin(
    audit_runner, os_name: str, free_kb: int, expected_status: str
) -> None:
    run, calls_file = audit_runner
    result = run("empty", os_name=os_name, free_kb=free_kb)

    assert result.returncode == 2
    assert f"[{expected_status}] Espace disque (.)" in result.stdout
    calls = calls_file.read_text(encoding="utf-8").splitlines()
    assert "-k ." in calls
    assert not any(call.startswith("-BG") for call in calls)


@pytest.mark.parametrize(
    "mode,count",
    [("bsd-positive", 2), ("bsd-empty", 0), ("bsd-error", 0), ("bsd-invalid", 0)],
)
def test_pgrep_bsd_sans_option_count(audit_runner, mode: str, count: int) -> None:
    """Le pgrep macOS fournit des PID, sans prendre en charge -c."""
    run, _ = audit_runner
    result = run(mode, os_name="Darwin")
    assert result.returncode == 2
    assert "syntax error" not in result.stderr
    warning = "[WARNING] Processus jupyter"
    if count:
        assert f"{warning} {count} instance(s) en cours" in result.stdout
    else:
        assert warning not in result.stdout
