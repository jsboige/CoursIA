"""Tests du contrat --path et des installations système de FFmpeg."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess


SCRIPT = Path(__file__).parents[1] / "environment" / "install-ffmpeg.sh"


def run_script(tmp_path: Path, os_type: str, *args: str) -> subprocess.CompletedProcess[str]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(exist_ok=True)
    log = tmp_path / "commands.log"
    for command in ("sudo", "apt-get", "yum", "dnf", "brew"):
        stub = bin_dir / command
        stub.write_text(f'#!/bin/sh\nprintf "%s\\n" "{command} $*" >> "{log}"\n')
        stub.chmod(0o755)
    ffmpeg = bin_dir / "ffmpeg"
    ffmpeg.write_text('#!/bin/sh\necho "ffmpeg version test"\n')
    ffmpeg.chmod(0o755)
    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"
    env["OSTYPE"] = os_type
    # Le chargement permet de simuler OSTYPE dans ce processus Bash sous Linux.
    command = 'OSTYPE="$1"; source "$2" "${@:3}"'
    result = subprocess.run(
        ["bash", "-c", command, "test", os_type, str(SCRIPT), *args],
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    result.command_log = log.read_text() if log.exists() else ""
    return result


def test_custom_path_fails_before_package_manager_even_with_force(tmp_path: Path) -> None:
    result = run_script(tmp_path, "linux-gnu", "--path", "/tmp/custom", "--force")

    assert result.returncode == 1
    assert "n’est pas pris en charge" in result.stderr
    assert "gestionnaire de paquets système" in result.stderr
    assert result.command_log == ""


def test_missing_or_empty_path_is_explained_before_installation(tmp_path: Path) -> None:
    missing = run_script(tmp_path / "missing", "linux-gnu", "--path")
    empty = run_script(tmp_path / "empty", "linux-gnu", "--path", "")

    for result in (missing, empty):
        assert result.returncode == 1
        assert "--path requiert un chemin non vide" in result.stderr
        assert result.command_log == ""


def test_help_documents_package_manager_installation(tmp_path: Path) -> None:
    result = run_script(tmp_path, "linux-gnu", "--help")

    assert result.returncode == 0
    assert "gestionnaire de paquets système" in result.stdout
    assert "ne sont pas pris en charge" in result.stdout
    assert result.command_log == ""


def test_default_linux_installation_still_uses_apt(tmp_path: Path) -> None:
    result = run_script(tmp_path, "linux-gnu", "--force")

    assert result.returncode == 0
    assert "sudo apt-get update" in result.command_log
    assert "sudo apt-get install -y ffmpeg" in result.command_log


def test_default_macos_installation_still_uses_homebrew(tmp_path: Path) -> None:
    result = run_script(tmp_path, "darwin", "--force")

    assert result.returncode == 0
    assert "brew install ffmpeg" in result.command_log
    assert "sudo " not in result.command_log
