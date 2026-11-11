"""Tests hors ligne du heal shallow propre au job Scripts Tests (#24986)."""

import os
import subprocess
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "scripts-tests.yml"
STEP = '      - name: "Purger un work dir reutilise au graphe incomplet (#15387)"\n'
BASH = resolve_bash()


def _git(cwd, *args, check=True):
    return subprocess.run(
        ["git", "-C", str(cwd), *args], check=check, capture_output=True,
        text=True, encoding="utf-8",
    )


def _heal_script():
    text = WORKFLOW.read_text(encoding="utf-8")
    block = text.split(STEP, 1)[1].split("\n      - uses: actions/checkout@v4", 1)[0]
    lines = block.splitlines()
    assert lines[0].strip() == "shell: bash"
    assert lines[1].strip() == "run: |"
    return "\n".join(line[10:] if line.startswith("          ") else line for line in lines[2:]) + "\n"


@pytest.fixture
def shallow_repo(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    _git(source, "init", "--quiet", "-b", "main")
    _git(source, "config", "user.email", "test@example.invalid")
    _git(source, "config", "user.name", "test")
    for index in range(4):
        (source / "history.txt").write_text(f"commit {index}\n", encoding="utf-8")
        _git(source, "add", "history.txt")
        _git(source, "commit", "--quiet", "-m", f"commit {index}")
    bare = tmp_path / "origin.git"
    _git(tmp_path, "clone", "--quiet", "--bare", str(source), str(bare))
    clone = tmp_path / "clone"
    subprocess.run(
        ["git", "clone", "--quiet", "--depth=1", "--branch", "main", bare.as_uri(), str(clone)],
        check=True, capture_output=True, text=True,
    )
    assert _git(clone, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
    return clone, bare


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_unshallow_local_reussit_et_garde_le_depot(shallow_repo, tmp_path):
    clone, _ = shallow_repo
    script = tmp_path / "heal.sh"
    script.write_text(_heal_script(), encoding="utf-8")
    env = dict(os.environ, GITHUB_WORKSPACE=str(clone))
    result = subprocess.run([BASH, str(script)], env=env, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert "unshallow explicite reussi" in result.stdout
    assert (clone / ".git").is_dir()
    assert not (clone / ".git" / "shallow").exists()
    assert _git(clone, "rev-list", "--all", "--count").stdout.strip() == "4"


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_echec_unshallow_purge_le_depot_incomplet(shallow_repo, tmp_path):
    clone, _ = shallow_repo
    _git(clone, "remote", "set-url", "origin", (tmp_path / "absent.git").as_uri())
    script = tmp_path / "heal.sh"
    script.write_text(_heal_script(), encoding="utf-8")
    env = dict(os.environ, GITHUB_WORKSPACE=str(clone))
    result = subprocess.run([BASH, str(script)], env=env, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert "unshallow impossible ou graphe incomplet" in result.stdout
    assert not (clone / ".git").exists()
