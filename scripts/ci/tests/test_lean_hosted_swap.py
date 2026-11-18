"""Le swap des jambes Lean hebergees se dimensionne sur l'espace libre.

Constat du 2026-11-04 : sur les runners heberges, /mnt est sur /dev/root
(145G, 84G libres mesures sur les runners sains). Un ``fallocate -l 32G``
fixe a vide le disque de runners moins garnis : ils sont morts en une
minute sur ``No space left on device`` en ecrivant leur journal de
diagnostic, sans laisser de log de job (8 jobs en echec, 4 runs, a partir de 16:19Z).

Le pas vit en trois copies (action composite du chemin matrice, job
mono-lake de lean-build.yml, lean-axiom.yml). Ce test verifie que les trois
copies portent le meme texte, qu'aucune n'alloue plus 32G en dur, et il
execute ce texte avec des ``df``/``sudo``/``free`` simules pour cinq cas,
dont un ``df`` en echec sous ``-eo pipefail``.
"""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import textwrap
from pathlib import Path

import pytest
import yaml

REPO = Path(__file__).resolve().parents[3]
SITES = {
    "action": REPO / ".github/actions/lean-build/action.yml",
    "lean-build": REPO / ".github/workflows/lean-build.yml",
    "lean-axiom": REPO / ".github/workflows/lean-axiom.yml",
}


def _swap_runs(path: Path) -> list[str]:
    doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    if "runs" in doc:
        steps = doc["runs"]["steps"]
    else:
        steps = [s for job in doc["jobs"].values() for s in job.get("steps", [])]
    return [s["run"] for s in steps if str(s.get("name", "")).startswith("Add swap space")]


def _all_runs() -> dict[str, list[str]]:
    return {name: _swap_runs(path) for name, path in SITES.items()}


def test_every_site_has_a_swap_step():
    for name, runs in _all_runs().items():
        assert runs, f"{name}: aucun pas 'Add swap space'"


def test_no_fixed_32g_fallocate():
    for name, runs in _all_runs().items():
        for body in runs:
            assert "fallocate -l 32G" not in body, f"{name}: swap fixe de 32G revenu"


def test_the_copies_are_identical():
    bodies = {body for runs in _all_runs().values() for body in runs}
    assert len(bodies) == 1, "les copies du pas de swap ont diverge"


SHIM_DF = """#!/usr/bin/env bash
if [ "${FAKE_DF_FAIL:-0}" = "1" ]; then
  echo "df: /mnt: No such file or directory" >&2
  exit 1
fi
if [ "$1" = "--output=avail" ]; then
  echo " Avail"
  echo " ${FAKE_AVAIL_G}G"
else
  echo "Filesystem Size Used Avail Use% Mounted on"
fi
"""

SHIM_SUDO = """#!/usr/bin/env bash
echo "$*" >> "$SUDO_LOG"
if [ "$1" = "fallocate" ] && [ "${FAKE_FALLOCATE_FAIL:-0}" = "1" ]; then
  exit 1
fi
exit 0
"""

SHIM_FREE = """#!/usr/bin/env bash
echo "free"
"""


def _bash() -> str | None:
    """Un bash POSIX qui voit le PATH des shims.

    Sous Windows, ``bash`` resout souvent vers celui de WSL, qui ne voit pas
    le PATH Windows : on cherche le bash de Git for Windows a cote de git.
    """
    if os.name == "nt":
        git = shutil.which("git")
        if git:
            # git.exe vit sous <Git>\cmd\ ou <Git>\mingw64\bin\ selon l'installation.
            for parent in Path(git).resolve().parents:
                candidate = parent / "bin" / "bash.exe"
                if candidate.exists():
                    return str(candidate)
        return None
    return shutil.which("bash")


def _posix(path: Path) -> str:
    """Chemin lisible par le bash choisi (``C:\\x`` devient ``/c/x`` sous Windows)."""
    text = str(path)
    if os.name == "nt" and len(text) > 1 and text[1] == ":":
        text = "/" + text[0].lower() + text[2:].replace("\\", "/")
    return text


@pytest.fixture()
def shim_env(tmp_path):
    if _bash() is None:
        pytest.skip("bash POSIX introuvable")
    bindir = tmp_path / "bin"
    bindir.mkdir()
    for name, body in {"df": SHIM_DF, "sudo": SHIM_SUDO, "free": SHIM_FREE}.items():
        shim = bindir / name
        shim.write_text(body, encoding="utf-8", newline="\n")
        shim.chmod(shim.stat().st_mode | stat.S_IEXEC)
    log = tmp_path / "sudo.log"
    env = dict(os.environ)
    env["SHIM_BIN"] = _posix(bindir)
    env["SUDO_LOG"] = _posix(log)
    return env, log, tmp_path


def _run(shim_env, avail_g: int, fallocate_fail: bool = False, df_fail: bool = False):
    env, log, tmp_path = shim_env
    env = dict(
        env,
        FAKE_AVAIL_G=str(avail_g),
        FAKE_FALLOCATE_FAIL="1" if fallocate_fail else "0",
        FAKE_DF_FAIL="1" if df_fail else "0",
    )
    body = next(iter({b for runs in _all_runs().values() for b in runs}))
    # Le PATH se prefixe DANS le script : le lanceur de Git Bash remet
    # /usr/bin en tete, ce qui ferait passer le vrai df devant le shim.
    # `-eo pipefail` est le shell des pas `run:` des runners : un df en echec
    # doit etre rattrape par le pas lui-meme, pas tuer le job.
    prelude = 'set -eo pipefail\nexport PATH="$SHIM_BIN:$PATH"\n'
    script = (prelude + textwrap.dedent(body)).replace("\r\n", "\n").encode("utf-8")
    raw = subprocess.run([_bash(), "-s"], input=script, env=env, capture_output=True)
    proc = subprocess.CompletedProcess(
        raw.args, raw.returncode,
        raw.stdout.decode("utf-8", "replace"), raw.stderr.decode("utf-8", "replace"),
    )
    calls = log.read_text(encoding="utf-8").splitlines() if log.exists() else []
    if log.exists():
        log.unlink()
    return proc, calls


def test_roomy_runner_gets_the_32g_cap(shim_env):
    proc, calls = _run(shim_env, 84)
    assert proc.returncode == 0, proc.stderr
    assert "fallocate -l 32G /mnt/lean-swap" in calls
    assert "swapon /mnt/lean-swap" in calls


def test_tight_runner_gets_a_smaller_swap(shim_env):
    proc, calls = _run(shim_env, 40)
    assert proc.returncode == 0, proc.stderr
    assert "fallocate -l 10G /mnt/lean-swap" in calls


def test_starved_runner_skips_the_swap(shim_env):
    proc, calls = _run(shim_env, 20)
    assert proc.returncode == 0, proc.stderr
    assert not any(c.startswith("fallocate") for c in calls)
    assert "Lean swap skipped" in proc.stdout


def test_failed_fallocate_cleans_up_and_goes_on(shim_env):
    proc, calls = _run(shim_env, 84, fallocate_fail=True)
    assert proc.returncode == 0, proc.stderr
    assert "rm -f /mnt/lean-swap" in calls
    assert not any(c.startswith("swapon") for c in calls)
    assert "Lean swap skipped" in proc.stdout


def test_unreadable_df_skips_the_swap(shim_env):
    proc, calls = _run(shim_env, 84, df_fail=True)
    assert proc.returncode == 0, proc.stderr
    assert not any(c.startswith("fallocate") for c in calls)
    assert "Lean swap skipped::df could not read" in proc.stdout
