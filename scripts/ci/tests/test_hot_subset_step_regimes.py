"""Regimes du step `hot_subset` de `always-on-guards.yml` (#22435).

Le code retour de pytest n'est pas un booleen : `1` dit que des tests ont
echoue -- le seul regime qui dise quelque chose du contenu --, tandis que
`2` (execution interrompue : erreur de collecte ou `ImportError`), `3`
(erreur interne), `4` (usage) et `5` (aucun test collecte) disent que la
mesure n'a pas eu lieu.

Le step imprimait le verdict de contenu `SRC_DRIFT` sur tout RC non nul. Une
PR verte sur son contenu portait donc un rouge qui affirmait une derive de
traduction jamais mesuree : #22130 (tete `402871d9cc`) et #22264 (tete
`07885aafc8`), `2 passed` localement sur les deux tetes.

Ce test execute le **vrai** bloc `run:` du workflow, avec des `python`,
`pip` et `git` factices : c'est le shell du workflow qui est mesure, pas une
reecriture de sa logique dans le test.
"""

from __future__ import annotations

import os
import pathlib
import shutil
import stat
import subprocess

import pytest

yaml = pytest.importorskip("yaml")

REPO = pathlib.Path(__file__).resolve().parents[3]
WORKFLOW = REPO / ".github" / "workflows" / "always-on-guards.yml"
VERDICT_LINE = "::error::Hot-subset ratchet : SRC_DRIFT"


def _hot_subset_run_block() -> str:
    doc = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    job = next(iter(doc["jobs"].values()))
    step = next(s for s in job["steps"] if s.get("id") == "hot_subset")
    return step["run"]


def _shim(directory: pathlib.Path, name: str, body: str) -> None:
    path = directory / name
    path.write_text("#!/bin/sh\n" + body + "\n", encoding="utf-8", newline="\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)


def _run_step(tmp_path: pathlib.Path, rc: str, files: str) -> subprocess.CompletedProcess:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    _shim(bin_dir, "python", 'exit "$FAKE_RC"')
    _shim(bin_dir, "pip", "exit 0")
    _shim(bin_dir, "git", 'printf "%s\\n" "$FAKE_FILES"')
    script = tmp_path / "step.sh"
    script.write_text(_hot_subset_run_block(), encoding="utf-8", newline="\n")
    env = dict(os.environ)
    env["PATH"] = str(bin_dir) + os.pathsep + env["PATH"]
    env["FAKE_RC"] = rc
    env["FAKE_FILES"] = files
    env["BASE"] = "0" * 40
    return subprocess.run(
        ["bash", str(script)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
    )


# (id, rc pytest, fichiers touches par la PR, exit attendu, texte attendu)
CASES = [
    ("vert", "0", "", 0, None),
    ("contenu", "1", "", 1, VERDICT_LINE),
    ("collecte-hors-organe", "2", "docs/README.md", 0, "n'a PAS pu mesurer"),
    ("collecte-notebook-hors-organe", "5", "MyIA.AI.Notebooks/x.ipynb", 0, "n'a PAS pu mesurer"),
    ("interne-hors-organe", "3", "", 0, "n'a PAS pu mesurer"),
    ("collecte-touche-organe", "2", "scripts/translation/foo.py", 1, "attribuable"),
    ("collecte-touche-outils", "2", "scripts/notebook_tools/bar.py", 1, "attribuable"),
]


@pytest.mark.skipif(shutil.which("bash") is None, reason="shell bash requis pour executer le step")
@pytest.mark.parametrize("case_id,rc,files,want_rc,want_text", CASES, ids=[c[0] for c in CASES])
def test_hot_subset_regime(tmp_path, case_id, rc, files, want_rc, want_text):
    proc = _run_step(tmp_path, rc, files)
    output = proc.stdout + proc.stderr
    assert proc.returncode == want_rc, output
    if want_text is not None:
        assert want_text in output, output
    if rc != "1":
        # garde-fou : la LIGNE DE VERDICT ne doit jamais sortir hors du rc 1.
        # On cherche la ligne emise, pas le token nu -- l'avertissement doit
        # pouvoir nommer SRC_DRIFT pour dire qu'il ne l'est pas.
        assert VERDICT_LINE not in output, output
