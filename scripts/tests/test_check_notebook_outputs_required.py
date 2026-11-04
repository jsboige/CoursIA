"""Tests du perimetre PR de la garde notebook-outputs-required (#23068).

Residu de la famille "diff en deux points" (#10403) : `pr_diff_files` lisait
`git diff --name-only base head`. Sur une PR empilee dont la base
(origin/main) a gagne des commits depuis le point de fork, la forme en deux
points liste AUSSI les fichiers modifies cote main, et la garde imputait a
la PR des defauts de carnets qu'elle n'a pas touches.

Le temoin comportemental exige par l'issue : un depot jetable ou main
ajoute APRES le fork un carnet portant le defaut chasse par la garde
(cellule code sans cle `outputs`, le cas fondateur c.1084), pendant que la
branche PR modifie un carnet propre. La forme en deux points voyait le
carnet de main ; la forme en trois points ne rend que le carnet de la PR.

Second temoin : une sonde git en echec rend None, et `main()` rend rc 2
"non evalue" -- jamais une liste vide lue comme "aucun carnet touche"
(faux quitus vert), jamais un rouge bloquant qui accuserait la PR.
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

# Charge le module sans dependre du packaging (le script n'est pas dans un
# package). Meme mecanisme que test_check_eol_blobs.py.
_HERE = Path(__file__).resolve().parent
_MOD_PATH = _HERE.parent / "notebook_tools" / "check_notebook_outputs_required.py"
_spec = importlib.util.spec_from_file_location(
    "check_notebook_outputs_required", _MOD_PATH,
)
assert _spec is not None and _spec.loader is not None
mod = importlib.util.module_from_spec(_spec)
sys.modules["check_notebook_outputs_required"] = mod
_spec.loader.exec_module(mod)


# Carnet propre : la cellule code PORTE la cle `outputs` (liste vide, forme
# canonique d'une cellule non executee) -> PASS pour la garde.
CLEAN_NB = {
    "cells": [
        {"cell_type": "code", "execution_count": None, "id": "c1",
         "metadata": {}, "outputs": [], "source": ["print('ok')\n"]},
    ],
    "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
}

# Le defaut fondateur de la garde (c.1084) : cle `outputs` ABSENTE.
DEFECTIVE_NB = {
    "cells": [
        {"cell_type": "code", "execution_count": None, "id": "d1",
         "metadata": {}, "source": ["print('defect')\n"]},
    ],
    "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
}


def _write_nb(path: Path, nb: dict) -> None:
    path.write_text(json.dumps(nb), encoding="utf-8")


def _stacked_repo(tmp_path: Path) -> Path:
    """Depot jetable : PR empilee dont la base a bouge depuis le fork.

        A (fork) -- B (main ajoute theirs.ipynb DEFECTUEUX)  <- origin/main
          \\
           C (branche pr modifie mine.ipynb, reste propre)  <- HEAD

    La forme en deux points entre origin/main (B) et HEAD (C) liste les
    DEUX carnets ; la forme en trois points (A..C) ne rend que mine.ipynb.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
    for key, val in (
        ("user.email", "test@example.com"),
        ("user.name", "Test"),
        ("core.autocrlf", "false"),
    ):
        subprocess.run(
            ["git", "config", key, val], cwd=str(repo), check=True,
        )
    # A -- point de fork : un seul carnet, propre.
    _write_nb(repo / "mine.ipynb", CLEAN_NB)
    subprocess.run(["git", "add", "."], cwd=str(repo), check=True)
    subprocess.run(
        ["git", "commit", "-m", "A: fork point", "-q"], cwd=str(repo), check=True,
    )
    subprocess.run(["git", "branch", "pr"], cwd=str(repo), check=True)
    # B -- main avance APRES le fork : ajoute le carnet defectueux.
    _write_nb(repo / "theirs.ipynb", DEFECTIVE_NB)
    subprocess.run(["git", "add", "."], cwd=str(repo), check=True)
    subprocess.run(
        ["git", "commit", "-m", "B: main adds defective notebook", "-q"],
        cwd=str(repo), check=True,
    )
    subprocess.run(
        ["git", "update-ref", "refs/remotes/origin/main", "HEAD"],
        cwd=str(repo), check=True,
    )
    # C -- la branche PR modifie son propre carnet (reste propre).
    subprocess.run(["git", "switch", "-q", "pr"], cwd=str(repo), check=True)
    edited = json.loads(json.dumps(CLEAN_NB))
    edited["cells"].append(
        {"cell_type": "markdown", "id": "m1", "metadata": {}, "source": ["edit\n"]},
    )
    _write_nb(repo / "mine.ipynb", edited)
    subprocess.run(["git", "add", "."], cwd=str(repo), check=True)
    subprocess.run(
        ["git", "commit", "-m", "C: PR edits mine", "-q"], cwd=str(repo), check=True,
    )
    return repo


def test_pr_diff_three_point_excludes_main_side_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Temoin comportemental #23068 : le perimetre ne rend que l'apport PR.

    Contre-factuel mesure dans le meme temoin : la forme en deux points
    VOYAIT le carnet de main -- sans cette assertion, le temoin ne prouverait
    pas que la correction mord.
    """
    repo = _stacked_repo(tmp_path)
    # Sanite du temoin : theirs porte le defaut chasse, mine est propre.
    # theirs.ipynb n'existe pas dans le worktree au HEAD de la PR (il n'est
    # suivi que cote main) -- on lit son blob depuis origin/main.
    blob = subprocess.run(
        ["git", "show", "origin/main:theirs.ipynb"],
        cwd=str(repo), capture_output=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout
    scratch = tmp_path / "theirs_from_main.ipynb"
    scratch.write_text(blob, encoding="utf-8")
    assert mod.scan_notebook(scratch), (
        "theirs.ipynb (cote main) doit porter le defaut (cle outputs absente)"
    )
    assert not mod.scan_notebook(repo / "mine.ipynb")

    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    got = mod.pr_diff_files("origin/main", "HEAD")
    assert got is not None
    assert [p.name for p in got] == ["mine.ipynb"], (
        f"le perimetre doit exclure les carnets gagnes par main depuis le "
        f"fork : {[p.name for p in got]!r}"
    )

    two_point = subprocess.run(
        ["git", "diff", "--name-only", "origin/main", "HEAD"],
        cwd=str(repo), capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout
    assert "theirs.ipynb" in two_point and "mine.ipynb" in two_point, (
        f"la forme en deux points (defaut #23068) aurait du voir les deux "
        f"carnets : {two_point!r}"
    )


def test_main_stacked_pr_green_two_point_would_flag(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture,
) -> None:
    """La PR (carnet propre) est VERTE : le defaut du carnet de main ne lui
    est plus impute, alors qu'un scan deux points l'aurait rougie."""
    repo = _stacked_repo(tmp_path)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    rc = mod.main(["--pr-diff", "origin/main", "HEAD"])
    out = capsys.readouterr()
    assert rc == 0, f"la PR ne porte aucun defaut : out={out.out!r} err={out.err!r}"
    assert "theirs.ipynb" not in out.out


def test_pr_diff_probe_failure_returns_none_not_empty(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Sonde git en echec -> None ("non evalue"), pas [] ("rien a voir")."""
    repo = _stacked_repo(tmp_path)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    assert mod.pr_diff_files("origin/ref-inexistante", "HEAD") is None


def test_main_probe_failure_exits_two_non_evalue(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture,
) -> None:
    """main() rend rc 2 et le DIT ("non evalue") quand la sonde echoue --
    le rc 2 est mappe en neutral "incident du garde" par warn_rc=(2,) du
    registre, jamais en vert silencieux ni en rouge bloquant."""
    repo = _stacked_repo(tmp_path)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    rc = mod.main(["--pr-diff", "origin/ref-inexistante", "HEAD"])
    err = capsys.readouterr().err
    assert rc == 2
    assert "non evalue" in err.lower(), f"message attendu dans stderr : {err!r}"
